#!/usr/bin/env python3

import os
import sys
import argparse
import json
import time
import hashlib
import pwd
import grp
from collections import defaultdict
from pathlib import Path
from datetime import datetime
import subprocess
import stat
import threading
from concurrent.futures import ThreadPoolExecutor

try:
    from rich.console import Console
    from rich.table import Table
    from rich.progress import Progress, SpinnerColumn, BarColumn, TextColumn, TimeElapsedColumn
    from rich import box
    RICH_AVAILABLE = True
    console = Console()
except ImportError:
    RICH_AVAILABLE = False
    console = None

try:
    import humanize
    HUMANIZE_AVAILABLE = True
except ImportError:
    HUMANIZE_AVAILABLE = False

try:
    import matplotlib.pyplot as plt
    PLOT_AVAILABLE = True
except ImportError:
    PLOT_AVAILABLE = False


class InodeAnalyzer:
    def __init__(self, threads=4, follow_symlinks=False):
        self.stats = {
            'total_files': 0,
            'total_dirs': 0,
            'total_symlinks': 0,
            'total_sockets': 0,
            'total_fifos': 0,
            'total_devices': 0,
            'extensions': defaultdict(int),
            'largest_files': [],
            'oldest_files': [],
            'newest_files': [],
            'largest_dirs': [],
            'permissions': defaultdict(int),
            'owners': defaultdict(int),
            'groups': defaultdict(int),
            'age_distribution': defaultdict(int),
            'size_distribution': defaultdict(int),
            'duplicates': [],
            'empty_files': 0,
            'empty_dirs': 0,
            'broken_symlinks': 0,
            'permission_denied': 0,
            'file_types': defaultdict(int)
        }
        self.threads = threads
        self.follow_symlinks = follow_symlinks
        self.total_size = 0
        self.lock = threading.Lock()
        self.processed_paths = set()
        
    def get_human_readable(self, value, is_bytes=True):
        if HUMANIZE_AVAILABLE:
            if is_bytes:
                return humanize.naturalsize(value)
            return humanize.intcomma(value)
        return f"{value:,}"

    def analyze_directory(self, path, sample_size=20, deep_scan=False, 
                         find_duplicates=False, export_json=None, 
                         generate_plot=None, age_days=None):
        path = Path(path).resolve()
        if not path.exists():
            if RICH_AVAILABLE:
                console.print(f"[bold red]Path does not exist: {path}[/bold red]")
            else:
                print(f"Path does not exist: {path}")
            return
        
        start_time = time.time()
        
        if RICH_AVAILABLE:
            console.rule(f"[bold blue]Analyzing: {path}[/bold blue]")
            console.print(f"Deep scan: [{'green' if deep_scan else 'yellow'}]{deep_scan}[/], Find duplicates: [{'green' if find_duplicates else 'yellow'}]{find_duplicates}[/]")
        else:
            print(f"Analyzing: {path}")
            print(f"Deep scan: {deep_scan}, Find duplicates: {find_duplicates}")
            print("-" * 70)
        
        if deep_scan:
            self._deep_scan_analysis(path, sample_size, find_duplicates, age_days)
        else:
            self._quick_scan_analysis(path, sample_size)
        
        if find_duplicates and not deep_scan:
            self.find_duplicate_files(path)
        
        elapsed_time = time.time() - start_time
        self.print_report(elapsed_time)
        
        if export_json:
            self.export_json(export_json)
        
        if generate_plot:
            self.generate_visualization(generate_plot)

    def _quick_scan_analysis(self, path, sample_size):
        try:
            if RICH_AVAILABLE:
                console.print("[cyan]Counting files...[/cyan]")
            
            files_count = 0
            dirs_count = 0
            symlinks_count = 0
            sockets_count = 0
            fifos_count = 0
            devices_count = 0
            files_data = []
            
            for root, dirs, files in os.walk(path):
                dirs_count += len(dirs)
                files_count += len(files)
                
                for file in files:
                    filepath = os.path.join(root, file)
                    try:
                        stat_info = os.lstat(filepath)
                        mode = stat_info.st_mode
                        
                        if stat.S_ISLNK(mode):
                            symlinks_count += 1
                        elif stat.S_ISSOCK(mode):
                            sockets_count += 1
                        elif stat.S_ISFIFO(mode):
                            fifos_count += 1
                        elif stat.S_ISBLK(mode) or stat.S_ISCHR(mode):
                            devices_count += 1
                        
                        if stat.S_ISREG(mode):
                            size = stat_info.st_size
                            self.total_size += size
                            
                            if '.' in file:
                                ext = file.rsplit('.', 1)[-1].lower()
                                self.stats['extensions'][ext] += 1
                            
                            try:
                                owner = pwd.getpwuid(stat_info.st_uid).pw_name
                            except:
                                owner = str(stat_info.st_uid)
                            self.stats['owners'][owner] += 1
                            
                            try:
                                group = grp.getgrgid(stat_info.st_gid).gr_name
                            except:
                                group = str(stat_info.st_gid)
                            self.stats['groups'][group] += 1
                            
                            perms = oct(mode)[-4:]
                            self.stats['permissions'][perms] += 1
                            
                            size_category = self._categorize_size(size)
                            self.stats['size_distribution'][size_category] += 1
                            
                            if size == 0:
                                self.stats['empty_files'] += 1
                            
                            atime = datetime.fromtimestamp(stat_info.st_atime)
                            mtime = datetime.fromtimestamp(stat_info.st_mtime)
                            
                            age_category = self._categorize_age(mtime)
                            self.stats['age_distribution'][age_category] += 1
                            
                            files_data.append((size, filepath, atime.isoformat(), owner, group, perms))
                    except OSError:
                        self.stats['permission_denied'] += 1
                        continue
                
                for dirname in dirs:
                    dirpath = os.path.join(root, dirname)
                    try:
                        if not os.listdir(dirpath):
                            self.stats['empty_dirs'] += 1
                    except OSError:
                        pass
            
            self.stats['total_files'] = files_count
            self.stats['total_dirs'] = dirs_count
            self.stats['total_symlinks'] = symlinks_count
            self.stats['total_sockets'] = sockets_count
            self.stats['total_fifos'] = fifos_count
            self.stats['total_devices'] = devices_count
            
            if RICH_AVAILABLE:
                console.print(f"  Found [green]{self.get_human_readable(self.stats['total_files'], False)}[/green] files")
                console.print(f"  Found [green]{self.get_human_readable(self.stats['total_dirs'], False)}[/green] directories")
            else:
                print(f"  Found {self.get_human_readable(self.stats['total_files'], False)} files")
                print(f"  Found {self.get_human_readable(self.stats['total_dirs'], False)} directories")
            
            files_data.sort(key=lambda x: x[0], reverse=True)
            self.stats['largest_files'] = files_data[:sample_size]
            
            files_data.sort(key=lambda x: x[2])
            self.stats['oldest_files'] = files_data[:sample_size]
            
            files_data.sort(key=lambda x: x[2], reverse=True)
            self.stats['newest_files'] = files_data[:sample_size]
            
            self._analyze_largest_directories(path, sample_size)
            
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[yellow]Scan failed: {e}, using fallback...[/yellow]")
            else:
                print(f"Scan failed: {e}, using fallback...")
            self._fallback_analysis(path, sample_size)

    def _deep_scan_analysis(self, path, sample_size, find_duplicates, age_days=None):
        if RICH_AVAILABLE:
            console.print("[bold blue]Performing deep scan...[/bold blue]")
        else:
            print("Performing deep scan...")
        
        all_items = []
        
        try:
            for root, dirs, files in os.walk(path):
                all_items.append(Path(root))
                for d in dirs:
                    try:
                        all_items.append(Path(root) / d)
                    except Exception:
                        pass
                for f in files:
                    try:
                        all_items.append(Path(root) / f)
                    except Exception:
                        pass
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[red]Error during walk: {e}[/red]")
            else:
                print(f"Error during walk: {e}")
            return
        
        total_items = len(all_items)
        
        if RICH_AVAILABLE:
            with Progress(
                SpinnerColumn(),
                TextColumn("[progress.description]{task.description}"),
                BarColumn(),
                TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
                TimeElapsedColumn(),
                console=console
            ) as progress:
                task = progress.add_task("[cyan]Scanning items...", total=total_items)
                
                with ThreadPoolExecutor(max_workers=self.threads) as executor:
                    futures = []
                    for item in all_items:
                        if str(item) not in self.processed_paths:
                            self.processed_paths.add(str(item))
                            futures.append(executor.submit(self._analyze_item, item, age_days))
                    
                    for future in futures:
                        future.result()
                        progress.update(task, advance=1)
        else:
            print(f"  Scanning {self.get_human_readable(total_items, False)} items...")
            with ThreadPoolExecutor(max_workers=self.threads) as executor:
                futures = []
                for item in all_items:
                    if str(item) not in self.processed_paths:
                        self.processed_paths.add(str(item))
                        futures.append(executor.submit(self._analyze_item, item, age_days))
                
                for i, future in enumerate(futures):
                    future.result()
                    if i % 1000 == 0 and total_items > 0:
                        progress = (i + 1) / total_items * 100
                        print(f"\r  Progress: {progress:.1f}% ({i+1:,}/{total_items:,})", end='', flush=True)
            
            print(f"\r  Progress: 100% ({total_items:,}/{total_items:,})")
        
        if RICH_AVAILABLE:
            console.print(f"  Found [green]{self.get_human_readable(self.stats['total_files'], False)}[/green] files")
            console.print(f"  Found [green]{self.get_human_readable(self.stats['total_dirs'], False)}[/green] directories")
        
        self.stats['largest_files'].sort(key=lambda x: x[0], reverse=True)
        self.stats['largest_files'] = self.stats['largest_files'][:sample_size]
        
        self.stats['oldest_files'].sort(key=lambda x: x[2])
        self.stats['oldest_files'] = self.stats['oldest_files'][:sample_size]
        
        self.stats['newest_files'].sort(key=lambda x: x[2], reverse=True)
        self.stats['newest_files'] = self.stats['newest_files'][:sample_size]
        
        self._analyze_largest_directories(path, sample_size, deep=True)
        
        if find_duplicates:
            self.find_duplicate_files(path)

    def _analyze_item(self, item, age_days=None):
        try:
            stat_info = item.stat() if self.follow_symlinks else item.lstat()
            mode = stat_info.st_mode
            
            if stat.S_ISREG(mode):
                with self.lock:
                    self.stats['total_files'] += 1
                    self.stats['file_types']['regular'] += 1
                
                if age_days:
                    mtime = datetime.fromtimestamp(stat_info.st_mtime)
                    age = datetime.now() - mtime
                    if age.days > age_days:
                        return
                
                size = stat_info.st_size
                with self.lock:
                    self.total_size += size
                
                with self.lock:
                    if item.name and '.' in item.name:
                        ext = item.name.rsplit('.', 1)[-1].lower()
                        self.stats['extensions'][ext] += 1
                    
                    self.stats['permissions'][oct(mode)[-4:]] += 1
                    
                    try:
                        owner = pwd.getpwuid(stat_info.st_uid).pw_name
                    except:
                        owner = str(stat_info.st_uid)
                    self.stats['owners'][owner] += 1
                    
                    try:
                        group = grp.getgrgid(stat_info.st_gid).gr_name
                    except:
                        group = str(stat_info.st_gid)
                    self.stats['groups'][group] += 1
                    
                    size_category = self._categorize_size(size)
                    self.stats['size_distribution'][size_category] += 1
                    
                    if size == 0:
                        self.stats['empty_files'] += 1
                    
                    atime = datetime.fromtimestamp(stat_info.st_atime)
                    mtime = datetime.fromtimestamp(stat_info.st_mtime)
                    
                    age_category = self._categorize_age(mtime)
                    self.stats['age_distribution'][age_category] += 1
                    
                    file_info = (size, str(item), atime.isoformat(), owner, group, oct(mode)[-4:])
                    self.stats['largest_files'].append(file_info)
                    self.stats['oldest_files'].append(file_info)
                    self.stats['newest_files'].append(file_info)
            
            elif stat.S_ISDIR(mode):
                with self.lock:
                    self.stats['total_dirs'] += 1
                    self.stats['file_types']['directory'] += 1
                    
                    try:
                        if item.is_dir() and not any(item.iterdir()):
                            self.stats['empty_dirs'] += 1
                    except (PermissionError, OSError):
                        self.stats['permission_denied'] += 1
            
            elif stat.S_ISLNK(mode):
                with self.lock:
                    self.stats['total_symlinks'] += 1
                    self.stats['file_types']['symlink'] += 1
                    
                    try:
                        if not item.exists():
                            self.stats['broken_symlinks'] += 1
                    except OSError:
                        self.stats['broken_symlinks'] += 1
            
            elif stat.S_ISSOCK(mode):
                with self.lock:
                    self.stats['total_sockets'] += 1
                    self.stats['file_types']['socket'] += 1
            
            elif stat.S_ISFIFO(mode):
                with self.lock:
                    self.stats['total_fifos'] += 1
                    self.stats['file_types']['fifo'] += 1
            
            elif stat.S_ISBLK(mode) or stat.S_ISCHR(mode):
                with self.lock:
                    self.stats['total_devices'] += 1
                    self.stats['file_types']['device'] += 1
                    
        except (PermissionError, OSError):
            with self.lock:
                self.stats['permission_denied'] += 1
        except Exception:
            pass

    def _analyze_largest_directories(self, path, sample_size, deep=False):
        try:
            if deep:
                dir_sizes = []
                for root, dirs, files in os.walk(path):
                    try:
                        dir_size = 0
                        file_count = 0
                        for file in files:
                            filepath = os.path.join(root, file)
                            try:
                                if os.path.isfile(filepath):
                                    dir_size += os.path.getsize(filepath)
                                    file_count += 1
                            except OSError:
                                pass
                        dir_sizes.append((dir_size, file_count, root))
                    except (PermissionError, OSError):
                        continue
                
                dir_sizes.sort(key=lambda x: x[0], reverse=True)
                self.stats['largest_dirs'] = dir_sizes[:sample_size]
            else:
                try:
                    result = subprocess.run(
                        ['du', '-b', '--max-depth=1', str(path)],
                        capture_output=True, text=True,
                        timeout=30
                    )
                    
                    dirs = []
                    for line in result.stdout.splitlines():
                        if line:
                            try:
                                size, dirpath = line.split('\t', 1)
                                if dirpath != str(path):
                                    dirs.append((int(size), dirpath))
                            except (ValueError, IndexError):
                                continue
                    
                    dirs.sort(key=lambda x: x[0], reverse=True)
                    self.stats['largest_dirs'] = [
                        (size, 0, dirpath) for size, dirpath in dirs[:sample_size]
                    ]
                except subprocess.TimeoutExpired:
                    pass
                
        except (subprocess.SubprocessError, FileNotFoundError):
            pass

    def find_duplicate_files(self, path):
        if RICH_AVAILABLE:
            console.print("[bold blue]Searching for duplicate files...[/bold blue]")
        else:
            print("  Searching for duplicate files...")
        
        size_dict = defaultdict(list)
        file_count = 0
        
        if RICH_AVAILABLE:
            with Progress(
                TextColumn("[progress.description]{task.description}"),
                BarColumn(),
                TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
                console=console
            ) as progress:
                task = progress.add_task("[cyan]Scanning files...", total=None)
                
                for root, dirs, files in os.walk(path):
                    for file in files:
                        filepath = os.path.join(root, file)
                        try:
                            if os.path.isfile(filepath):
                                size = os.path.getsize(filepath)
                                if size > 0:
                                    size_dict[size].append(filepath)
                                    file_count += 1
                                    if file_count % 1000 == 0:
                                        progress.update(task, description=f"[cyan]Scanned {self.get_human_readable(file_count, False)} files...")
                        except OSError:
                            continue
                    
                    progress.update(task, total=file_count + 1000)
                
                progress.update(task, description=f"[green]Scanned {self.get_human_readable(file_count, False)} files")
        else:
            for root, dirs, files in os.walk(path):
                for file in files:
                    filepath = os.path.join(root, file)
                    try:
                        if os.path.isfile(filepath):
                            size = os.path.getsize(filepath)
                            if size > 0:
                                size_dict[size].append(filepath)
                                file_count += 1
                                if file_count % 10000 == 0:
                                    print(f"\r    Scanned {self.get_human_readable(file_count, False)} files...", end='', flush=True)
                    except OSError:
                        continue
            
            print(f"\r    Scanned {self.get_human_readable(file_count, False)} files.")
        
        unique_sizes = len(size_dict)
        if RICH_AVAILABLE:
            console.print(f"Found [green]{self.get_human_readable(unique_sizes, False)}[/green] unique sizes, checking duplicates...")
        else:
            print(f"    Found {self.get_human_readable(unique_sizes, False)} unique sizes, checking duplicates...")
        
        duplicate_count = 0
        for size, filepaths in size_dict.items():
            if len(filepaths) > 1:
                checksum_dict = defaultdict(list)
                
                for filepath in filepaths:
                    try:
                        checksum = self._calculate_hash(filepath)
                        checksum_dict[checksum].append(filepath)
                    except (OSError, IOError):
                        continue
                
                for checksum, duplicate_files in checksum_dict.items():
                    if len(duplicate_files) > 1:
                        total_size = size * len(duplicate_files)
                        wasted_space = size * (len(duplicate_files) - 1)
                        self.stats['duplicates'].append({
                            'size': size,
                            'checksum': checksum,
                            'files': duplicate_files,
                            'total_size': total_size,
                            'wasted_space': wasted_space,
                            'count': len(duplicate_files)
                        })
                        duplicate_count += 1
        
        if RICH_AVAILABLE:
            console.print(f"Found [green]{self.get_human_readable(duplicate_count, False)}[/green] duplicate sets")
        else:
            print(f"    Found {self.get_human_readable(duplicate_count, False)} duplicate sets.")
        
        self.stats['duplicates'].sort(key=lambda x: x['wasted_space'], reverse=True)

    def _calculate_hash(self, filepath, buffer_size=65536):
        hasher = hashlib.md5()
        with open(filepath, 'rb') as f:
            buffer = f.read(buffer_size)
            while buffer:
                hasher.update(buffer)
                buffer = f.read(buffer_size)
        return hasher.hexdigest()

    def _categorize_size(self, size):
        if size < 1024:
            return '< 1 KB'
        elif size < 1024 * 1024:
            return '1 KB - 1 MB'
        elif size < 10 * 1024 * 1024:
            return '1 MB - 10 MB'
        elif size < 100 * 1024 * 1024:
            return '10 MB - 100 MB'
        elif size < 1024 * 1024 * 1024:
            return '100 MB - 1 GB'
        else:
            return '> 1 GB'

    def _categorize_age(self, mtime):
        age = datetime.now() - mtime
        if age.days < 1:
            return 'Today'
        elif age.days < 7:
            return 'This week'
        elif age.days < 30:
            return 'This month'
        elif age.days < 365:
            return 'This year'
        else:
            return '> 1 year'

    def _fallback_analysis(self, path, sample_size):
        if RICH_AVAILABLE:
            console.print("[yellow]Using fallback analysis method...[/yellow]")
        else:
            print("Using fallback analysis method...")
        
        files_data = []
        
        for root, dirs, files in os.walk(path):
            self.stats['total_dirs'] += 1
            self.stats['total_files'] += len(files)
            
            for file in files:
                if '.' in file:
                    ext = file.rsplit('.', 1)[-1].lower()
                    self.stats['extensions'][ext] += 1
                
                filepath = os.path.join(root, file)
                try:
                    if os.path.isfile(filepath):
                        size = os.path.getsize(filepath)
                        self.total_size += size
                        
                        size_category = self._categorize_size(size)
                        self.stats['size_distribution'][size_category] += 1
                        
                        if size == 0:
                            self.stats['empty_files'] += 1
                        
                        mtime = os.path.getmtime(filepath)
                        age_category = self._categorize_age(datetime.fromtimestamp(mtime))
                        self.stats['age_distribution'][age_category] += 1
                        
                        try:
                            stat_info = os.lstat(filepath)
                            try:
                                owner = pwd.getpwuid(stat_info.st_uid).pw_name
                            except:
                                owner = str(stat_info.st_uid)
                            self.stats['owners'][owner] += 1
                            
                            try:
                                group = grp.getgrgid(stat_info.st_gid).gr_name
                            except:
                                group = str(stat_info.st_gid)
                            self.stats['groups'][group] += 1
                            
                            perms = oct(stat_info.st_mode)[-4:]
                            self.stats['permissions'][perms] += 1
                        except:
                            pass
                        
                        files_data.append((size, filepath, '', '', '', ''))
                    
                except OSError:
                    self.stats['permission_denied'] += 1
            
            for dirname in dirs:
                dirpath = os.path.join(root, dirname)
                try:
                    if not os.listdir(dirpath):
                        self.stats['empty_dirs'] += 1
                except OSError:
                    pass
        
        if RICH_AVAILABLE:
            console.print(f"  Found [green]{self.get_human_readable(self.stats['total_files'], False)}[/green] files")
            console.print(f"  Found [green]{self.get_human_readable(self.stats['total_dirs'], False)}[/green] directories")
        
        files_data.sort(key=lambda x: x[0], reverse=True)
        self.stats['largest_files'] = files_data[:sample_size]

    def print_report(self, elapsed_time):
        total_inodes = (self.stats['total_files'] + self.stats['total_dirs'] + 
                       self.stats['total_symlinks'] + self.stats['total_sockets'] +
                       self.stats['total_fifos'] + self.stats['total_devices'])
        
        if RICH_AVAILABLE:
            console.rule("[bold green]INODE ANALYSIS REPORT[/bold green]")
            
            summary_table = Table(title="Summary", box=box.ROUNDED, title_style="bold")
            summary_table.add_column("Metric", style="cyan")
            summary_table.add_column("Count", style="white", justify="right")
            
            summary_table.add_row("Total Files", self.get_human_readable(self.stats['total_files'], False))
            summary_table.add_row("Total Directories", self.get_human_readable(self.stats['total_dirs'], False))
            summary_table.add_row("Total Symlinks", self.get_human_readable(self.stats['total_symlinks'], False))
            summary_table.add_row("Total Sockets", self.get_human_readable(self.stats['total_sockets'], False))
            summary_table.add_row("Total FIFOs/pipes", self.get_human_readable(self.stats['total_fifos'], False))
            summary_table.add_row("Total Device files", self.get_human_readable(self.stats['total_devices'], False))
            summary_table.add_row("", "")
            summary_table.add_row("TOTAL INODES", self.get_human_readable(total_inodes, False), style="bold yellow")
            summary_table.add_row("Total Size", self.get_human_readable(self.total_size))
            summary_table.add_row("Empty Files", self.get_human_readable(self.stats['empty_files'], False))
            summary_table.add_row("Empty Directories", self.get_human_readable(self.stats['empty_dirs'], False))
            summary_table.add_row("Broken Symlinks", self.get_human_readable(self.stats['broken_symlinks'], False))
            summary_table.add_row("Permission Denied", self.get_human_readable(self.stats['permission_denied'], False))
            summary_table.add_row("Scan Time", f"{elapsed_time:.2f} seconds")
            
            console.print(summary_table)
            
            if self.stats['duplicates']:
                total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
                total_duplicate_sets = len(self.stats['duplicates'])
                total_duplicate_files = sum(d['count'] for d in self.stats['duplicates'])
                
                dup_table = Table(title="Duplicate Files", box=box.ROUNDED, title_style="bold")
                dup_table.add_column("Metric", style="cyan")
                dup_table.add_column("Count", justify="right")
                
                dup_table.add_row("Duplicate Sets", self.get_human_readable(total_duplicate_sets, False))
                dup_table.add_row("Duplicate Files", self.get_human_readable(total_duplicate_files, False))
                dup_table.add_row("Wasted Space", self.get_human_readable(total_wasted))
                
                console.print(dup_table)
            
            if self.stats['extensions']:
                ext_table = Table(title="Top 10 File Extensions", box=box.SIMPLE, title_style="bold")
                ext_table.add_column("Extension", style="green")
                ext_table.add_column("Count", justify="right")
                ext_table.add_column("Percentage", justify="right")
                
                sorted_exts = sorted(
                    self.stats['extensions'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:10]
                
                for ext, count in sorted_exts:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    ext_table.add_row(f".{ext}", 
                                    self.get_human_readable(count, False),
                                    f"{percentage:.1f}%")
                
                console.print(ext_table)
            
            if self.stats['owners']:
                owner_table = Table(title="Top 10 Owners", box=box.SIMPLE, title_style="bold")
                owner_table.add_column("Owner", style="blue")
                owner_table.add_column("Files", justify="right")
                owner_table.add_column("Percentage", justify="right")
                
                sorted_owners = sorted(
                    self.stats['owners'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:10]
                
                for owner, count in sorted_owners:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    owner_table.add_row(owner[:25],
                                      self.get_human_readable(count, False),
                                      f"{percentage:.1f}%")
                
                console.print(owner_table)
            
            if self.stats['groups']:
                group_table = Table(title="Top 10 Groups", box=box.SIMPLE, title_style="bold")
                group_table.add_column("Group", style="magenta")
                group_table.add_column("Files", justify="right")
                group_table.add_column("Percentage", justify="right")
                
                sorted_groups = sorted(
                    self.stats['groups'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:10]
                
                for group, count in sorted_groups:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    group_table.add_row(group[:25],
                                      self.get_human_readable(count, False),
                                      f"{percentage:.1f}%")
                
                console.print(group_table)
            
            if self.stats['size_distribution']:
                size_table = Table(title="Size Distribution", box=box.SIMPLE, title_style="bold")
                size_table.add_column("Size Range", style="magenta")
                size_table.add_column("Files", justify="right")
                size_table.add_column("Percentage", justify="right")
                size_table.add_column("Bar", justify="left")
                
                sorted_sizes = sorted(
                    self.stats['size_distribution'].items(),
                    key=lambda x: self._size_category_order(x[0])
                )
                
                max_count = max(self.stats['size_distribution'].values()) if self.stats['size_distribution'] else 1
                
                for category, count in sorted_sizes:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    bar_length = int((count / max_count) * 20) if max_count > 0 else 0
                    bar = '█' * bar_length + '░' * (20 - bar_length)
                    size_table.add_row(category,
                                     self.get_human_readable(count, False),
                                     f"{percentage:.1f}%",
                                     bar)
                
                console.print(size_table)
            
            if self.stats['age_distribution']:
                age_table = Table(title="Age Distribution", box=box.SIMPLE, title_style="bold")
                age_table.add_column("Age", style="yellow")
                age_table.add_column("Files", justify="right")
                age_table.add_column("Percentage", justify="right")
                
                sorted_ages = sorted(
                    self.stats['age_distribution'].items(),
                    key=lambda x: self._age_category_order(x[0])
                )
                
                for category, count in sorted_ages:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    age_table.add_row(category,
                                    self.get_human_readable(count, False),
                                    f"{percentage:.1f}%")
                
                console.print(age_table)
            
            if self.stats['largest_files']:
                largest_table = Table(title="Top 10 Largest Files", box=box.SIMPLE, title_style="bold")
                largest_table.add_column("#", justify="right", style="dim")
                largest_table.add_column("Size", justify="right")
                largest_table.add_column("Filename", style="cyan")
                largest_table.add_column("Path", style="white")
                
                for i, file_info in enumerate(self.stats['largest_files'][:10], 1):
                    if len(file_info) >= 2:
                        size = file_info[0]
                        filepath = file_info[1]
                        size_str = self.get_human_readable(size)
                        largest_table.add_row(
                            str(i),
                            size_str,
                            os.path.basename(filepath)[:30],
                            os.path.dirname(filepath)[:40] + "..." if len(os.path.dirname(filepath)) > 40 else os.path.dirname(filepath)
                        )
                
                console.print(largest_table)
            
            if self.stats['oldest_files']:
                oldest_table = Table(title="Top 10 Oldest Files", box=box.SIMPLE, title_style="bold")
                oldest_table.add_column("#", justify="right", style="dim")
                oldest_table.add_column("Size", justify="right")
                oldest_table.add_column("Filename", style="cyan")
                oldest_table.add_column("Accessed", style="white")
                
                for i, file_info in enumerate(self.stats['oldest_files'][:10], 1):
                    if len(file_info) >= 3:
                        size = file_info[0]
                        filepath = file_info[1]
                        atime = file_info[2]
                        size_str = self.get_human_readable(size)
                        accessed = atime.split('T')[0] if 'T' in atime else str(atime)[:10]
                        oldest_table.add_row(
                            str(i),
                            size_str,
                            os.path.basename(filepath)[:30],
                            accessed
                        )
                
                console.print(oldest_table)
            
            if self.stats['newest_files']:
                newest_table = Table(title="Top 10 Newest Files", box=box.SIMPLE, title_style="bold")
                newest_table.add_column("#", justify="right", style="dim")
                newest_table.add_column("Size", justify="right")
                newest_table.add_column("Filename", style="cyan")
                newest_table.add_column("Accessed", style="white")
                
                for i, file_info in enumerate(self.stats['newest_files'][:10], 1):
                    if len(file_info) >= 3:
                        size = file_info[0]
                        filepath = file_info[1]
                        atime = file_info[2]
                        size_str = self.get_human_readable(size)
                        accessed = atime.split('T')[0] if 'T' in atime else str(atime)[:10]
                        newest_table.add_row(
                            str(i),
                            size_str,
                            os.path.basename(filepath)[:30],
                            accessed
                        )
                
                console.print(newest_table)
            
            if self.stats['largest_dirs']:
                dir_table = Table(title="Top 10 Largest Directories", box=box.SIMPLE, title_style="bold")
                dir_table.add_column("#", justify="right", style="dim")
                dir_table.add_column("Size", justify="right")
                dir_table.add_column("Files", justify="right")
                dir_table.add_column("Directory", style="blue")
                
                for i, (size, file_count, dirpath) in enumerate(self.stats['largest_dirs'][:10], 1):
                    size_str = self.get_human_readable(size)
                    dir_table.add_row(
                        str(i),
                        size_str,
                        self.get_human_readable(file_count, False) if file_count > 0 else "-",
                        dirpath[:60] + "..." if len(dirpath) > 60 else dirpath
                    )
                
                console.print(dir_table)
            
            if self.stats['duplicates']:
                dup_detail_table = Table(title="Top 10 Duplicate Sets", box=box.SIMPLE, title_style="bold")
                dup_detail_table.add_column("#", justify="right", style="dim")
                dup_detail_table.add_column("Wasted", justify="right")
                dup_detail_table.add_column("Copies", justify="right")
                dup_detail_table.add_column("Total Size", justify="right")
                dup_detail_table.add_column("Sample File", style="cyan")
                
                for i, dup in enumerate(self.stats['duplicates'][:10], 1):
                    dup_detail_table.add_row(
                        str(i),
                        self.get_human_readable(dup['wasted_space']),
                        str(dup['count']),
                        self.get_human_readable(dup['total_size']),
                        os.path.basename(dup['files'][0])[:30]
                    )
                
                console.print(dup_detail_table)
            
            console.rule("[bold]Scan Complete[/bold]")
            
        else:
            print("\n" + "=" * 80)
            print("INODE ANALYSIS REPORT")
            print("=" * 80)
            
            print(f"\nSUMMARY:")
            print(f"  Total Files:           {self.get_human_readable(self.stats['total_files'], False):>18}")
            print(f"  Total Directories:     {self.get_human_readable(self.stats['total_dirs'], False):>18}")
            print(f"  Total Symlinks:        {self.get_human_readable(self.stats['total_symlinks'], False):>18}")
            print(f"  Total Sockets:         {self.get_human_readable(self.stats['total_sockets'], False):>18}")
            print(f"  Total FIFOs/pipes:     {self.get_human_readable(self.stats['total_fifos'], False):>18}")
            print(f"  Total Device files:    {self.get_human_readable(self.stats['total_devices'], False):>18}")
            print(f"  {'─' * 45}")
            print(f"  TOTAL INODES:          {self.get_human_readable(total_inodes, False):>18}")
            print(f"  Total Size:            {self.get_human_readable(self.total_size):>18}")
            print(f"  Empty Files:           {self.get_human_readable(self.stats['empty_files'], False):>18}")
            print(f"  Empty Directories:     {self.get_human_readable(self.stats['empty_dirs'], False):>18}")
            print(f"  Broken Symlinks:       {self.get_human_readable(self.stats['broken_symlinks'], False):>18}")
            print(f"  Permission Denied:     {self.get_human_readable(self.stats['permission_denied'], False):>18}")
            print(f"  Scan Time:            {elapsed_time:>18.2f} seconds")
            
            if self.stats['duplicates']:
                total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
                total_duplicate_sets = len(self.stats['duplicates'])
                total_duplicate_files = sum(d['count'] for d in self.stats['duplicates'])
                
                print(f"\nDUPLICATE FILES:")
                print(f"  Duplicate sets:        {self.get_human_readable(total_duplicate_sets, False):>18}")
                print(f"  Duplicate files:       {self.get_human_readable(total_duplicate_files, False):>18}")
                print(f"  Wasted space:          {self.get_human_readable(total_wasted):>18}")
            
            if self.stats['extensions']:
                print(f"\nTOP 10 FILE EXTENSIONS:")
                sorted_exts = sorted(
                    self.stats['extensions'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:10]
                
                for ext, count in sorted_exts:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    print(f"  .{ext:<20} {self.get_human_readable(count, False):>12} ({percentage:>6.1f}%)")
            
            if self.stats['size_distribution']:
                print(f"\nSIZE DISTRIBUTION:")
                sorted_sizes = sorted(
                    self.stats['size_distribution'].items(),
                    key=lambda x: self._size_category_order(x[0])
                )
                
                max_count = max(self.stats['size_distribution'].values()) if self.stats['size_distribution'] else 1
                
                for category, count in sorted_sizes:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    bar_length = int((count / max_count) * 40) if max_count > 0 else 0
                    bar = '█' * bar_length + '░' * (40 - bar_length)
                    print(f"  {category:<16} {self.get_human_readable(count, False):>12} ({percentage:>6.1f}%) {bar}")
            
            if self.stats['largest_files']:
                print(f"\nTOP 10 LARGEST FILES:")
                for i, file_info in enumerate(self.stats['largest_files'][:10], 1):
                    if len(file_info) >= 2:
                        size = file_info[0]
                        filepath = file_info[1]
                        size_str = self.get_human_readable(size)
                        print(f"  {i:2}. {size_str:>12} - {os.path.basename(filepath)}")
                        print(f"       Path: {os.path.dirname(filepath)[:60]}...")
            
            if self.stats['largest_dirs']:
                print(f"\nTOP 10 LARGEST DIRECTORIES:")
                for i, (size, file_count, dirpath) in enumerate(self.stats['largest_dirs'][:10], 1):
                    size_str = self.get_human_readable(size)
                    print(f"  {i:2}. {size_str:>12} - {dirpath}")
                    if file_count > 0:
                        print(f"       Files: {self.get_human_readable(file_count, False)}")

    def _size_category_order(self, category):
        order = {
            '< 1 KB': 1,
            '1 KB - 1 MB': 2,
            '1 MB - 10 MB': 3,
            '10 MB - 100 MB': 4,
            '100 MB - 1 GB': 5,
            '> 1 GB': 6
        }
        return order.get(category, 999)

    def _age_category_order(self, category):
        order = {
            'Today': 1,
            'This week': 2,
            'This month': 3,
            'This year': 4,
            '> 1 year': 5
        }
        return order.get(category, 999)

    def export_json(self, output_file):
        export_stats = self.stats.copy()
        export_stats['extensions'] = dict(export_stats['extensions'])
        export_stats['permissions'] = dict(export_stats['permissions'])
        export_stats['owners'] = dict(export_stats['owners'])
        export_stats['groups'] = dict(export_stats['groups'])
        export_stats['age_distribution'] = dict(export_stats['age_distribution'])
        export_stats['size_distribution'] = dict(export_stats['size_distribution'])
        export_stats['file_types'] = dict(export_stats['file_types'])
        export_stats['total_inodes'] = (self.stats['total_files'] + self.stats['total_dirs'] + 
                                       self.stats['total_symlinks'] + self.stats['total_sockets'] +
                                       self.stats['total_fifos'] + self.stats['total_devices'])
        export_stats['total_size_human'] = self.get_human_readable(self.total_size)
        export_stats['total_size'] = self.total_size
        export_stats['scan_time'] = datetime.now().isoformat()
        
        with open(output_file, 'w') as f:
            json.dump(export_stats, f, indent=2, default=str)
        
        if RICH_AVAILABLE:
            console.print(f"[green]JSON report exported to: {output_file}[/green]")
        else:
            print(f"\nJSON report exported to: {output_file}")

    def generate_visualization(self, output_file):
        if not PLOT_AVAILABLE:
            if RICH_AVAILABLE:
                console.print("[yellow]Matplotlib not available. Install with: pip install matplotlib[/yellow]")
            else:
                print("Matplotlib not available. Install with: pip install matplotlib")
            return
        
        try:
            fig, axes = plt.subplots(2, 2, figsize=(14, 10))
            fig.suptitle('Inode Analysis Visualization', fontsize=16)
            
            ax1 = axes[0, 0]
            file_types = dict(self.stats['file_types'])
            if file_types:
                labels = list(file_types.keys())
                sizes = list(file_types.values())
                if sizes and sum(sizes) > 0:
                    ax1.pie(sizes, labels=labels, autopct='%1.1f%%', startangle=90)
                    ax1.set_title('File Type Distribution')
            
            ax2 = axes[0, 1]
            size_dist = dict(self.stats['size_distribution'])
            if size_dist:
                categories = list(size_dist.keys())
                counts = list(size_dist.values())
                if counts and sum(counts) > 0:
                    bars = ax2.barh(range(len(categories)), counts)
                    ax2.set_yticks(range(len(categories)))
                    ax2.set_yticklabels(categories)
                    ax2.set_xlabel('Number of files')
                    ax2.set_title('File Size Distribution')
                    
                    for bar, count in zip(bars, counts):
                        width = bar.get_width()
                        ax2.text(width, bar.get_y() + bar.get_height()/2, 
                                f'{count:,}', ha='left', va='center', fontsize=8)
            
            ax3 = axes[1, 0]
            age_dist = dict(self.stats['age_distribution'])
            if age_dist:
                categories = list(age_dist.keys())
                counts = list(age_dist.values())
                if counts and sum(counts) > 0:
                    colors = ['#2ecc71', '#f1c40f', '#e67e22', '#e74c3c', '#95a5a6']
                    wedges, texts, autotexts = ax3.pie(counts, autopct='%1.1f%%', 
                                                       startangle=90, colors=colors[:len(categories)])
                    ax3.set_title('File Age Distribution')
                    ax3.legend(wedges, categories, title="Age", loc="center left", 
                              bbox_to_anchor=(1, 0, 0.5, 1))
            
            ax4 = axes[1, 1]
            if self.stats['largest_dirs']:
                dir_data = self.stats['largest_dirs'][:5]
                dir_names = [os.path.basename(d[2])[:20] for d in dir_data]
                dir_sizes = [d[0] / (1024*1024) for d in dir_data]
                if dir_sizes and any(dir_sizes):
                    colors = plt.cm.viridis_r([i/len(dir_sizes) for i in range(len(dir_sizes))])
                    bars = ax4.barh(range(len(dir_names)), dir_sizes, color=colors)
                    ax4.set_yticks(range(len(dir_names)))
                    ax4.set_yticklabels(dir_names)
                    ax4.set_xlabel('Size (MB)')
                    ax4.set_title('Largest Directories (Top 5)')
                    
                    for bar, size in zip(bars, dir_sizes):
                        width = bar.get_width()
                        ax4.text(width, bar.get_y() + bar.get_height()/2, 
                                f'{size:.1f} MB', ha='left', va='center', fontsize=8)
            
            plt.tight_layout()
            plt.savefig(output_file, dpi=150, bbox_inches='tight')
            
            if RICH_AVAILABLE:
                console.print(f"[green]Visualization saved to: {output_file}[/green]")
            else:
                print(f"\nVisualization saved to: {output_file}")
            
            if os.environ.get('DISPLAY') or sys.platform.startswith('darwin'):
                plt.show()
            else:
                plt.close()
                
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[red]Error generating visualization: {e}[/red]")
            else:
                print(f"Error generating visualization: {e}")


def main():
    parser = argparse.ArgumentParser(
        description='Deep inode usage analysis tool',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('path', nargs='?', default='.',
                       help='Directory to analyze (default: current directory)')
    
    parser.add_argument('--samples', type=int, default=20,
                       help='Number of samples for largest files/dirs (default: 20)')
    
    parser.add_argument('--deep', action='store_true',
                       help='Perform deep scan with detailed analysis')
    
    parser.add_argument('--duplicates', action='store_true',
                       help='Find duplicate files (works with --deep)')
    
    parser.add_argument('--threads', type=int, default=4,
                       help='Number of threads for deep scan (default: 4)')
    
    parser.add_argument('--json', metavar='FILE',
                       help='Export report to JSON file')
    
    parser.add_argument('--plot', metavar='FILE',
                       help='Generate visualization plot')
    
    parser.add_argument('--age', type=int, metavar='DAYS',
                       help='Only analyze files accessed/modified within N days')
    
    parser.add_argument('--symlinks', action='store_true',
                       help='Follow symbolic links')
    
    parser.add_argument('--no-rich', action='store_true',
                       help='Disable rich output (fallback to plain text)')
    
    args = parser.parse_args()
    
    if args.no_rich:
        global RICH_AVAILABLE
        RICH_AVAILABLE = False
    
    if not RICH_AVAILABLE and not args.no_rich:
        print("Note: Install 'rich' for better visualization: pip install rich", file=sys.stderr)
    
    if not HUMANIZE_AVAILABLE:
        print("Note: Install 'humanize' for better formatting: pip install humanize", file=sys.stderr)
    
    analyzer = InodeAnalyzer(threads=args.threads, follow_symlinks=args.symlinks)
    
    analyzer.analyze_directory(
        path=args.path,
        sample_size=args.samples,
        deep_scan=args.deep,
        find_duplicates=args.duplicates,
        export_json=args.json,
        generate_plot=args.plot,
        age_days=args.age
    )


if __name__ == "__main__":
    main()
