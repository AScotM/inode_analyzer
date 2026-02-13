#!/usr/bin/env python3

import os
import sys
import argparse
import json
import time
import hashlib
import heapq
import pwd
import grp
from collections import defaultdict, Counter
from pathlib import Path
from datetime import datetime, timedelta
import subprocess
import stat
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import fnmatch
import pickle
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Any, Set
import signal

try:
    from rich.console import Console
    from rich.table import Table
    from rich.progress import Progress, SpinnerColumn, BarColumn, TextColumn, TimeElapsedColumn
    from rich.tree import Tree
    from rich.panel import Panel
    from rich.layout import Layout
    from rich.live import Live
    from rich.text import Text
    from rich import box
    from rich.style import Style
    from rich.color import Color
    from rich.columns import Columns
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
    import matplotlib.patches as mpatches
    from matplotlib.patches import Rectangle
    import numpy as np
    PLOT_AVAILABLE = True
except ImportError:
    PLOT_AVAILABLE = False

try:
    import xxhash
    HASH_FAST_AVAILABLE = True
except ImportError:
    HASH_FAST_AVAILABLE = False


@dataclass
class FileMetadata:
    path: str
    size: int
    mtime: datetime
    atime: datetime
    ctime: datetime
    owner: str
    group: str
    permissions: str
    extension: str = ''
    is_duplicate: bool = False
    checksum: Optional[str] = None


@dataclass
class DirectoryStats:
    path: str
    size: int
    file_count: int
    dir_count: int
    avg_file_size: float
    largest_file: str
    largest_file_size: int


class ProgressTracker:
    def __init__(self, total: int, description: str = "Processing"):
        self.total = total
        self.current = 0
        self.description = description
        self.start_time = time.time()
        self.lock = threading.Lock()
    
    def update(self, n: int = 1):
        with self.lock:
            self.current += n
    
    def get_progress(self) -> Tuple[float, float]:
        with self.lock:
            elapsed = time.time() - self.start_time
            if self.current > 0:
                rate = self.current / elapsed
                eta = (self.total - self.current) / rate if rate > 0 else 0
            else:
                eta = 0
            return (self.current / self.total * 100 if self.total > 0 else 0, eta)
    
    def format_eta(self, seconds: float) -> str:
        if seconds < 60:
            return f"{seconds:.0f}s"
        elif seconds < 3600:
            return f"{seconds/60:.1f}m"
        else:
            return f"{seconds/3600:.1f}h"


class InodeAnalyzer:
    def __init__(self, threads=4, follow_symlinks=False, exclude_patterns=None):
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
            'file_types': defaultdict(int),
            'top_level_summary': {}
        }
        self.threads = threads
        self.follow_symlinks = follow_symlinks
        self.exclude_patterns = exclude_patterns or []
        self.total_size = 0
        self.lock = threading.Lock()
        self.processed_paths = set()
        self.file_metadata = {}
        self.directory_cache = {}
        self.interrupted = False
        
        self.largest_files_heap = []
        self.oldest_files_heap = []
        self.newest_files_heap = []
        
        signal.signal(signal.SIGINT, self._handle_interrupt)
    
    def _handle_interrupt(self, signum, frame):
        self.interrupted = True
        if RICH_AVAILABLE:
            console.print("\n[yellow]Interrupt received, finishing current operations...[/yellow]")
        else:
            print("\nInterrupt received, finishing current operations...")
    
    def get_human_readable(self, value, is_bytes=True):
        if HUMANIZE_AVAILABLE:
            if is_bytes:
                return humanize.naturalsize(value)
            return humanize.intcomma(value)
        return f"{value:,}"
    
    def _should_exclude(self, path: Path) -> bool:
        str_path = str(path)
        for pattern in self.exclude_patterns:
            if fnmatch.fnmatch(str_path, pattern) or fnmatch.fnmatch(os.path.basename(str_path), pattern):
                return True
        return False
    
    def analyze_directory(self, path, sample_size=20, deep_scan=False, 
                         find_duplicates=False, export_json=None, 
                         generate_plot=None, age_days=None, save_state=None,
                         load_state=None, max_depth=None):
        
        if load_state:
            self.load_checkpoint(load_state)
            return
        
        path = Path(path).resolve()
        if not path.exists():
            if RICH_AVAILABLE:
                console.print(f"[bold red]✗ Path does not exist: {path}[/bold red]")
            else:
                print(f"Error: Path does not exist: {path}")
            return
        
        start_time = time.time()
        
        if RICH_AVAILABLE:
            layout = Layout()
            layout.split(
                Layout(name="header", size=3),
                Layout(name="body"),
                Layout(name="footer", size=3)
            )
            
            console.rule(f"[bold blue]╔══ Inode Analyzer v2.0 ══╗[/bold blue]")
            console.print(f"[bold]Target:[/bold] [cyan]{path}[/cyan]")
            console.print(f"[bold]Mode:[/bold] [{'green' if deep_scan else 'yellow'}]{'Deep Scan' if deep_scan else 'Quick Scan'}[/]")
            console.print(f"[bold]Duplicates:[/bold] [{'green' if find_duplicates else 'yellow'}]{'Enabled' if find_duplicates else 'Disabled'}[/]")
            console.print()
        else:
            print(f"\n{'='*80}")
            print(f"INODE ANALYZER v2.0")
            print(f"{'='*80}")
            print(f"Target: {path}")
            print(f"Mode: {'Deep Scan' if deep_scan else 'Quick Scan'}")
            print(f"Duplicates: {'Enabled' if find_duplicates else 'Disabled'}")
            print(f"{'='*80}\n")
        
        if deep_scan:
            self._deep_scan_analysis(path, sample_size, find_duplicates, age_days, max_depth)
        else:
            self._quick_scan_analysis(path, sample_size, max_depth)
        
        if find_duplicates and not deep_scan:
            self.find_duplicate_files(path)
        
        if save_state:
            self.save_checkpoint(save_state)
        
        elapsed_time = time.time() - start_time
        self.print_report(elapsed_time)
        
        if export_json:
            self.export_json(export_json)
        
        if generate_plot:
            self.generate_visualization(generate_plot)

    def _quick_scan_analysis(self, path, sample_size, max_depth=None):
        try:
            if RICH_AVAILABLE:
                console.print("[cyan]► Scanning filesystem...[/cyan]")
            
            files_count = 0
            dirs_count = 0
            symlinks_count = 0
            sockets_count = 0
            fifos_count = 0
            devices_count = 0
            
            current_depth = 0
            base_depth = len(path.parts)
            
            for root, dirs, files in os.walk(path):
                if self.interrupted:
                    break
                
                current_depth = len(Path(root).parts) - base_depth
                if max_depth and current_depth >= max_depth:
                    dirs.clear()
                
                dirs_count += len(dirs)
                files_count += len(files)
                
                for file in files:
                    filepath = os.path.join(root, file)
                    
                    if self._should_exclude(Path(filepath)):
                        continue
                    
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
                            
                            mtime = datetime.fromtimestamp(stat_info.st_mtime)
                            age_category = self._categorize_age(mtime)
                            self.stats['age_distribution'][age_category] += 1
                            
                            metadata = FileMetadata(
                                path=filepath,
                                size=size,
                                mtime=mtime,
                                atime=datetime.fromtimestamp(stat_info.st_atime),
                                ctime=datetime.fromtimestamp(stat_info.st_ctime),
                                owner=owner,
                                group=group,
                                permissions=perms,
                                extension=ext
                            )
                            
                            self.file_metadata[filepath] = metadata
                            
                            heapq.heappush(self.largest_files_heap, (size, filepath, mtime.isoformat(), owner, group, perms))
                            if len(self.largest_files_heap) > sample_size * 2:
                                heapq.heappop(self.largest_files_heap)
                            
                            heapq.heappush(self.oldest_files_heap, (mtime.timestamp(), filepath, size, owner, group, perms))
                            if len(self.oldest_files_heap) > sample_size * 2:
                                heapq.heappop(self.oldest_files_heap)
                            
                            heapq.heappush(self.newest_files_heap, (-mtime.timestamp(), filepath, size, owner, group, perms))
                            if len(self.newest_files_heap) > sample_size * 2:
                                heapq.heappop(self.newest_files_heap)
                                
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
            
            largest_list = []
            for item in self.largest_files_heap:
                largest_list.append(item)
            largest_list.sort(key=lambda x: x[0], reverse=True)
            self.stats['largest_files'] = largest_list[:sample_size]
            
            oldest_list = []
            for item in self.oldest_files_heap:
                oldest_list.append(item)
            oldest_list.sort(key=lambda x: x[0])
            self.stats['oldest_files'] = [(item[2], item[1], datetime.fromtimestamp(item[0]).isoformat(), item[3], item[4], item[5]) 
                                         for item in oldest_list[:sample_size]]
            
            newest_list = []
            for item in self.newest_files_heap:
                newest_list.append(item)
            newest_list.sort(key=lambda x: x[0])
            self.stats['newest_files'] = [(item[2], item[1], datetime.fromtimestamp(-item[0]).isoformat(), item[3], item[4], item[5]) 
                                         for item in newest_list[:sample_size]]
            
            self._analyze_largest_directories(path, sample_size)
            
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[yellow]Scan failed: {e}, using fallback...[/yellow]")
            else:
                print(f"Scan failed: {e}, using fallback...")
            self._fallback_analysis(path, sample_size)

    def _deep_scan_analysis(self, path, sample_size, find_duplicates, age_days=None, max_depth=None):
        if RICH_AVAILABLE:
            console.print("[bold blue]▼ Performing Deep Analysis ▼[/bold blue]")
            console.print()
        else:
            print("\nPerforming deep scan analysis...\n")
        
        all_items = []
        
        try:
            base_depth = len(path.parts)
            for root, dirs, files in os.walk(path):
                if self.interrupted:
                    break
                
                current_depth = len(Path(root).parts) - base_depth
                if max_depth and current_depth >= max_depth:
                    dirs.clear()
                
                if not self._should_exclude(Path(root)):
                    all_items.append(Path(root))
                
                for d in dirs:
                    dir_path = Path(root) / d
                    if not self._should_exclude(dir_path):
                        try:
                            all_items.append(dir_path)
                        except Exception:
                            pass
                
                for f in files:
                    file_path = Path(root) / f
                    if not self._should_exclude(file_path):
                        try:
                            all_items.append(file_path)
                        except Exception:
                            pass
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[red]Error during walk: {e}[/red]")
            else:
                print(f"Error during walk: {e}")
            return
        
        total_items = len(all_items)
        tracker = ProgressTracker(total_items, "Analyzing items")
        
        if RICH_AVAILABLE:
            with Progress(
                SpinnerColumn(),
                TextColumn("[progress.description]{task.description}"),
                BarColumn(bar_width=40),
                TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
                TextColumn("•"),
                TimeElapsedColumn(),
                TextColumn("•"),
                TextColumn("[cyan]{task.fields[eta]}[/cyan]"),
                console=console
            ) as progress:
                task = progress.add_task("[cyan]Scanning items...", total=total_items, eta="--:--")
                
                with ThreadPoolExecutor(max_workers=self.threads) as executor:
                    futures = []
                    for item in all_items:
                        if str(item) not in self.processed_paths and not self.interrupted:
                            self.processed_paths.add(str(item))
                            futures.append(executor.submit(self._analyze_item_deep, item, age_days))
                    
                    for future in as_completed(futures):
                        if self.interrupted:
                            executor.shutdown(wait=False)
                            break
                        future.result()
                        tracker.update(1)
                        progress.update(task, advance=1, 
                                      eta=tracker.format_eta(tracker.get_progress()[1]))
        else:
            print(f"  Scanning {self.get_human_readable(total_items, False)} items...")
            with ThreadPoolExecutor(max_workers=self.threads) as executor:
                futures = []
                for item in all_items:
                    if str(item) not in self.processed_paths and not self.interrupted:
                        self.processed_paths.add(str(item))
                        futures.append(executor.submit(self._analyze_item_deep, item, age_days))
                
                for i, future in enumerate(as_completed(futures)):
                    if self.interrupted:
                        executor.shutdown(wait=False)
                        break
                    future.result()
                    if i % 100 == 0 and total_items > 0:
                        progress = (i + 1) / total_items * 100
                        eta = tracker.format_eta(tracker.get_progress()[1])
                        print(f"\r  Progress: {progress:.1f}% ({i+1:,}/{total_items:,}) • ETA: {eta}", end='', flush=True)
            
            if not self.interrupted:
                print(f"\r  Progress: 100% ({total_items:,}/{total_items:,}) {' ' * 20}")
        
        if self.interrupted:
            if RICH_AVAILABLE:
                console.print("[yellow]Scan interrupted. Partial results available.[/yellow]")
            else:
                print("\nScan interrupted. Partial results available.")
        
        largest_list = []
        for item in self.largest_files_heap:
            largest_list.append(item)
        largest_list.sort(key=lambda x: x[0], reverse=True)
        self.stats['largest_files'] = largest_list[:sample_size]
        
        oldest_list = []
        for item in self.oldest_files_heap:
            oldest_list.append(item)
        oldest_list.sort(key=lambda x: x[0])
        self.stats['oldest_files'] = [(item[2], item[1], datetime.fromtimestamp(item[0]).isoformat(), item[3], item[4], item[5]) 
                                     for item in oldest_list[:sample_size]]
        
        newest_list = []
        for item in self.newest_files_heap:
            newest_list.append(item)
        newest_list.sort(key=lambda x: x[0])
        self.stats['newest_files'] = [(item[2], item[1], datetime.fromtimestamp(-item[0]).isoformat(), item[3], item[4], item[5]) 
                                     for item in newest_list[:sample_size]]
        
        self._analyze_largest_directories(path, sample_size, deep=True)
        
        if find_duplicates and not self.interrupted:
            self.find_duplicate_files(path)

    def _analyze_item_deep(self, item: Path, age_days=None):
        try:
            if self._should_exclude(item):
                return
            
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
                
                ext = ''
                if item.name and '.' in item.name:
                    ext = item.name.rsplit('.', 1)[-1].lower()
                
                with self.lock:
                    if ext:
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
                    
                    mtime = datetime.fromtimestamp(stat_info.st_mtime)
                    atime = datetime.fromtimestamp(stat_info.st_atime)
                    ctime = datetime.fromtimestamp(stat_info.st_ctime)
                    
                    age_category = self._categorize_age(mtime)
                    self.stats['age_distribution'][age_category] += 1
                    
                    metadata = FileMetadata(
                        path=str(item),
                        size=size,
                        mtime=mtime,
                        atime=atime,
                        ctime=ctime,
                        owner=owner,
                        group=group,
                        permissions=oct(mode)[-4:],
                        extension=ext
                    )
                    
                    self.file_metadata[str(item)] = metadata
                    
                    heapq.heappush(self.largest_files_heap, (size, str(item), mtime.isoformat(), owner, group, oct(mode)[-4:]))
                    if len(self.largest_files_heap) > 1000:
                        heapq.heappop(self.largest_files_heap)
                    
                    heapq.heappush(self.oldest_files_heap, (mtime.timestamp(), str(item), size, owner, group, oct(mode)[-4:]))
                    if len(self.oldest_files_heap) > 1000:
                        heapq.heappop(self.oldest_files_heap)
                    
                    heapq.heappush(self.newest_files_heap, (-mtime.timestamp(), str(item), size, owner, group, oct(mode)[-4:]))
                    if len(self.newest_files_heap) > 1000:
                        heapq.heappop(self.newest_files_heap)
            
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
            dir_stats = {}
            
            for filepath, metadata in self.file_metadata.items():
                dir_path = os.path.dirname(filepath)
                if dir_path not in dir_stats:
                    dir_stats[dir_path] = {'size': 0, 'count': 0, 'largest': 0, 'largest_file': ''}
                
                dir_stats[dir_path]['size'] += metadata.size
                dir_stats[dir_path]['count'] += 1
                
                if metadata.size > dir_stats[dir_path]['largest']:
                    dir_stats[dir_path]['largest'] = metadata.size
                    dir_stats[dir_path]['largest_file'] = os.path.basename(filepath)
            
            dir_list = []
            for dir_path, stats in dir_stats.items():
                avg_size = stats['size'] / stats['count'] if stats['count'] > 0 else 0
                dir_list.append(DirectoryStats(
                    path=dir_path,
                    size=stats['size'],
                    file_count=stats['count'],
                    dir_count=0,
                    avg_file_size=avg_size,
                    largest_file=stats['largest_file'],
                    largest_file_size=stats['largest']
                ))
            
            dir_list.sort(key=lambda x: x.size, reverse=True)
            self.stats['largest_dirs'] = [
                (d.size, d.file_count, d.path, d.avg_file_size, d.largest_file, d.largest_file_size) 
                for d in dir_list[:sample_size]
            ]
            
        except Exception as e:
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
                    (size, 0, dirpath, 0, '', 0) for size, dirpath in dirs[:sample_size]
                ]
            except subprocess.TimeoutExpired:
                pass
            except (subprocess.SubprocessError, FileNotFoundError):
                pass

    def find_duplicate_files(self, path):
        if RICH_AVAILABLE:
            console.print("[bold blue]► Searching for duplicate files...[/bold blue]")
        else:
            print("  Searching for duplicate files...")
        
        size_dict = defaultdict(list)
        file_count = 0
        
        for root, dirs, files in os.walk(path):
            if self.interrupted:
                break
            
            for file in files:
                filepath = os.path.join(root, file)
                
                if self._should_exclude(Path(filepath)):
                    continue
                
                try:
                    if os.path.isfile(filepath):
                        size = os.path.getsize(filepath)
                        if size > 0:
                            size_dict[size].append(filepath)
                            file_count += 1
                except OSError:
                    continue
        
        if self.interrupted:
            return
        
        total_candidates = sum(1 for paths in size_dict.values() if len(paths) > 1)
        
        if RICH_AVAILABLE:
            console.print(f"  Found [cyan]{self.get_human_readable(file_count, False)}[/cyan] files, [yellow]{self.get_human_readable(total_candidates, False)}[/yellow] potential duplicate sets")
            console.print("[bold blue]► Computing checksums...[/bold blue]")
            
            with Progress(
                BarColumn(bar_width=40),
                TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
                TextColumn("•"),
                TimeElapsedColumn(),
                console=console
            ) as progress:
                task = progress.add_task("[cyan]Hashing files...", total=total_candidates)
                
                for size, filepaths in size_dict.items():
                    if len(filepaths) > 1:
                        checksum_dict = defaultdict(list)
                        
                        for filepath in filepaths:
                            try:
                                checksum = self._calculate_hash_fast(filepath)
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
                        
                        progress.update(task, advance=1)
        else:
            print(f"    Found {self.get_human_readable(file_count, False)} files, {self.get_human_readable(total_candidates, False)} potential duplicate sets")
            print("    Computing checksums...")
            
            processed = 0
            for size, filepaths in size_dict.items():
                if len(filepaths) > 1:
                    checksum_dict = defaultdict(list)
                    
                    for filepath in filepaths:
                        try:
                            checksum = self._calculate_hash_fast(filepath)
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
                    
                    processed += 1
                    if processed % 10 == 0:
                        print(f"\r      Progress: {processed}/{total_candidates}", end='', flush=True)
            
            print(f"\r      Progress: {total_candidates}/{total_candidates} complete!")
        
        self.stats['duplicates'].sort(key=lambda x: x['wasted_space'], reverse=True)
        
        if RICH_AVAILABLE:
            total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
            console.print(f"  Found [red]{self.get_human_readable(len(self.stats['duplicates']), False)}[/red] duplicate sets, wasting [red]{self.get_human_readable(total_wasted)}[/red]")
        else:
            total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
            print(f"    Found {self.get_human_readable(len(self.stats['duplicates']), False)} duplicate sets, wasting {self.get_human_readable(total_wasted)}")

    def _calculate_hash_fast(self, filepath, buffer_size=65536):
        if HASH_FAST_AVAILABLE:
            hasher = xxhash.xxh64()
        else:
            hasher = hashlib.md5()
        
        try:
            with open(filepath, 'rb') as f:
                buffer = f.read(buffer_size)
                while buffer:
                    hasher.update(buffer)
                    buffer = f.read(buffer_size)
            return hasher.hexdigest()
        except Exception:
            return None

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
            console.print("[yellow]► Using fallback analysis method...[/yellow]")
        else:
            print("  Using fallback analysis method...")
        
        files_data = []
        
        for root, dirs, files in os.walk(path):
            if self.interrupted:
                break
            
            self.stats['total_dirs'] += 1
            self.stats['total_files'] += len(files)
            
            for file in files:
                if '.' in file:
                    ext = file.rsplit('.', 1)[-1].lower()
                    self.stats['extensions'][ext] += 1
                
                filepath = os.path.join(root, file)
                
                if self._should_exclude(Path(filepath)):
                    continue
                
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
                        
                        heapq.heappush(self.largest_files_heap, (size, filepath, '', '', '', ''))
                        if len(self.largest_files_heap) > sample_size * 2:
                            heapq.heappop(self.largest_files_heap)
                    
                except OSError:
                    self.stats['permission_denied'] += 1
            
            for dirname in dirs:
                dirpath = os.path.join(root, dirname)
                try:
                    if not os.listdir(dirpath):
                        self.stats['empty_dirs'] += 1
                except OSError:
                    pass
        
        largest_list = []
        for item in self.largest_files_heap:
            largest_list.append(item)
        largest_list.sort(key=lambda x: x[0], reverse=True)
        self.stats['largest_files'] = largest_list[:sample_size]

    def print_report(self, elapsed_time):
        total_inodes = (self.stats['total_files'] + self.stats['total_dirs'] + 
                       self.stats['total_symlinks'] + self.stats['total_sockets'] +
                       self.stats['total_fifos'] + self.stats['total_devices'])
        
        if RICH_AVAILABLE:
            console.rule("[bold green]══════ INODE ANALYSIS REPORT ══════[/bold green]")
            
            summary_panel = Panel(
                f"[bold cyan]Files:[/bold cyan] {self.get_human_readable(self.stats['total_files'], False)} • "
                f"[bold cyan]Dirs:[/bold cyan] {self.get_human_readable(self.stats['total_dirs'], False)} • "
                f"[bold cyan]Symlinks:[/bold cyan] {self.get_human_readable(self.stats['total_symlinks'], False)} • "
                f"[bold cyan]Special:[/bold cyan] {self.get_human_readable(self.stats['total_sockets'] + self.stats['total_fifos'] + self.stats['total_devices'], False)}\n"
                f"[bold yellow]Total Size:[/bold yellow] {self.get_human_readable(self.total_size)} • "
                f"[bold yellow]Total Inodes:[/bold yellow] {self.get_human_readable(total_inodes, False)} • "
                f"[bold yellow]Scan Time:[/bold yellow] {elapsed_time:.2f}s\n"
                f"[bold red]Issues:[/bold red] {self.get_human_readable(self.stats['empty_files'], False)} empty, "
                f"{self.get_human_readable(self.stats['empty_dirs'], False)} empty dirs, "
                f"{self.get_human_readable(self.stats['broken_symlinks'], False)} broken, "
                f"{self.get_human_readable(self.stats['permission_denied'], False)} denied",
                title="[bold]📊 Summary[/bold]",
                border_style="green",
                padding=(1, 2)
            )
            console.print(summary_panel)
            
            if self.stats['duplicates']:
                total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
                total_duplicate_sets = len(self.stats['duplicates'])
                total_duplicate_files = sum(d['count'] for d in self.stats['duplicates'])
                
                dup_panel = Panel(
                    f"[bold red]⚠ Duplicate Files Detected ⚠[/bold red]\n\n"
                    f"[white]Sets:[/white] {self.get_human_readable(total_duplicate_sets, False)} • "
                    f"[white]Files:[/white] {self.get_human_readable(total_duplicate_files, False)} • "
                    f"[white]Wasted:[/white] [bold red]{self.get_human_readable(total_wasted)}[/bold red]",
                    border_style="red",
                    padding=(1, 2)
                )
                console.print(dup_panel)
            
            col1 = Columns(2)
            
            if self.stats['extensions']:
                ext_table = Table(title="[bold]📁 Top 10 Extensions[/bold]", box=box.ROUNDED, 
                                title_style="bold cyan", header_style="cyan", border_style="blue")
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
                owner_table = Table(title="[bold]👤 Top 10 Owners[/bold]", box=box.ROUNDED,
                                  title_style="bold cyan", header_style="cyan", border_style="blue")
                owner_table.add_column("Owner", style="yellow")
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
            
            if self.stats['size_distribution']:
                size_table = Table(title="[bold]📊 Size Distribution[/bold]", box=box.ROUNDED,
                                 title_style="bold cyan", header_style="cyan", border_style="blue")
                size_table.add_column("Size Range", style="magenta")
                size_table.add_column("Files", justify="right")
                size_table.add_column("Percentage", justify="right")
                size_table.add_column("Visual", justify="left")
                
                sorted_sizes = sorted(
                    self.stats['size_distribution'].items(),
                    key=lambda x: self._size_category_order(x[0])
                )
                
                max_count = max(self.stats['size_distribution'].values()) if self.stats['size_distribution'] else 1
                
                colors = ['▅', '█', '▇', '▓', '▒', '░']
                for i, (category, count) in enumerate(sorted_sizes):
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    bar_length = int((count / max_count) * 30) if max_count > 0 else 0
                    bar = colors[i % len(colors)] * bar_length + ' ' * (30 - bar_length)
                    size_table.add_row(category,
                                     self.get_human_readable(count, False),
                                     f"{percentage:.1f}%",
                                     f"[cyan]{bar}[/cyan]")
                
                console.print(size_table)
            
            if self.stats['age_distribution']:
                age_table = Table(title="[bold]⏰ Age Distribution[/bold]", box=box.ROUNDED,
                                title_style="bold cyan", header_style="cyan", border_style="blue")
                age_table.add_column("Age", style="yellow")
                age_table.add_column("Files", justify="right")
                age_table.add_column("Percentage", justify="right")
                age_table.add_column("Visual", justify="left")
                
                sorted_ages = sorted(
                    self.stats['age_distribution'].items(),
                    key=lambda x: self._age_category_order(x[0])
                )
                
                max_count = max(self.stats['age_distribution'].values()) if self.stats['age_distribution'] else 1
                
                for category, count in sorted_ages:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    bar_length = int((count / max_count) * 30) if max_count > 0 else 0
                    bar = '█' * bar_length + '░' * (30 - bar_length)
                    age_table.add_row(category,
                                    self.get_human_readable(count, False),
                                    f"{percentage:.1f}%",
                                    f"[green]{bar}[/green]")
                
                console.print(age_table)
            
            if self.stats['largest_files']:
                largest_table = Table(title="[bold]💾 Top 10 Largest Files[/bold]", box=box.ROUNDED,
                                    title_style="bold cyan", header_style="cyan", border_style="blue")
                largest_table.add_column("#", justify="right", style="dim")
                largest_table.add_column("Size", justify="right")
                largest_table.add_column("Filename", style="cyan")
                largest_table.add_column("Location", style="white")
                largest_table.add_column("Owner", style="yellow")
                
                for i, file_info in enumerate(self.stats['largest_files'][:10], 1):
                    if len(file_info) >= 6:
                        size, filepath, atime, owner, group, perms = file_info
                        size_str = self.get_human_readable(size)
                        largest_table.add_row(
                            str(i),
                            f"[red]{size_str}[/red]",
                            os.path.basename(filepath)[:25],
                            os.path.dirname(filepath)[:25] + "..." if len(os.path.dirname(filepath)) > 25 else os.path.dirname(filepath),
                            owner[:15]
                        )
                
                console.print(largest_table)
            
            if self.stats['largest_dirs']:
                dir_table = Table(title="[bold]📂 Top 10 Largest Directories[/bold]", box=box.ROUNDED,
                                title_style="bold cyan", header_style="cyan", border_style="blue")
                dir_table.add_column("#", justify="right", style="dim")
                dir_table.add_column("Size", justify="right")
                dir_table.add_column("Files", justify="right")
                dir_table.add_column("Avg Size", justify="right")
                dir_table.add_column("Directory", style="blue")
                
                for i, dir_info in enumerate(self.stats['largest_dirs'][:10], 1):
                    if len(dir_info) >= 6:
                        size, file_count, dirpath, avg_size, largest_file, largest_size = dir_info
                        size_str = self.get_human_readable(size)
                        avg_size_str = self.get_human_readable(avg_size) if avg_size > 0 else "-"
                        dir_table.add_row(
                            str(i),
                            f"[yellow]{size_str}[/yellow]",
                            self.get_human_readable(file_count, False),
                            avg_size_str,
                            os.path.basename(dirpath) if len(dirpath) < 40 else f"...{dirpath[-40:]}"
                        )
                
                console.print(dir_table)
            
            if self.stats['duplicates']:
                dup_detail_table = Table(title="[bold]⚠ Top 10 Duplicate Sets[/bold]", box=box.ROUNDED,
                                       title_style="bold red", header_style="red", border_style="red")
                dup_detail_table.add_column("#", justify="right", style="dim")
                dup_detail_table.add_column("Wasted", justify="right")
                dup_detail_table.add_column("Copies", justify="right")
                dup_detail_table.add_column("Size Each", justify="right")
                dup_detail_table.add_column("Sample File", style="cyan")
                
                for i, dup in enumerate(self.stats['duplicates'][:10], 1):
                    dup_detail_table.add_row(
                        str(i),
                        f"[red]{self.get_human_readable(dup['wasted_space'])}[/red]",
                        str(dup['count']),
                        self.get_human_readable(dup['size']),
                        os.path.basename(dup['files'][0])[:30]
                    )
                
                console.print(dup_detail_table)
            
            if self.stats['permissions']:
                perm_table = Table(title="[bold]🔐 Top 10 Permissions[/bold]", box=box.SIMPLE,
                                 title_style="bold cyan", header_style="cyan")
                perm_table.add_column("Permissions", style="green")
                perm_table.add_column("Count", justify="right")
                perm_table.add_column("Percentage", justify="right")
                
                sorted_perms = sorted(
                    self.stats['permissions'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:10]
                
                for perm, count in sorted_perms:
                    percentage = (count / max(self.stats['total_files'], 1)) * 100
                    perm_table.add_row(perm,
                                     self.get_human_readable(count, False),
                                     f"{percentage:.1f}%")
                
                console.print(perm_table)
            
            if self.interrupted:
                console.print("[yellow]╔════════════════════════════════════════╗[/yellow]")
                console.print("[yellow]║     SCAN INTERRUPTED - PARTIAL DATA    ║[/yellow]")
                console.print("[yellow]╚════════════════════════════════════════╝[/yellow]")
            else:
                console.rule("[bold green]══════ Scan Complete ══════[/bold green]")
            
        else:
            print("\n" + "═" * 80)
            print("                    INODE ANALYSIS REPORT")
            print("═" * 80)
            
            print(f"\nSUMMARY:")
            print(f"  ┌{'─'*50}┐")
            print(f"  │ Files:          {self.get_human_readable(self.stats['total_files'], False):>20} │")
            print(f"  │ Directories:    {self.get_human_readable(self.stats['total_dirs'], False):>20} │")
            print(f"  │ Symlinks:       {self.get_human_readable(self.stats['total_symlinks'], False):>20} │")
            print(f"  │ Special files:  {self.get_human_readable(self.stats['total_sockets'] + self.stats['total_fifos'] + self.stats['total_devices'], False):>20} │")
            print(f"  ├{'─'*50}┤")
            print(f"  │ TOTAL INODES:   {self.get_human_readable(total_inodes, False):>20} │")
            print(f"  │ TOTAL SIZE:     {self.get_human_readable(self.total_size):>20} │")
            print(f"  ├{'─'*50}┤")
            print(f"  │ Empty files:    {self.get_human_readable(self.stats['empty_files'], False):>20} │")
            print(f"  │ Empty dirs:     {self.get_human_readable(self.stats['empty_dirs'], False):>20} │")
            print(f"  │ Broken links:   {self.get_human_readable(self.stats['broken_symlinks'], False):>20} │")
            print(f"  │ Permission err: {self.get_human_readable(self.stats['permission_denied'], False):>20} │")
            print(f"  │ Scan time:      {elapsed_time:>20.2f}s │")
            print(f"  └{'─'*50}┘")
            
            if self.stats['duplicates']:
                total_wasted = sum(d['wasted_space'] for d in self.stats['duplicates'])
                total_duplicate_sets = len(self.stats['duplicates'])
                total_duplicate_files = sum(d['count'] for d in self.stats['duplicates'])
                
                print(f"\nDUPLICATE FILES:")
                print(f"  ┌{'─'*50}┐")
                print(f"  │ Duplicate sets:  {self.get_human_readable(total_duplicate_sets, False):>20} │")
                print(f"  │ Duplicate files: {self.get_human_readable(total_duplicate_files, False):>20} │")
                print(f"  │ Wasted space:    {self.get_human_readable(total_wasted):>20} │")
                print(f"  └{'─'*50}┘")
            
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
            
            if self.interrupted:
                print("\n" + "!" * 60)
                print("  SCAN INTERRUPTED - RESULTS ARE PARTIAL")
                print("!" * 60)

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
        export_stats['interrupted'] = self.interrupted
        
        if self.file_metadata:
            export_stats['file_sample'] = [
                {
                    'path': meta.path,
                    'size': meta.size,
                    'mtime': meta.mtime.isoformat(),
                    'owner': meta.owner,
                    'group': meta.group,
                    'permissions': meta.permissions
                }
                for path, meta in list(self.file_metadata.items())[:100]
            ]
        
        with open(output_file, 'w') as f:
            json.dump(export_stats, f, indent=2, default=str)
        
        if RICH_AVAILABLE:
            console.print(f"[green]✓ JSON report exported to: {output_file}[/green]")
        else:
            print(f"\nJSON report exported to: {output_file}")

    def save_checkpoint(self, checkpoint_file):
        checkpoint = {
            'stats': dict(self.stats),
            'total_size': self.total_size,
            'processed_paths': list(self.processed_paths)[:10000],
            'timestamp': datetime.now().isoformat(),
            'interrupted': self.interrupted
        }
        
        checkpoint['stats']['extensions'] = dict(self.stats['extensions'])
        checkpoint['stats']['permissions'] = dict(self.stats['permissions'])
        checkpoint['stats']['owners'] = dict(self.stats['owners'])
        checkpoint['stats']['groups'] = dict(self.stats['groups'])
        checkpoint['stats']['age_distribution'] = dict(self.stats['age_distribution'])
        checkpoint['stats']['size_distribution'] = dict(self.stats['size_distribution'])
        checkpoint['stats']['file_types'] = dict(self.stats['file_types'])
        
        with open(checkpoint_file, 'wb') as f:
            pickle.dump(checkpoint, f)
        
        if RICH_AVAILABLE:
            console.print(f"[green]✓ Checkpoint saved to: {checkpoint_file}[/green]")
        else:
            print(f"\nCheckpoint saved to: {checkpoint_file}")

    def load_checkpoint(self, checkpoint_file):
        try:
            with open(checkpoint_file, 'rb') as f:
                checkpoint = pickle.load(f)
            
            self.stats.update(checkpoint['stats'])
            self.total_size = checkpoint['total_size']
            self.processed_paths = set(checkpoint['processed_paths'])
            self.interrupted = checkpoint['interrupted']
            
            self.stats['extensions'] = defaultdict(int, checkpoint['stats'].get('extensions', {}))
            self.stats['permissions'] = defaultdict(int, checkpoint['stats'].get('permissions', {}))
            self.stats['owners'] = defaultdict(int, checkpoint['stats'].get('owners', {}))
            self.stats['groups'] = defaultdict(int, checkpoint['stats'].get('groups', {}))
            self.stats['age_distribution'] = defaultdict(int, checkpoint['stats'].get('age_distribution', {}))
            self.stats['size_distribution'] = defaultdict(int, checkpoint['stats'].get('size_distribution', {}))
            self.stats['file_types'] = defaultdict(int, checkpoint['stats'].get('file_types', {}))
            
            if RICH_AVAILABLE:
                console.print(f"[green]✓ Checkpoint loaded from: {checkpoint_file}[/green]")
                console.print(f"[cyan]  Scan date: {checkpoint['timestamp']}[/cyan]")
            else:
                print(f"\nCheckpoint loaded from: {checkpoint_file}")
                print(f"  Scan date: {checkpoint['timestamp']}")
                
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[red]✗ Failed to load checkpoint: {e}[/red]")
            else:
                print(f"Failed to load checkpoint: {e}")

    def generate_visualization(self, output_file):
        if not PLOT_AVAILABLE:
            if RICH_AVAILABLE:
                console.print("[yellow]⚠ Matplotlib not available. Install with: pip install matplotlib[/yellow]")
            else:
                print("Matplotlib not available. Install with: pip install matplotlib")
            return
        
        try:
            plt.style.use('seaborn-v0_8-darkgrid')
            fig = plt.figure(figsize=(20, 12))
            fig.patch.set_facecolor('#f8f9fa')
            
            gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)
            
            ax1 = fig.add_subplot(gs[0, 0])
            file_types = dict(self.stats['file_types'])
            if file_types:
                labels = list(file_types.keys())
                sizes = list(file_types.values())
                if sizes and sum(sizes) > 0:
                    colors = plt.cm.Set3(np.linspace(0, 1, len(labels)))
                    wedges, texts, autotexts = ax1.pie(sizes, labels=labels, autopct='%1.1f%%', 
                                                       startangle=90, colors=colors,
                                                       wedgeprops={'edgecolor': 'white', 'linewidth': 2},
                                                       textprops={'fontsize': 10, 'weight': 'bold'})
                    for autotext in autotexts:
                        autotext.set_color('white')
                        autotext.set_weight('bold')
                    ax1.set_title('File Type Distribution', fontsize=14, weight='bold', pad=20)
            
            ax2 = fig.add_subplot(gs[0, 1])
            size_dist = dict(self.stats['size_distribution'])
            if size_dist:
                categories = list(size_dist.keys())
                counts = list(size_dist.values())
                if counts and sum(counts) > 0:
                    colors = plt.cm.viridis(np.linspace(0.2, 0.9, len(categories)))
                    bars = ax2.barh(range(len(categories)), counts, color=colors)
                    ax2.set_yticks(range(len(categories)))
                    ax2.set_yticklabels(categories, fontsize=10)
                    ax2.set_xlabel('Number of Files', fontsize=11, weight='bold')
                    ax2.set_title('File Size Distribution', fontsize=14, weight='bold', pad=20)
                    ax2.grid(axis='x', alpha=0.3, linestyle='--')
                    
                    for bar, count in zip(bars, counts):
                        width = bar.get_width()
                        ax2.text(width + max(counts)*0.01, bar.get_y() + bar.get_height()/2, 
                                f'{count:,}', ha='left', va='center', fontsize=9, weight='bold')
            
            ax3 = fig.add_subplot(gs[0, 2])
            age_dist = dict(self.stats['age_distribution'])
            if age_dist:
                categories = list(age_dist.keys())
                counts = list(age_dist.values())
                if counts and sum(counts) > 0:
                    colors = ['#2ecc71', '#f1c40f', '#e67e22', '#e74c3c', '#95a5a6']
                    wedges, texts, autotexts = ax3.pie(counts, autopct='%1.1f%%', 
                                                       startangle=90, colors=colors[:len(categories)],
                                                       wedgeprops={'edgecolor': 'white', 'linewidth': 2},
                                                       textprops={'fontsize': 10, 'weight': 'bold'})
                    for autotext in autotexts:
                        autotext.set_color('white')
                        autotext.set_weight('bold')
                    ax3.set_title('File Age Distribution', fontsize=14, weight='bold', pad=20)
                    ax3.legend(wedges, categories, title="Age", loc="center left", 
                              bbox_to_anchor=(1, 0, 0.5, 1), fontsize=9)
            
            ax4 = fig.add_subplot(gs[1, :2])
            if self.stats['largest_dirs']:
                dir_data = self.stats['largest_dirs'][:8]
                dir_names = [os.path.basename(d[2])[:20] for d in dir_data]
                dir_sizes = [d[0] / (1024*1024*1024) for d in dir_data]
                if dir_sizes and any(dir_sizes):
                    colors = plt.cm.plasma_r(np.linspace(0.2, 0.9, len(dir_names)))
                    bars = ax4.barh(range(len(dir_names)), dir_sizes, color=colors)
                    ax4.set_yticks(range(len(dir_names)))
                    ax4.set_yticklabels(dir_names, fontsize=10)
                    ax4.set_xlabel('Size (GB)', fontsize=11, weight='bold')
                    ax4.set_title('Largest Directories', fontsize=14, weight='bold', pad=20)
                    ax4.grid(axis='x', alpha=0.3, linestyle='--')
                    
                    for bar, size in zip(bars, dir_sizes):
                        width = bar.get_width()
                        ax4.text(width + max(dir_sizes)*0.01, bar.get_y() + bar.get_height()/2, 
                                f'{size:.2f} GB', ha='left', va='center', fontsize=9, weight='bold')
            
            ax5 = fig.add_subplot(gs[1, 2])
            if self.stats['owners']:
                owners_data = sorted(
                    self.stats['owners'].items(),
                    key=lambda x: x[1],
                    reverse=True
                )[:6]
                if owners_data:
                    labels = [o[0][:15] for o in owners_data]
                    sizes = [o[1] for o in owners_data]
                    colors = plt.cm.Pastel1(np.linspace(0, 1, len(labels)))
                    wedges, texts, autotexts = ax5.pie(sizes, labels=labels, autopct='%1.1f%%',
                                                       colors=colors, wedgeprops={'edgecolor': 'white', 'linewidth': 2},
                                                       textprops={'fontsize': 9})
                    for autotext in autotexts:
                        autotext.set_color('black')
                        autotext.set_weight('bold')
                    ax5.set_title('Top Owners', fontsize=14, weight='bold', pad=20)
            
            ax6 = fig.add_subplot(gs[2, :])
            if self.stats['largest_files']:
                file_data = self.stats['largest_files'][:10]
                file_names = [os.path.basename(f[1])[:25] for f in file_data]
                file_sizes = [f[0] / (1024*1024) for f in file_data]
                if file_sizes and any(file_sizes):
                    x_pos = np.arange(len(file_names))
                    colors = plt.cm.coolwarm(np.linspace(0.2, 0.9, len(file_names)))
                    bars = ax6.bar(x_pos, file_sizes, color=colors, edgecolor='white', linewidth=2)
                    ax6.set_xticks(x_pos)
                    ax6.set_xticklabels(file_names, rotation=45, ha='right', fontsize=9)
                    ax6.set_ylabel('Size (MB)', fontsize=11, weight='bold')
                    ax6.set_xlabel('File Name', fontsize=11, weight='bold')
                    ax6.set_title('Top 10 Largest Files', fontsize=14, weight='bold', pad=20)
                    ax6.grid(axis='y', alpha=0.3, linestyle='--')
                    
                    for bar, size in zip(bars, file_sizes):
                        height = bar.get_height()
                        ax6.text(bar.get_x() + bar.get_width()/2., height + max(file_sizes)*0.01,
                                f'{size:.1f}', ha='center', va='bottom', fontsize=8, weight='bold')
            
            summary_text = f"Inode Analysis Report\nGenerated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
            summary_text += f"Total Files: {self.get_human_readable(self.stats['total_files'], False)} | "
            summary_text += f"Total Size: {self.get_human_readable(self.total_size)} | "
            summary_text += f"Total Inodes: {self.get_human_readable(total_inodes, False)}"
            
            fig.text(0.5, 0.98, summary_text, ha='center', fontsize=12, 
                    bbox={'facecolor': '#2c3e50', 'alpha': 0.8, 'pad': 10, 'edgecolor': 'none'},
                    color='white', weight='bold')
            
            plt.tight_layout()
            plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor=fig.get_facecolor())
            
            if RICH_AVAILABLE:
                console.print(f"[green]✓ Visualization saved to: {output_file}[/green]")
            else:
                print(f"\nVisualization saved to: {output_file}")
            
            if os.environ.get('DISPLAY') or sys.platform.startswith('darwin'):
                plt.show()
            else:
                plt.close()
                
        except Exception as e:
            if RICH_AVAILABLE:
                console.print(f"[red]✗ Error generating visualization: {e}[/red]")
            else:
                print(f"Error generating visualization: {e}")


def main():
    parser = argparse.ArgumentParser(
        description='Advanced inode usage analysis tool with deep scanning and visualization capabilities',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s /home/user              Quick scan of home directory
  %(prog)s /var --deep --duplicates Deep scan with duplicate detection
  %(prog)s / --deep --threads 8    Deep scan of root with 8 threads
  %(prog)s . --json report.json    Export results to JSON
  %(prog)s . --plot analysis.png   Generate visualization
  %(prog)s . --exclude "*.tmp" --exclude "*.cache"  Exclude patterns
  %(prog)s . --max-depth 3         Limit scan depth
        """
    )
    
    parser.add_argument('path', nargs='?', default='.',
                       help='Directory to analyze (default: current directory)')
    
    parser.add_argument('--samples', type=int, default=20,
                       help='Number of samples for largest files/dirs (default: 20)')
    
    parser.add_argument('--deep', action='store_true',
                       help='Perform deep scan with detailed metadata analysis')
    
    parser.add_argument('--duplicates', action='store_true',
                       help='Find duplicate files (automatically enabled with --deep)')
    
    parser.add_argument('--threads', type=int, default=4,
                       help='Number of threads for deep scan (default: 4)')
    
    parser.add_argument('--json', metavar='FILE',
                       help='Export report to JSON file')
    
    parser.add_argument('--plot', metavar='FILE',
                       help='Generate visualization plot (requires matplotlib)')
    
    parser.add_argument('--age', type=int, metavar='DAYS',
                       help='Only analyze files accessed/modified within N days')
    
    parser.add_argument('--symlinks', action='store_true',
                       help='Follow symbolic links (use with caution)')
    
    parser.add_argument('--exclude', action='append', metavar='PATTERN',
                       help='Exclude files/directories matching pattern (can be used multiple times)')
    
    parser.add_argument('--max-depth', type=int, metavar='N',
                       help='Maximum directory depth to scan')
    
    parser.add_argument('--save-state', metavar='FILE',
                       help='Save scan state to resume later')
    
    parser.add_argument('--load-state', metavar='FILE',
                       help='Resume scan from saved state')
    
    parser.add_argument('--no-rich', action='store_true',
                       help='Disable rich output (fallback to plain text)')
    
    parser.add_argument('--quiet', action='store_true',
                       help='Suppress non-error output')
    
    parser.add_argument('--version', action='version',
                       version='Inode Analyzer v2.0')
    
    args = parser.parse_args()
    
    if args.no_rich:
        global RICH_AVAILABLE
        RICH_AVAILABLE = False
    
    if args.deep and args.duplicates is False:
        args.duplicates = True
    
    if not RICH_AVAILABLE and not args.no_rich and not args.quiet:
        print("Note: Install 'rich' for enhanced visualization: pip install rich", file=sys.stderr)
    
    if not HUMANIZE_AVAILABLE and not args.quiet:
        print("Note: Install 'humanize' for better number formatting: pip install humanize", file=sys.stderr)
    
    if args.duplicates and not HASH_FAST_AVAILABLE and not args.quiet:
        print("Note: Install 'xxhash' for faster duplicate detection: pip install xxhash", file=sys.stderr)
    
    if args.plot and not PLOT_AVAILABLE and not args.quiet:
        print("Note: Install 'matplotlib' for visualization: pip install matplotlib", file=sys.stderr)
    
    analyzer = InodeAnalyzer(
        threads=args.threads,
        follow_symlinks=args.symlinks,
        exclude_patterns=args.exclude or []
    )
    
    analyzer.analyze_directory(
        path=args.path,
        sample_size=args.samples,
        deep_scan=args.deep,
        find_duplicates=args.duplicates,
        export_json=args.json,
        generate_plot=args.plot,
        age_days=args.age,
        save_state=args.save_state,
        load_state=args.load_state,
        max_depth=args.max_depth
    )


if __name__ == "__main__":
    main()
