import os
from collections import defaultdict

# --- CONFIGURATION ---
baseline_folder = './decomp_j60'
folders_to_check = [
    './knapsack_j60', './naive_no_j60', './naive_yes_j60',
    './shift_j60', './greedy_j60', './decomp_j60'
]
DELIMITER = '=========='
SOLVER_TIME_STRING = 'engineStatisticsTimeSpentInSolver'

# --- SCRIPT LOGIC ---

def file_contains_delimiter(file_path):
    """Checks if a file contains the global DELIMITER string."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            return DELIMITER in f.read()
    except IOError:
        return False

def find_common_valid_files(all_folders):
    """
    Scans all folders to find a common set of files that all contain the delimiter.
    """
    if not all_folders:
        return set(), {}

    # 1. Find the intersection of filenames that exist in ALL folders.
    try:
        # Start with the set of files from the first folder.
        common_filenames = set(os.listdir(all_folders[0]))
        # Find the intersection with all other folders.
        for folder in all_folders[1:]:
            if os.path.isdir(folder):
                common_filenames.intersection_update(os.listdir(folder))
            else:
                return set(), {"Error": f"Folder not found: {folder}"} # Critical error if a folder is missing.
    except (IOError, IndexError):
        return set(), {"Error": "Could not read files from initial folders."}

    # 2. From this common set, check that the delimiter exists in every copy of the file.
    valid_files = set()
    excluded_files = defaultdict(list)
    for filename in sorted(list(common_filenames)):
        is_valid_everywhere = True
        for folder in all_folders:
            file_path = os.path.join(folder, filename)
            if not os.path.isfile(file_path) or not file_contains_delimiter(file_path):
                is_valid_everywhere = False
                excluded_files[filename].append(f"Delimiter missing or not a file in '{folder}'")
        
        if is_valid_everywhere:
            valid_files.add(filename)

    return valid_files, excluded_files


def extract_solver_times(file_path):
    """Finds the last two solver time lines and extracts their values."""
    filename = os.path.basename(file_path)
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f: lines = f.readlines()
        solver_line_indices = [i for i, line in enumerate(lines) if SOLVER_TIME_STRING in line]
        if len(solver_line_indices) < 2: return None, None
        
        line_optimal_raw, line_proven_raw = lines[solver_line_indices[-2]], lines[solver_line_indices[-1]]
        val_optimal = line_optimal_raw.split('=', 1)[1].strip() if '=' in line_optimal_raw else None
        val_proven = line_proven_raw.split('=', 1)[1].strip() if '=' in line_proven_raw else None
        
        if val_optimal is None or val_proven is None: return None, None
        if float(val_optimal) == 0 or float(val_proven) == 0:
            print(f"  [FLAG] Skipping {filename}: Found a zero value for solver time.")
            return None, None
        return val_optimal, val_proven
    except (IOError, IndexError, ValueError):
        return None, None

def process_folder(folder_path, filenames_to_process, baseline_data=None):
    """Scans a folder for a pre-defined list of files, extracts data, and calculates stats."""
    folder_results = {}
    optimal_times, proven_times, optimal_gains, proven_gains = [], [], [], []

    for filename in sorted(list(filenames_to_process)):
        file_path = os.path.join(folder_path, filename)
        time_optimal_str, time_proven_str = extract_solver_times(file_path)

        if time_optimal_str is not None and time_proven_str is not None:
            file_data = {'time_optimal': time_optimal_str, 'time_proven': time_proven_str}
            if baseline_data:
                try:
                    current_optimal, current_proven = float(time_optimal_str), float(time_proven_str)
                    baseline_optimal = float(baseline_data[filename]['time_optimal'])
                    baseline_proven = float(baseline_data[filename]['time_proven'])
                    opt_gain = 1.0 if baseline_optimal == 0 else current_optimal / baseline_optimal
                    prov_gain = 1.0 if baseline_proven == 0 else current_proven / baseline_proven
                    file_data.update({'time_optimal_gain': opt_gain, 'time_proven_gain': prov_gain})
                    optimal_gains.append(opt_gain)
                    proven_gains.append(prov_gain)
                except (ValueError, KeyError):
                    file_data.update({'time_optimal_gain': None, 'time_proven_gain': None})
            folder_results[filename] = file_data
            try:
                optimal_times.append(float(time_optimal_str))
                proven_times.append(float(time_proven_str))
            except ValueError: pass
    
    folder_results['_summary'] = {
        'avg_time_optimal': sum(optimal_times)/len(optimal_times) if optimal_times else 0.0,
        'avg_time_proven': sum(proven_times)/len(proven_times) if proven_times else 0.0,
        'files_in_average': len(optimal_times),
        'avg_time_optimal_gain': sum(optimal_gains)/len(optimal_gains) if optimal_gains else 0.0,
        'avg_time_proven_gain': sum(proven_gains)/len(proven_gains) if proven_gains else 0.0,
    }
    return folder_results

def print_results(results):
    """Prints the calculated summary stats for each folder."""
    print("\n" + "="*40 + "\n--- FINAL RESULTS ---\n" + "="*40)
    for folder, data in results.items():
        print(f"\n--- Results for Folder: {folder} ---")
        summary = data.pop('_summary')
        print("\n  Folder Summary:")
        if summary['files_in_average'] > 0:
            print(f"    - Average time_optimal: {summary['avg_time_optimal']:.4f}")
            print(f"    - Average time_proven:  {summary['avg_time_proven']:.4f}")
            if summary.get('avg_time_optimal_gain'): print(f"    - Average time_optimal_gain: {summary['avg_time_optimal_gain']:.4f}")
            if summary.get('avg_time_proven_gain'): print(f"    - Average time_proven_gain:  {summary['avg_time_proven_gain']:.4f}")
            print(f"    - (Stats calculated over {summary['files_in_average']} files)")
        else:
            print("    - No valid data found to calculate averages.")

# --- EXECUTION ---
if __name__ == "__main__":
    all_folders_to_scan = list(set([baseline_folder] + folders_to_check))
    print("--- Phase 1: Finding common set of valid files across all folders ---")
    valid_filenames, excluded_files = find_common_valid_files(all_folders_to_scan)

    if excluded_files.get("Error"):
        print(f"CRITICAL ERROR during pre-scan: {excluded_files['Error']}")
    elif not valid_filenames:
        print("CRITICAL ERROR: No common set of valid files found. Analysis cannot continue.")
    else:
        print(f"\nFound {len(valid_filenames)} files that are valid across all folders.")
        print("These files will be used for analysis.")
        for fname in sorted(list(valid_filenames)):
            print(f"  - {fname}")

        if excluded_files:
            print(f"\nExcluded {len(excluded_files)} files:")
            for fname, reasons in excluded_files.items():
                print(f"  - {fname} (Reason: {reasons[0]})")
        
        print("\n--- Phase 2: Processing data for the valid set of files ---")
        
        # Process baseline folder first
        print(f"\n--- Analyzing Baseline: {baseline_folder} ---")
        baseline_data_full = process_folder(baseline_folder, valid_filenames)
        baseline_files_data = {k: v for k, v in baseline_data_full.items() if k != '_summary'}
        
        all_results = {baseline_folder: baseline_data_full}

        # Process comparison folders
        print("\n--- Analyzing Comparison Folders ---")
        for folder in folders_to_check:
            print(f"\n--- Analyzing: {folder} ---")
            filtered_data = process_folder(folder, valid_filenames, baseline_data=baseline_files_data)
            if filtered_data: all_results[folder] = filtered_data

        print_results(all_results)