import os

# --- CONFIGURATION ---
baseline_folder = './decomp_bl'
folders_to_check = [
    './knapsack_bl', './naive_no_bl', './naive_yes_bl',
    './shift_bl', './greedy_bl', './decomp_bl'
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

def extract_solver_times(file_path):
    """
    Finds the last two solver time lines and extracts their values.
    Assumes the delimiter has already been verified to exist in the file.
    """
    filename = os.path.basename(file_path)
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        solver_line_indices = [i for i, line in enumerate(lines) if SOLVER_TIME_STRING in line]

        if len(solver_line_indices) < 2: return None, None
        
        line_optimal_raw = lines[solver_line_indices[-2]]
        line_proven_raw = lines[solver_line_indices[-1]]
        val_optimal = line_optimal_raw.split('=', 1)[1].strip() if '=' in line_optimal_raw else None
        val_proven = line_proven_raw.split('=', 1)[1].strip() if '=' in line_proven_raw else None
        
        if val_optimal is None or val_proven is None: return None, None
        
        if float(val_optimal) == 0 or float(val_proven) == 0:
            print(f"  [FLAG] Skipping {filename}: Found a zero value for solver time.")
            return None, None
        
        return val_optimal, val_proven
    except (IOError, IndexError, ValueError):
        return None, None

def process_folder(folder_path, baseline_data=None):
    """
    Scans a folder, extracts data, and tracks skipped files.
    """
    if not os.path.isdir(folder_path):
        print(f"\nWARNING: Folder not found, skipping: {folder_path}")
        return None

    folder_results = {}
    skipped_no_delimiter = [] # NEW: List to track skipped files.
    optimal_times, proven_times, optimal_gains, proven_gains = [], [], [], []

    filenames_to_check = baseline_data.keys() if baseline_data else os.listdir(folder_path)

    for filename in sorted(filenames_to_check):
        if baseline_data and filename not in baseline_data: continue
        file_path = os.path.join(folder_path, filename)
        if not os.path.isfile(file_path): continue

        # NEW: Check for delimiter first.
        if not file_contains_delimiter(file_path):
            skipped_no_delimiter.append(filename)
            continue # Skip to the next file.

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
        'skipped_no_delimiter': skipped_no_delimiter # NEW: Add the list to the summary.
    }
    return folder_results

def print_results(results):
    """Prints the calculated summary stats and skipped file info for each folder."""
    print("\n" + "="*40 + "\n--- FINAL RESULTS ---\n" + "="*40)
    for folder, data in results.items():
        print(f"\n--- Results for Folder: {folder} ---")
        summary = data.pop('_summary')
        skipped_list = summary.pop('skipped_no_delimiter', []) # Safely get the skipped list.

        print("\n  Folder Summary:")
        if summary['files_in_average'] > 0:
            print(f"    - Average time_optimal: {summary['avg_time_optimal']:.4f}")
            print(f"    - Average time_proven:  {summary['avg_time_proven']:.4f}")
            if summary['avg_time_optimal_gain']: print(f"    - Average time_optimal_gain: {summary['avg_time_optimal_gain']:.4f}")
            if summary['avg_time_proven_gain']: print(f"    - Average time_proven_gain:  {summary['avg_time_proven_gain']:.4f}")
            print(f"    - (Stats calculated over {summary['files_in_average']} files)")
        else:
            print("    - No valid data found to calculate averages.")

        # NEW: Print the list of files that were skipped.
        if skipped_list:
            print(f"\n  Skipped Files (No Delimiter '{DELIMITER}' Found): {len(skipped_list)}")
            for fname in skipped_list:
                print(f"    - {fname}")

# --- EXECUTION ---
if __name__ == "__main__":
    print(f"--- Processing Baseline Folder: {baseline_folder} ---")
    baseline_data_full = process_folder(baseline_folder)
    if not baseline_data_full or len(baseline_data_full) <= 1:
        print(f"CRITICAL ERROR: Baseline folder '{baseline_folder}' could not be processed or was empty.")
    else:
        baseline_files_data = {k: v for k, v in baseline_data_full.items() if k != '_summary'}
        print(f"Found {len(baseline_files_data)} valid files in baseline to use for comparison.")
        all_results = {baseline_folder: baseline_data_full}
        print("\n--- Processing Comparison Folders ---")
        for folder in folders_to_check:
            print(f"\n--- Analyzing: {folder} ---")
            filtered_data = process_folder(folder, baseline_data=baseline_files_data)
            if filtered_data: all_results[folder] = filtered_data
        print_results(all_results)