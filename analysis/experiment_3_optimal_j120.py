import os

# --- CONFIGURATION ---
# The folder containing the "correct" or "golden" versions of the files.
baseline_folder = './naive_yes_j120'

# A list of other folders to check against the baseline.
# The baseline folder is included here for a sanity check.
folders_to_check = [
    './naive_yes_j120',
    './shift_j120',
    './greedy_j120',
    './knapsack_j120'
]

# The string to find to determine the anchor line.
OBJECTIVE_STRING = '%%%mzn-stat: objective'

# The metrics to extract, with their line offset from the anchor line.
METRICS_CONFIG = {
    'conflicts': 2,
    'runtime': 5,
    'backtrack': 11,
    'lbd': 12,
}

# --- SCRIPT LOGIC ---

def extract_metrics(file_path, expected_anchor_line=None):
    """
    Finds an anchor line and extracts metrics relative to it.
    If expected_anchor_line is None (baseline run), it finds the last objective line.
    If provided (comparison run), it searches for that exact line.
    Returns (metric_values, found_anchor_line).
    """
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()

        # 1. Find the anchor (objective) line's index and content.
        anchor_index = -1
        anchor_line_content = None
        if expected_anchor_line:
            try:
                # For comparison runs, find the exact line provided from the baseline.
                anchor_index = lines.index(expected_anchor_line)
            except ValueError:
                return None, None # The expected anchor was not found in this file.
        else:
            # For baseline runs, find the LAST occurrence of the objective string.
            for i, line in enumerate(lines):
                if OBJECTIVE_STRING in line:
                    anchor_index = i
                    anchor_line_content = line
        
        if anchor_index == -1:
            return None, None # No anchor could be established for this file.

        # 2. Extract metrics using offsets from the found anchor index.
        max_offset = max(METRICS_CONFIG.values())
        if anchor_index + max_offset < len(lines):
            raw_values = {}
            for name, offset in METRICS_CONFIG.items():
                value_line = lines[anchor_index + offset]
                if '=' in value_line:
                    raw_values[name] = value_line.split('=', 1)[1].strip()
                else:
                    raw_values[name] = None
            return raw_values, anchor_line_content
        else:
            return None, None # File is too short after the anchor line.
            
    except (IOError, IndexError):
        return None, None

def process_folder(folder_path, baseline_data=None):
    """
    Scans a folder, extracts metrics using dynamic anchors, and calculates ratios.
    """
    if not os.path.isdir(folder_path):
        print(f"\nWARNING: Folder not found, skipping: {folder_path}")
        return None

    folder_results = {}
    ratio_lists = {name: [] for name in METRICS_CONFIG.keys()}
    filenames_to_check = baseline_data.keys() if baseline_data else os.listdir(folder_path)

    for filename in sorted(filenames_to_check):
        if baseline_data and filename not in baseline_data:
            continue

        file_path = os.path.join(folder_path, filename)
        if not os.path.isfile(file_path): continue

        expected_anchor = baseline_data[filename].get('anchor_line') if baseline_data else None
        current_metrics, found_anchor_line = extract_metrics(file_path, expected_anchor)
        
        if not current_metrics:
            continue

        if baseline_data:
            baseline_metrics = baseline_data.get(filename)
            if not baseline_metrics: continue

            file_ratios = {}
            for name in METRICS_CONFIG.keys():
                try:
                    current_val = float(current_metrics[name])
                    baseline_val = float(baseline_metrics[name])
                    ratio = 1.0 if baseline_val == 0 else current_val / baseline_val
                    file_ratios[name] = ratio
                    ratio_lists[name].append(ratio)
                except (ValueError, TypeError):
                    file_ratios[name] = None
            folder_results[filename] = file_ratios
        else:
            current_metrics['anchor_line'] = found_anchor_line
            folder_results[filename] = current_metrics

    summary = {}
    if baseline_data:
        for name, lst in ratio_lists.items():
            summary[f'avg_{name}'] = sum(lst) / len(lst) if lst else 0.0
        summary['files_in_average'] = len(next(iter(ratio_lists.values()), []))
    folder_results['_summary'] = summary
    
    return folder_results

def print_results(results):
    """Prints the calculated summary stats for each folder."""
    print("\n" + "="*40 + "\n--- FINAL RESULTS ---\n" + "="*40)
    for folder, data in results.items():
        print(f"\n--- Results for Folder: {folder} ---")
        summary = data.pop('_summary')
        if not data and not summary:
            print("  No valid data could be processed for this folder.")
            continue
        
        if summary:
            print("\n  Folder Summary (Ratios vs Baseline):")
            if summary.get('files_in_average', 0) > 0:
                for name in METRICS_CONFIG.keys():
                    avg_key = f'avg_{name}'
                    if avg_key in summary:
                        print(f"    - Average {name}_ratio: {summary[avg_key]:.4f}")
                print(f"    - (Stats calculated over {summary['files_in_average']} files)")
            else:
                print("    - No numeric data found to calculate averages.")
        else:
             print("  (This is the initial baseline processing run)")

# --- EXECUTION ---
if __name__ == "__main__":
    print(f"--- Processing Baseline Folder: {baseline_folder} ---")
    baseline_data_full = process_folder(baseline_folder)

    if not baseline_data_full or len(baseline_data_full) <= 1:
        print(f"CRITICAL ERROR: Baseline folder '{baseline_folder}' could not be processed or was empty.")
    else:
        baseline_files_data = {k: v for k, v in baseline_data_full.items() if k != '_summary'}
        print(f"Found {len(baseline_files_data)} valid files in baseline to use for comparison.")

        # The results dictionary will now hold all processed folders, including the baseline's initial run.
        all_results = {f"{baseline_folder} (Baseline)": baseline_data_full}

        print("\n--- Processing Comparison Folders ---")
        for folder in folders_to_check:
            print(f"\n--- Analyzing: {folder} ---")
            filtered_data = process_folder(folder, baseline_data=baseline_files_data)
            if filtered_data:
                all_results[folder] = filtered_data
        
        print_results(all_results)