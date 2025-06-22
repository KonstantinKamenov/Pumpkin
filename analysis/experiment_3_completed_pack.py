import os

# --- CONFIGURATION ---
# The folder containing the "correct" or "golden" versions of the files.
baseline_folder = './naive_yes_pack'

# A list of other folders to check against the baseline.
folders_to_check = [
    './naive_yes_pack',
    './shift_pack',
    './greedy_pack',
    './knapsack_pack',
]

# The delimiter to search for in files.
DELIMITER = '=========='

# The metrics to extract, with their line offset from the delimiter.
METRICS_CONFIG = {
    'conflicts': 2,
    'runtime': 5,
    'backtrack': 11,
    'lbd': 12,
}

# --- SCRIPT LOGIC ---

def extract_metrics(file_path):
    """
    Finds the first delimiter and extracts the raw string values for all configured metrics.
    """
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()

        max_offset = max(METRICS_CONFIG.values())

        for i, line in enumerate(lines):
            if DELIMITER in line:
                # Ensure there are enough lines after the delimiter for all metrics.
                if i + max_offset < len(lines):
                    raw_values = {}
                    for name, offset in METRICS_CONFIG.items():
                        value_line = lines[i + offset]
                        print(value_line)
                        # Extract value after the '=' sign.
                        if '=' in value_line:
                            raw_values[name] = value_line.split('=', 1)[1].strip()
                        else:
                            raw_values[name] = None # Metric line found, but no '='
                    return raw_values
                else:
                    return None # Delimiter found, but file is too short.
        return None # Delimiter not found in the file.
    except (IOError, IndexError):
        return None

def process_folder(folder_path, baseline_data=None):
    """
    Scans a folder, extracts metrics, and calculates ratios against a baseline if provided.
    """
    if not os.path.isdir(folder_path):
        print(f"\nWARNING: Folder not found, skipping: {folder_path}")
        return None

    folder_results = {}
    # A dictionary to hold lists of ratios for averaging.
    ratio_lists = {name: [] for name in METRICS_CONFIG.keys()}

    filenames_to_check = baseline_data.keys() if baseline_data else os.listdir(folder_path)

    for filename in sorted(filenames_to_check):
        if baseline_data and filename not in baseline_data:
            continue

        file_path = os.path.join(folder_path, filename)
        if not os.path.isfile(file_path):
            continue

        current_metrics = extract_metrics(file_path)
        if not current_metrics:
            continue

        # If this is a comparison run, calculate ratios.
        if baseline_data:
            baseline_metrics = baseline_data.get(filename)
            if not baseline_metrics: continue # Baseline file had no valid data.

            file_ratios = {}
            for name in METRICS_CONFIG.keys():
                try:
                    current_val = float(current_metrics[name])
                    baseline_val = float(baseline_metrics[name])

                    # Calculate ratio with the special rule for baseline_val == 0.
                    if baseline_val == 0:
                        ratio = 1.0
                    else:
                        ratio = current_val / baseline_val
                    
                    file_ratios[name] = ratio
                    ratio_lists[name].append(ratio)
                except (ValueError, TypeError):
                    # Handle cases where values are not numbers or are None.
                    file_ratios[name] = None
            
            folder_results[filename] = file_ratios
        else:
            # For the baseline run, just store the raw extracted values.
            folder_results[filename] = current_metrics

    # --- SUMMARY CALCULATION ---
    summary = {}
    if baseline_data: # Averages only make sense for comparison folders.
        for name, lst in ratio_lists.items():
            summary[f'avg_{name}'] = sum(lst) / len(lst) if lst else 0.0
        summary['files_in_average'] = len(next(iter(ratio_lists.values()), []))
    folder_results['_summary'] = summary
    
    return folder_results

def print_results(results):
    """Prints all extracted data and calculated stats in a readable format."""
    print("\n" + "="*40 + "\n--- FINAL RESULTS ---\n" + "="*40)
    for folder, data in results.items():
        print(f"\n--- Results for Folder: {folder} ---")
        summary = data.pop('_summary')
        if not data:
            print("  No matching files with the required data were found in this folder.")

        if summary: # Only print summary for comparison folders.
            print("\n  Folder Summary (Ratios vs Baseline):")
            if summary['files_in_average'] > 0:
                for name in METRICS_CONFIG.keys():
                    print(f"    - Average {name}_ratio: {summary[f'avg_{name}']:.4f}")
                print(f"    - (Stats calculated over {summary['files_in_average']} files)")
            else:
                print("    - No numeric data found to calculate averages.")

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
            filtered_data = process_folder(folder, baseline_data=baseline_files_data)
            if filtered_data:
                all_results[folder] = filtered_data
        
        print_results(all_results)