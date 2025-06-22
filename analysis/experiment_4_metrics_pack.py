import os

# --- CONFIGURATION ---
# A list of all folders to scan and analyze. Each is processed independently.
folders_to_scan = [
    './greedy_pack',
    './knapsack_pack',
    './shift_pack',
]

# The delimiter to search for in files.
DELIMITER = '----------'

# --- SCRIPT LOGIC ---

def extract_move_stats(file_path):
    """
    In a single file, finds the *last* delimiter, parses the line at i-5,
    and calculates stats. All numbers for the division are taken from that line.
    """
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()

        # 1. Find the index of the LAST delimiter in the file.
        last_delimiter_index = -1
        for i, line in enumerate(lines):
            if DELIMITER in line:
                last_delimiter_index = i

        # 2. Proceed only if a delimiter was found and there's enough space before it.
        if last_delimiter_index != -1 and last_delimiter_index >= 5:
            # 3. Get the target line (i-5).
            target_line = lines[last_delimiter_index - 5]

            # 4. Split by '-' and get the part after the second one.
            parts = target_line.split('-')
            if len(parts) < 3: return None
            
            # 5. Split the result by ',' to get the numbers.
            num_str_list = parts[2].strip().split(',')
            if len(num_str_list) < 6: return None

            nums = [float(n) for n in num_str_list]
            denominator = nums[4]
            if denominator == 0: return None

            # 6. Perform calculations and return the stats dictionary.
            stats = {
                'no_energy': nums[0] / denominator,
                'no_removel': nums[1] / denominator,
                'no_change': nums[2] / denominator,
                'avg_overload': nums[5] / denominator
            }
            return stats
            
        return None # Return None if no delimiter was found or not enough lines.
    except (IOError, IndexError, ValueError, ZeroDivisionError):
        return None # Return None on any parsing or calculation error.

def analyze_folder(folder_path):
    """Scans a single folder, extracts move stats, and calculates its summary statistics."""
    if not os.path.isdir(folder_path):
        print(f"  WARNING: Folder not found, skipping: {folder_path}")
        return None

    folder_results = {}
    # Lists for move stat averages
    no_energy_list, no_removel_list, no_change_list, avg_overload_list = [], [], [], []

    for filename in sorted(os.listdir(folder_path)):
        file_path = os.path.join(folder_path, filename)
        if not os.path.isfile(file_path): continue

        move_stats = extract_move_stats(file_path)

        if move_stats:
            folder_results[filename] = move_stats
            no_energy_list.append(move_stats['no_energy'])
            no_removel_list.append(move_stats['no_removel'])
            no_change_list.append(move_stats['no_change'])
            avg_overload_list.append(move_stats['avg_overload'])

    # --- SUMMARY CALCULATION ---
    folder_results['_summary'] = {
        'files_in_average': len(no_energy_list),
        'avg_no_energy': sum(no_energy_list) / len(no_energy_list) if no_energy_list else 0.0,
        'avg_no_removel': sum(no_removel_list) / len(no_removel_list) if no_removel_list else 0.0,
        'avg_no_change': sum(no_change_list) / len(no_change_list) if no_change_list else 0.0,
        'avg_avg_overload': sum(avg_overload_list) / len(avg_overload_list) if avg_overload_list else 0.0,
    }
    return folder_results

def print_results(results):
    """Prints all extracted data and calculated stats in a readable format."""
    print("\n" + "="*40 + "\n--- FINAL RESULTS ---\n" + "="*40)
    for folder, data in results.items():
        print(f"\n--- Results for Folder: {folder} ---")
        summary = data.pop('_summary')
        if not data:
            print("  No files with the required data were found in this folder.")
        
        print("\n  Folder Summary:")
        if summary['files_in_average'] > 0:
            print(f"    - Average no_energy:    {summary['avg_no_energy']:.4f}")
            print(f"    - Average no_removel:   {summary['avg_no_removel']:.4f}")
            print(f"    - Average no_change:    {summary['avg_no_change']:.4f}")
            print(f"    - Average avg_overload: {summary['avg_avg_overload']:.4f}")
            print(f"    - (Stats calculated over {summary['files_in_average']} files)")
        else:
            print("    - No numeric data found to calculate averages.")

# --- EXECUTION ---
if __name__ == "__main__":
    all_folder_data = {}
    print("--- Starting Analysis of All Specified Folders ---")

    for folder_path in folders_to_scan:
        print(f"\n--- Analyzing Folder: {folder_path} ---")
        folder_data = analyze_folder(folder_path)
        if folder_data:
            all_folder_data[folder_path] = folder_data

    print_results(all_folder_data)