from pathlib import Path

# File paths
results_file_path = Path("examples/sw/simple_system/hello_test/test_results.txt")
log_file_path = Path("./ibex_multicore_system.log")
pass_file_path = Path("examples/sw/simple_system/hello_test/test_pass.txt")

# Helper function to read integers from a file
def read_integers(file_path):
    integers = []
    with open(file_path, "r") as file:
        for line in file:
            line = line.strip()
            if line:  # skip empty lines
                integers.append(int(line))
    return integers

# Read both files
try:
    results_array = read_integers(results_file_path)
    log_array = read_integers(log_file_path)
except Exception as e:
    print(f"Error reading files: {e}")
    exit(1)

# Compare arrays
status = "PASSED" if results_array == log_array else "FAILED"

# Append the result to the pass file
try:
    with open(pass_file_path, "a") as f:
        f.write(status + "\n")
        if status == "FAILED":
            f.write("results_array: " + str(results_array) + "\n")
            f.write("log_array: " + str(log_array) + "\n")
    print(f"Test {status}")
except Exception as e:
    print(f"Error writing to pass file: {e}")
    exit(1)
