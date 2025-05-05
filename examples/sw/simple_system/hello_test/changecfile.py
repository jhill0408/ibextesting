import os

# Path to the file
file_path = "examples/sw/simple_system/hello_test/hello_test.c"

# Check if file exists
if not os.path.isfile(file_path):
    print(f"Error: File '{file_path}' not found.")
    exit(1)

# Read the file
with open(file_path, "r") as file:
    lines = file.readlines()

# Modify the target line
new_lines = []
replaced = False
for line in lines:
    if "while (count < 500)" in line:
        new_line = line.replace("while (count < 500)", "while (count < 501)")
        new_lines.append(new_line)
        replaced = True
    elif "while (count < 501)" in line:
        new_line = line.replace("while (count < 501)", "while (count < 500)")
        new_lines.append(new_line)
        replaced = True
    else:
        new_lines.append(line)

if not replaced:
    print("Warning: No matching line found to replace.")
else:
    # Write back the modified file
    with open(file_path, "w") as file:
        file.writelines(new_lines)
    print("Replacement complete.")

