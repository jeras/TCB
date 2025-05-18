#!/usr/bin/env python3

import subprocess
import pprint

tests = [
  "tcb_lib_logsize2byteena_tb",
  "tcb_lib_misaligned_memory_controller_tb"
]

report = []

# run tests
for top in tests:
    status = subprocess.run(f"TOP={top} make -C questa/ check", shell=True)
    report.append([top, status.returncode])

# print report
print("==== REPORT ====")
for test in report:
    print(test)
