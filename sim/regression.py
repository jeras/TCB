#!/usr/bin/env python3

import subprocess
import pprint
import re

tests = [
#  "tcb_vip_tb",
#  "tcb_lib_passthrough_tb",
#  "tcb_lib_register_request_tb",
#  "tcb_lib_register_response_tb",
#  "tcb_lib_register_backpressure_tb",
#  "tcb_lib_demultiplexer_tb",
#  "tcb_lib_multiplexer_tb",
  "tcb_lib_logsize2byteena_tb",
#  "tcb_lib_misaligned_memory_controller_tb",
#  "tcb_lib_read_modify_write_tb",
#  "tcb_peri_gpio_tb",
#  "tcb_peri_uart_tb",
]

simulator = "questa"
#simulator = "vivado"
#simulator = "verilator"

report = []

# run tests
for top in tests:
    if (simulator == "questa"):
        # run simulation
        status = subprocess.run(f"TOP={top} make -C questa/", shell=True)
        # parse Questa log file
        log = open("questa/qrun.log").read()
        summary = re.search(r'Totals: Errors:\s+(\d+), Warnings:\s+(\d+)', log)
    if (simulator == "verilator"):
        # run simulation
        status = subprocess.run(f"TOP={top} make -C verilator/", shell=True)
#        # parse Questa log file
#        log = open("questa/qrun.log").read()
#        summary = re.search(r'Totals: Errors:\s+(\d+), Warnings:\s+(\d+)', log)
    errors   = summary.groups()[0]
    warnings = summary.groups()[1]
    # create report
    report.append([top, errors, warnings])

# print report
print("==== REPORT ====")
for test in report:
    print(test)
