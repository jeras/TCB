#!/bin/sh

wavedrom-cli -i lite_doc/tcb_lite_read_write_sram.json         --svg lite_doc/tcb_lite_read_write_sram.svg
wavedrom-cli -i lite_doc/tcb_lite_request_response_timing.json --svg lite_doc/tcb_lite_request_response_timing.svg
wavedrom-cli -i lite_doc/tcb_lite_handshake.json               --svg lite_doc/tcb_lite_handshake.svg
wavedrom-cli -i lite_doc/tcb_lite_reset.json                   --svg lite_doc/tcb_lite_reset.svg
wavedrom-cli -i lite_doc/tcb_lite_write.json                   --svg lite_doc/tcb_lite_write.svg
wavedrom-cli -i lite_doc/tcb_lite_read.json                    --svg lite_doc/tcb_lite_read.svg
wavedrom-cli -i lite_doc/tcb_lite_read_modify_write.json       --svg lite_doc/tcb_lite_read_modify_write.svg

asciidoctor-pdf lite_doc/TCB-Lite.adoc