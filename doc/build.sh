#!/bin/sh

#wavedrom-cli -i tcb_handshake.json --svg tcb_handshake.svg
#wavedrom-cli -i tcb_reset.json     --svg tcb_reset.svg
#wavedrom-cli -i tcb_write.json     --svg tcb_write.svg
#wavedrom-cli -i tcb_read.json      --svg tcb_read.svg

wavedrom-cli -i lite_doc/tcb_lite_handshake.json         --svg lite_doc/tcb_lite_handshake.svg
wavedrom-cli -i lite_doc/tcb_lite_reset.json             --svg lite_doc/tcb_lite_reset.svg
wavedrom-cli -i lite_doc/tcb_lite_write.json             --svg lite_doc/tcb_lite_write.svg
wavedrom-cli -i lite_doc/tcb_lite_read.json              --svg lite_doc/tcb_lite_read.svg
wavedrom-cli -i lite_doc/tcb_lite_read_modify_write.json --svg lite_doc/tcb_lite_read_modify_write.svg

asciidoctor-pdf lite_doc/TCB-Lite.adoc