#!/bin/sh

wavedrom-cli -i tcb_handshake.json --svg tcb_handshake.svg
wavedrom-cli -i tcb_reset.json     --svg tcb_reset.svg
wavedrom-cli -i tcb_write.json     --svg tcb_write.svg
wavedrom-cli -i tcb_read.json      --svg tcb_read.svg
