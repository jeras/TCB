# import yosys commands
yosys -import

set PATH_HDL "../hdl"

#foreach dut {"PASSTHROUGH"} {
foreach dut { \
    "ERROR" \
    "PASSTHROUGH" \
    "REGISTER_REQUEST" \
    "REGISTER_RESPONSE" \
    "REGISTER_BACKPRESSURE" \
    "LOGSIZE2BYTEENA_ALIGNED_FALSE" \
    "LOGSIZE2BYTEENA_ALIGNED_TRUE" \
    "ARBITER_MULTIPLEXER" \
    "DECODER_DEMULTIPLEXER" \
} {
    if {$dut == "ARBITER_MULTIPLEXER"  } { set sub_ifn 2 } else { set sub_ifn 1 }
    if {$dut == "DECODER_DEMULTIPLEXER"} { set man_ifn 2 } else { set man_ifn 1 }

    puts "================================================================================"
    puts "= DUT : $dut"
    puts "= SUB_IFN : $sub_ifn"
    puts "= MAN_IFN : $man_ifn"
    puts "================================================================================"

    read_slang -DSLANG \
    -G DUT="$dut" -G SUB_IFN=$sub_ifn -G MAN_IFN=$man_ifn \
    $PATH_HDL/rtl/tcb_lite_if.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_error.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_passthrough.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_register_request.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_register_response.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_register_backpressure.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_arbiter.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_multiplexer.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_decoder.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_demultiplexer.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_logsize2byteena.sv \
    $PATH_HDL/rtl/lite_lib/tcb_lite_lib_interconnect.sv \
    tcb_lite_dut_wrapper.sv

    hierarchy -top tcb_lite_dut_wrapper

    write_rtlil

    procs; opt

    #show

    write_json $dut.json

    exec netlistsvg $dut.json -o $dut.svg

    delete
}

#read_slang -DSLANG ../hdl/rtl/tcb_lite_if.sv \
# ../hdl/rtl/lite_lib/tcb_lite_lib_arbiter.sv \
# ../hdl/rtl/lite_lib/tcb_lite_lib_decoder.sv \
# ../hdl/rtl/lite_lib/tcb_lite_lib_multiplexer.sv \
# ../hdl/rtl/lite_lib/tcb_lite_lib_demultiplexer.sv \
# ../hdl/rtl/lite_lib/tcb_lite_lib_interconnect.sv \
# tcb_lite_dut_wrapper.sv
