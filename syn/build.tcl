# import yosys commands
yosys -import

set PATH_HDL "../hdl"

#foreach dut { \
#    "ERROR" \
#    "PASSTHROUGH" \
#    "REGISTER_REQUEST" \
#    "REGISTER_RESPONSE" \
#    "REGISTER_BACKPRESSURE" \
#    "LOGSIZE2BYTEENA_ALIGNED_FALSE" \
#    "LOGSIZE2BYTEENA_ALIGNED_TRUE" \
#    "ARBITER_MULTIPLEXER" \
#    "DECODER_DEMULTIPLEXER" \
#}
foreach dut {"DECODER_DEMULTIPLEXER"} {
    if {$dut == "ARBITER_MULTIPLEXER"   || $dut == "PASSTHROUGH"} { set sub_ifn 2 } else { set sub_ifn 1 }
    if {$dut == "DECODER_DEMULTIPLEXER" || $dut == "PASSTHROUGH"} { set man_ifn 2 } else { set man_ifn 1 }

    foreach mod {0 1} {
        puts "================================================================================"
        puts "= DUT : $dut"
        puts "= MOD : $mod"
        puts "= SUB_IFN : $sub_ifn"
        puts "= MAN_IFN : $man_ifn"
        puts "================================================================================"

        read_slang -DSLANG \
        -G DUT="$dut" -G MOD=$mod -G SUB_IFN=$sub_ifn -G MAN_IFN=$man_ifn \
        $PATH_HDL/rtl/tcb_lite_pkg.sv \
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

        procs
        opt -full

        write_json ${dut}_mod${mod}.json
        write_verilog -sv ${dut}_mod${mod}.sv
        #write_rtlil $dut_yosys.rtlil

        exec netlistsvg ${dut}_mod${mod}.json -o ${dut}_mod${mod}.svg

        delete
    }
}
