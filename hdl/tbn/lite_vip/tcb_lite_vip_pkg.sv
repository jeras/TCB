
package tcb_lite_vip_pkg;

    import tcb_lite_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// request comparison
////////////////////////////////////////////////////////////////////////////////

    class tcb_lite_vip_c #(
        parameter tcb_lite_cfg_t TST_CFG = TCB_LITE_CFG_DEF,
        parameter tcb_lite_cfg_t REF_CFG = TCB_LITE_CFG_DEF
    )

        // local parameters (calculated from configuration)
        localparam int unsigned CFG_BUS_BYT = CFG.BUS.DAT/8;          // byte enable width
        localparam int unsigned CFG_BUS_MAX = $clog2(CFG_BUS_BYT);    // maximum logarithmic size
        localparam int unsigned CFG_BUS_SIZ = $clog2(CFG_BUS_MAX+1);  // logarithmic size width
        
        // request type
        typedef struct {
            logic                   lck;  // arbitration lock
            logic                   ndn;  // endianness (0-little, 1-big)
            logic                   wen;  // write enable
            logic                   ren;  // read  enable
            logic [CFG.BUS.CTL-1:0] ctl;  // control (user defined request signals)
            logic [CFG.BUS.ADR-1:0] adr;  // address
            logic [CFG_BUS_SIZ-1:0] siz;  // transfer size
            logic [CFG_BUS_BYT-1:0] byt;  // byte enable
            logic [CFG.BUS.DAT-1:0] wdt;  // write data
        } req_t;
        
        // response type
        typedef struct {
            logic [CFG.BUS.DAT-1:0] rdt;  // read data
            logic [CFG.BUS.STS-1:0] sts;  // response status (user defined response signals)
            logic                   err;  // response error
        } rsp_t;


    endclass: tcb_lite_vip_c

////////////////////////////////////////////////////////////////////////////////
// request comparison
////////////////////////////////////////////////////////////////////////////////

// TODO: class parameterized with request/response struct types

endpackage: tcb_lite_vip_pkg
