////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP (Verification IP) memory
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
////////////////////////////////////////////////////////////////////////////////

module tcb_lite_vip_memory
    import tcb_lite_pkg::*;
#(
    // memory file name
    parameter  string        MFN = "",
    // memory size
    parameter  int unsigned  SIZE = 2**8,
    // slave interface number
    parameter  int unsigned  IFN = 1,
    // write mask (which interfaces are allowed write access)
    parameter  bit [IFN-1:0] WRM = '1
)(
    // TCB interface
    tcb_lite_if tcb [IFN-1:0]
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    generate
    for (genvar i=0; i<IFN; i++) begin
    end
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    logic [8-1:0] mem [0:SIZE-1];

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

    // load memory at initial if a file is provided as parameter
    initial
    begin
        if (MFN.len()>0) begin
            void'(read_bin(MFN));
        end
    end

    // read binary into memory
    function int read_bin (
        string fn
    );
        int code;  // status code
        int fd;    // file descriptor
        bit [640-1:0] err;
        fd = $fopen(fn, "rb");
        code = $fread(mem, fd);
`ifndef VERILATOR
        if (code == 0) begin
            code = $ferror(fd, err);
            $display("DEBUG: read_bin: code = %d, err = %s", code, err);
        end else begin
            $display("DEBUG: read %dB from binary file", code);
        end
`endif
        $fclose(fd);
        return code;
    endfunction: read_bin

    // dump
    function void write_hex (
        string fn,
        int unsigned start_addr = 0,
        int unsigned end_addr = SIZE-1
    );
        int fd;    // file descriptor
        fd = $fopen(fn, "w");
        for (int unsigned addr=start_addr; addr<end_addr; addr+=4) begin
    //      if (s.DW == 32) begin
            $fwrite(fd, "%h%h%h%h\n", mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
    //      end else begin
    //        $fwrite(fd, "%h%h%h%h%h%h%h%h\n", mem[addr+7], mem[addr+6], mem[addr+5], mem[addr+4], mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
    //      end
        end
        $fclose(fd);
    endfunction: write_hex

////////////////////////////////////////////////////////////////////////////////
// read/write access
////////////////////////////////////////////////////////////////////////////////

    generate
    for (genvar i=0; i<IFN; i++) begin: ifn

        localparam int unsigned BYT = tcb[i].BYT;

        // request address and size (TCB_LOG_SIZE mode)
        int unsigned adr;
        int unsigned siz;

        // request address and size
        assign adr =    int'(tcb[i].req.adr);
        assign siz = 2**int'(tcb[i].req.siz);

        logic [BYT-1:0][8-1:0] wdt;
        logic [BYT-1:0][8-1:0] rdt;

        // write mask (which interfaces are allowed write access)
        // NOTE: `always_ff` provides better simulator performance than `always`,
        //       but allows only one statement to be able to write into the `mem` array

        assign wdt = tcb[i].req.wdt;

        if (WRM[i]) begin: write_mask

            // write access
            always_ff @(posedge tcb[i].clk)
            if (tcb[i].trn) begin
                if (tcb[i].req.wen) begin: write
                    for (int unsigned b=0; b<BYT; b++) begin: bytes
                        if (tcb[i].MOD == 1'b0) begin
                            // write only transfer size bytes
                            if (b < siz)  mem[(adr+b)%SIZE] <= wdt[b];
                        end else begin
                            // write only enabled bytes
                            if (tcb[i].req.byt[(adr+b)%BYT])  mem[(adr+b)%SIZE] <= wdt[(adr+b)%BYT];
                        end
                    end: bytes
                end: write
            end

        end: write_mask

        // combinational read data
        // TODO: some simulator might detect multiple drivers even if there is a single interface
        //       but at least on Questa always_comb provides faster execution
        //always @(*)
        always_latch
        if (tcb[i].trn) begin
            if (tcb[i].req.ren) begin: read
                for (int unsigned b=0; b<BYT; b++) begin: bytes
                    if (tcb[i].MOD == 1'b0) begin
                        // read only transfer size bytes, the rest remains undefined
                        if (b < siz)  rdt[b] = mem[(adr+b)%SIZE];
                        else          rdt[b] = 'x;
                    end else begin
                        // read only enabled bytes, the rest remains undefined
                        if (tcb[i].req.byt[(adr+b)%BYT])  rdt[(adr+b)%BYT] = mem[(adr+b)%SIZE];
                        else                              rdt[(adr+b)%BYT] = 'x;
                    end
                end: bytes
            end: read
        end

        // continuous assignment
        assign tcb[i].rsp.rdt = $past(rdt, tcb[i].DLY, , @(posedge tcb[i].clk));
        assign tcb[i].rsp.sts = '0;
        assign tcb[i].rsp.err = 1'b0;

        // as a memory model, there is no immediate need for backpressure, this feature might be added in the future
        assign tcb[i].rdy = 1'b1;

    end: ifn
    endgenerate

endmodule: tcb_lite_vip_memory
