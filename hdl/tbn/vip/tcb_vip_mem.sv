////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) memory
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

module tcb_vip_mem
  import tcb_pkg::*;
//  import tcb_vip_pkg::*;
#(
  int unsigned SIZ = 2**8,
  int unsigned SPN = 1
)(
  // TCB interface (without modport constraints)
  tcb_if.sub tcb [0:SPN-1]
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // TODO: detect Xilinx Vivado simulator instead
//  `ifdef VERILATOR
  logic [8-1:0] mem [0:SIZ-1];  // 4194304
//  `else
//  logic [8-1:0] mem [0:1757700-1];
//  `endif

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

/*
  // initialization
  initial
  begin
    if (FN!="") begin
      void'(read_bin(FN));
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
  function int write_hex (
    string fn,
    int unsigned start_addr = 0,
    int unsigned finish_addr = SIZ-1
  );
    int code;  // status code
    int fd;    // file descriptor
    fd = $fopen(fn, "w");
    for (int unsigned addr=start_addr; addr<finish_addr; addr+=4) begin
  //    if (s.DW == 32) begin
        $fwrite(fd, "%h%h%h%h\n", mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
  //    end else begin
  //      $fwrite(fd, "%h%h%h%h%h%h%h%h\n", mem[addr+7], mem[addr+6], mem[addr+5], mem[addr+4], mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
  //    end
    end
    $fclose(fd);
    return code;
  endfunction: write_hex
*/
////////////////////////////////////////////////////////////////////////////////
// read/write access
////////////////////////////////////////////////////////////////////////////////

  generate
  for (genvar i=0; i<SPN; i++) begin: port

    int unsigned tmp_req_siz;

    // read/write data packed arrays
    logic [tcb[i].PHY_BEW-1:0][tcb[i].PHY.SLW-1:0] tmp_req_wdt;
    logic [tcb[i].PHY_BEW-1:0][tcb[i].PHY.SLW-1:0] tmp_rsp_rdt [0:tcb[i].PHY.DLY];

    // as a memory model, there is no immediate need for backpressure, this feature might be added in the future
    assign tcb[i].rdy = 1'b1;

    // as a memory model, there is no immediate need for error responses, this feature might be added in the future
    // TODO
    assign tcb[i].rsp.sts = 1'b0; // '{err: 1'b0, default: '0};

    // map write data to a packed array
    assign tmp_req_wdt = tcb[i].req.wdt;

    assign tmp_req_siz = (tcb[i].PHY.SIZ == TCB_LINEAR) ? tcb[i].req.siz : 2**tcb[i].req.siz;

    // write access
    always @(posedge tcb[i].clk)
    if (tcb[i].trn) begin
      if (tcb[i].req.wen) begin: write
        // temporary variables
        automatic int unsigned               adr;
        if (tcb[i].PHY.MOD == TCB_REFERENCE) begin: reference
          $display("DEBUG: tcb[%d]: write adr=%08X=%d, tmp_req_siz=%d, wdt=%08X", i, tcb[i].req.adr, tcb[i].req.adr, tmp_req_siz, tmp_req_wdt);
          for (int unsigned b=0; b<tmp_req_siz; b++) begin: byteenable
            // byte address
            adr = b + int'(tcb[i].req.adr);
            mem[adr%SIZ] <= tmp_req_wdt[b];
          end: byteenable
        end: reference
        else begin: memory
          $display("DEBUG: tcb[%d]: write adr=%08X=%d, ben=%04b, wdt=%08X", i, tcb[i].req.adr, tcb[i].req.adr, tcb[i].req.ben, tmp_req_wdt);
          for (int unsigned b=0; b<tcb[i].PHY_BEW; b++) begin: byteenable
            // byte address
            adr = b + int'(tcb[i].req.adr);
            if (tcb[i].req.ben[adr%tcb[i].PHY_BEW])  mem[adr%SIZ] <= tmp_req_wdt[adr%tcb[i].PHY_BEW];
          end: byteenable
        end: memory
      end: write
    end

    // initialize read data array
    initial begin
      tmp_rsp_rdt = '{default: 'x};
    end

    // combinational read data
    always @(*)
    if (tcb[i].trn) begin
      if (~tcb[i].req.wen) begin: read
        // temporary variables
        automatic int unsigned adr;
        if (tcb[i].PHY.MOD == TCB_REFERENCE) begin: reference
          tmp_rsp_rdt = '{default: 'x};
          for (int unsigned b=0; b<tmp_req_siz; b++) begin: byteenable
            adr = b + int'(tcb[i].req.adr);
            tmp_rsp_rdt[0][b] = mem[adr%SIZ];
          end: byteenable
        end: reference
        else begin: memory
          for (int unsigned b=0; b<tcb[i].PHY_BEW; b++) begin: byteenable
            adr = b + int'(tcb[i].req.adr);
            if (tcb[i].req.ben[adr%tcb[i].PHY_BEW])  tmp_rsp_rdt[0][adr%tcb[i].PHY_BEW] = mem[adr%SIZ];
            else                                     tmp_rsp_rdt[0][adr%tcb[i].PHY_BEW] = 'x;
          end: byteenable
        end: memory
      end: read
      else begin
        tmp_rsp_rdt[0] = 'x;
      end
    end else begin
      tmp_rsp_rdt[0] = 'x;
    end

    // read data delay pipeline
    for (genvar d=1; d<=tcb[i].PHY.DLY; d++) begin: delay
      always @(posedge tcb[i].clk)
      begin
        for (int unsigned b=0; b<tcb[i].PHY_BEW; b++) begin: byteenable
          if (tcb[i].dly[d-1].ben[b]) begin
            tmp_rsp_rdt[d][b] <= tmp_rsp_rdt[d-1][b];
          end
        end: byteenable
      end
    end: delay

    // map read data from an unpacked array
    assign tcb[i].rsp.rdt = tmp_rsp_rdt[tcb[i].PHY.DLY];

  end: port
  endgenerate

endmodule: tcb_vip_mem
