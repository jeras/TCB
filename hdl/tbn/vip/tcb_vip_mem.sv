////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) memory
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
  import tcb_vip_pkg::*;
#(
  int unsigned SZ = 2**8,
  int unsigned PN = 1
)(
  // TCB interface (without modport constraints)
  tcb_if.sub tcb [0:PN-1]
);

  // parameterized class specialization
  typedef tcb_c #(tcb[0].ABW, tcb[0].DBW, tcb[0].SLW) tcb_s;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // TODO: detect Xilinx Vivado simulator instead
//  `ifdef VERILATOR
  logic [8-1:0] mem [0:SZ-1];  // 4194304
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
    int unsigned finish_addr = SZ-1
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
  for (genvar i=0; i<PN; i++) begin: port

    // read/write data packed arrays
    logic [tcb[i].BEW-1:0][tcb[i].SLW-1:0] tmp_wdt;
    logic [tcb[i].BEW-1:0][tcb[i].SLW-1:0] tmp_rdt [0:tcb[i].DLY];

    assign tcb[i].rdy = 1'b1;
    assign tcb[i].err = 1'b0;

    // map write data to a packed array
    assign tmp_wdt = tcb[i].wdt;

    // write access
    always @(posedge tcb[i].clk)
    if (tcb[i].trn) begin
      if (tcb[i].wen) begin
        for (int unsigned b=0; b<tcb[i].BEW; b++) begin
          if (tcb[i].ben[b])  mem[(b+int'(tcb[i].adr))%SZ] <= tmp_wdt[(b+int'(tcb[i].adr))%tcb[i].BEW];
        end
      end
    end

    // map read data from a packed array
    assign tcb[i].rdt = tmp_rdt[tcb[i].DLY];

    initial begin
      tmp_rdt <= '{default: 'x};
    end

    // read data pipeline
    for (genvar d=1; d<=tcb[i].DLY; d++) begin
      always @(posedge tcb[i].clk)
      begin
        for (int unsigned b=0; b<tcb[i].BEW; b++) begin
          if (tcb[i].rbe[d][b])  tmp_rdt[d][b] <= tmp_rdt[d-1][b];
        end
      end
    end

    // combinational read
    // TODO: think about the correct assignment operator, read data is supposed to be held till the next transfer
    always @(*)
    if (tcb[i].trn) begin
      if (~tcb[i].wen) begin
        for (int unsigned b=0; b<tcb[i].BEW; b++) begin
//          tmp_rdt[0][((b+int'(tcb[i].adr))%tcb[i].BEW] <= (tcb[i].ben[b] ==? CFG_BEN_RD) ? mem[(b+int'(tcb[i].adr))%SZ] : 'x;
          $display("DEBUG: byte = 8'b%08h", mem[(int'(tcb[i].adr)+b)%SZ]);
          tmp_rdt[0][(b+int'(tcb[i].adr))%tcb[i].BEW] <= tcb[i].ben[b] ? mem[(b+int'(tcb[i].adr))%SZ] : 'x;
        end
      end
    end

  end: port
  endgenerate

endmodule: tcb_vip_mem