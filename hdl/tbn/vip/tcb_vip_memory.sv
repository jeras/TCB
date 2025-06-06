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

module tcb_vip_memory
  import tcb_pkg::*;
//  import tcb_vip_blocking_pkg::*;
#(
  // memory file name
  parameter  string        MFN = "",
  // memory size
  parameter  int unsigned  SIZ = 2**8,
  // slave interface number
  parameter  int unsigned  IFN = 1,
  // write mask (which interfaces are allowed write access)
  parameter  bit [IFN-1:0] WRM = '1
)(
  // TCB interface
  tcb_if.sub tcb [IFN-1:0]
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

  generate
  for (genvar i=0; i<IFN; i++) begin
    initial assert (tcb[i].VIP) else $error("VIP parameter must be enabled to support read access.");
  end
  endgenerate

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

  // load memory at initial if a file is provided as parameter
  initial
  begin
    if (MFN.len()) begin
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
    int unsigned end_addr = SIZ-1
  );
    int fd;    // file descriptor
    fd = $fopen(fn, "w");
    for (int unsigned addr=start_addr; addr<end_addr; addr+=4) begin
  //    if (s.DW == 32) begin
        $fwrite(fd, "%h%h%h%h\n", mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
  //    end else begin
  //      $fwrite(fd, "%h%h%h%h%h%h%h%h\n", mem[addr+7], mem[addr+6], mem[addr+5], mem[addr+4], mem[addr+3], mem[addr+2], mem[addr+1], mem[addr+0]);
  //    end
    end
    $fclose(fd);
  endfunction: write_hex

////////////////////////////////////////////////////////////////////////////////
// read/write access
////////////////////////////////////////////////////////////////////////////////

  generate
  for (genvar i=0; i<IFN; i++) begin: port

    // local copies of TCB BUS parameters
    localparam DLY = tcb[i].CFG.HSK.DLY;
    localparam BEN = tcb[i].CFG_BUS_BYT;

    // request address and size (TCB_LOG_SIZE mode)
    int unsigned adr;
    int unsigned siz;

    // request address and size
    assign adr =    int'(tcb[i].req.adr);
    assign siz = 2**int'(tcb[i].req.siz);

    // write mask (which interfaces are allowed write access)
    // NOTE: `always_ff` provides better simulator performance than `always`,
    //       but allows only one statement to be able to write into the `mem` array

    if (WRM[i]) begin: write_mask

      // write access
      always_ff @(posedge tcb[i].clk)
      if (tcb[i].trn) begin
        if (tcb[i].req.wen) begin: write
          for (int unsigned b=0; b<BEN; b++) begin: bytes
            case (tcb[i].CFG.BUS.MOD)
              TCB_MOD_LOG_SIZE: begin: log_size
                // write only transfer size bytes
                if (b < siz)  mem[(adr+b)%SIZ] <= tcb[i].req.wdt[b];
              end: log_size
              TCB_MOD_BYTE_ENA: begin: byte_ena
                // write only enabled bytes
                if (tcb[i].req.byt[(adr+b)%BEN])  mem[(adr+b)%SIZ] <= tcb[i].req.wdt[(adr+b)%BEN];
              end: byte_ena
            endcase
          end: bytes
        end: write
      end

    end: write_mask

    // combinational read data
    // TODO: some simulator might detect multiple drivers even if there is a single interface
    //       but at least on Questa always_comb provides faster execution
    //always @(*)
    always_comb
    if (tcb[i].trn) begin
      if (~tcb[i].req.wen) begin: read
        for (int unsigned b=0; b<BEN; b++) begin: bytes
          case (tcb[i].CFG.BUS.MOD)
            TCB_MOD_LOG_SIZE: begin: log_size
              // read only transfer size bytes, the rest remains undefined
              if (b < siz)  tcb[i].rsp_dly[0].rdt[b] = mem[(adr+b)%SIZ];
              else          tcb[i].rsp_dly[0].rdt[b] = 'x;
            end: log_size
            TCB_MOD_BYTE_ENA: begin: byte_ena
              // read only enabled bytes, the rest remains undefined
              if (tcb[i].req.byt[(adr+b)%BEN])  tcb[i].rsp_dly[0].rdt[(adr+b)%BEN] = mem[(adr+b)%SIZ];
              else                              tcb[i].rsp_dly[0].rdt[(adr+b)%BEN] = 'x;
            end: byte_ena
          endcase
        end: bytes
      end: read
      // as a memory model, there is no immediate need for error responses, this feature might be added in the future
      // TODO
      tcb[i].rsp_dly[0].sts = '0; // '{err: 1'b0, default: '0};
    end

    // as a memory model, there is no immediate need for backpressure, this feature might be added in the future
    assign tcb[i].rdy = 1'b1;

  end: port
  endgenerate

endmodule: tcb_vip_memory
