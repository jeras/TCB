////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library misaligned_memory_controller testbench
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

module tcb_lib_misaligned_memory_controller_tb
  import tcb_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // handshake parameter
  parameter  int unsigned      DLY = TCB_HSK_DEF.DLY      // response delay
//  // bus parameters
//  parameter  tcb_bus_channel_t BUS_CHN = TCB_BUS_DEF.CHN,  // channel configuration
//  parameter  tcb_bus_mode_t    BUS_MOD = TCB_BUS_DEF.MOD,  // manager     data position mode
//  // data packing parameters for manager/subordinate
//  parameter  int unsigned      BUS_ALN = TCB_BUS_DEF.ALN,  // TODO
//  parameter  int unsigned      BUS_MIN = TCB_BUS_DEF.MIN,  // TODO
//  parameter  int unsigned      BUS_OFF = TCB_BUS_DEF.OFF,  // TODO
//  parameter  tcb_bus_order_t   PCK_ORD = TCB_BUS_DEF.ORD   // manager     byte order
);

  // handshake parameter
  localparam tcb_hsk_t HSK = TCB_HSK_DEF;

  // bus parameter
  localparam tcb_bus_t BUS = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_BYTE_ENA,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

  // physical interface parameter default
  localparam tcb_pck_t PCK = '{
    MIN: 0,
    OFF: 0,
    ALN: 0,
    BND: 0
  };

//  typedef tcb_c #(HSK, BUS_SIZ, PCK)::req_t req_t;
//  typedef tcb_c #(HSK, BUS_SIZ, PCK)::rsp_t rsp_t;

  // local request/response types are copies of packaged defaults
  typedef tcb_req_t req_t;
  typedef tcb_rsp_t rsp_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals (initialized)
  logic clk = 1'b1;  // clock
  logic rst = 1'b1;  // reset

  string testname = "none";

  // TCB interfaces
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t) tcb (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t) tcb_vip_s;

  // TCB class objects
  tcb_vip_s obj = new(tcb, "MAN");
  
  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb.BUS_BEN-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                  sts;  // status response

  // local parameters
  localparam int unsigned BUS_BEN = BUS.DAT/8;
  localparam int unsigned BUS_MAX = $clog2(BUS_BEN);
  localparam int unsigned MEM_CEN = BUS_BEN/(2**PCK.OFF);
  localparam int unsigned MEM_ADR = BUS.ADR-BUS_MAX;
  localparam int unsigned MEM_DAT = BUS.DAT/MEM_CEN;

  // SRAM model
  logic [MEM_CEN-1:0]              mem_cen;  // chip enable
  logic                            mem_wen;  // write enable
  logic [MEM_CEN-1:0][MEM_ADR-1:0] mem_adr;  // address
  logic [MEM_CEN-1:0][MEM_DAT-1:0] mem_wdt;  // write data
  logic [MEM_CEN-1:0][MEM_DAT-1:0] mem_rdt;  // read data

////////////////////////////////////////////////////////////////////////////////
// tests
////////////////////////////////////////////////////////////////////////////////

  task test_aligned ();
    // write sequence
    $display("write sequence");
    testname = "write";
    // manager (blocking API)
    obj.write8 (32'h00000010,        8'h10, sts);
    obj.write8 (32'h00000011,      8'h32  , sts);
    obj.write8 (32'h00000012,    8'h54    , sts);
    obj.write8 (32'h00000013,  8'h76      , sts);
    obj.write16(32'h00000020,     16'hba98, sts);
    obj.write16(32'h00000022, 16'hfedc    , sts);
    obj.write32(32'h00000030, 32'h76543210, sts);

    // read sequence
    $display("read sequence");
    testname = "read";
    // manager (blocking API)
    obj.read8  (32'h00000010, rdt[1-1:0], sts);
    obj.read8  (32'h00000011, rdt[1-1:0], sts);
    obj.read8  (32'h00000012, rdt[1-1:0], sts);
    obj.read8  (32'h00000013, rdt[1-1:0], sts);
    obj.read16 (32'h00000020, rdt[2-1:0], sts);
    obj.read16 (32'h00000022, rdt[2-1:0], sts);
    obj.read32 (32'h00000030, rdt[4-1:0], sts);

    // check sequence
    $display("check sequence");
    testname = "check";
    obj.check8 (32'h00000010,        8'h10, 1'b0);
    obj.check8 (32'h00000011,      8'h32  , 1'b0);
    obj.check8 (32'h00000012,    8'h54    , 1'b0);
    obj.check8 (32'h00000013,  8'h76      , 1'b0);
    obj.check32(32'h00000010, 32'h76543210, 1'b0);
    obj.check16(32'h00000020,     16'hba98, 1'b0);
    obj.check16(32'h00000022, 16'hfedc    , 1'b0);
    obj.check32(32'h00000020, 32'hfedcba98, 1'b0);
    obj.check32(32'h00000030, 32'h76543210, 1'b0);
  endtask: test_aligned

  task test_misaligned ();
    // misaligned write sequence
    $display("misaligned write sequence");
    testname = "misaligned write";
    // test sequence
    obj.write16(32'h00000091, 16'h3210    , sts);
    obj.write16(32'h000000a3, 16'h7654    , sts);
    obj.write32(32'h000000b1, 32'h76543210, sts);
    obj.write32(32'h000000c2, 32'h76543210, sts);
    obj.write32(32'h000000d3, 32'h76543210, sts);

    // misaligned read/check sequence
    $display("misaligned read/check sequence");
    testname = "misaligned read/check";
    // test sequence
    obj.check16(32'h00000091, 16'h3210    , sts);
    obj.check16(32'h000000a3, 16'h7654    , sts);
    obj.check32(32'h000000b1, 32'h76543210, sts);
    obj.check32(32'h000000c2, 32'h76543210, sts);
    obj.check32(32'h000000d3, 32'h76543210, sts);
  endtask: test_misaligned

  task test_parameterized();
    // parameterized tests
    $display("parameterized tests");
    testname = "parameterized tests";
    for (int unsigned siz=tcb.PCK.MIN; siz<=tcb.BUS_MAX; siz++) begin
//    begin
//      static int unsigned siz=1;
//      for (int unsigned off=0; off<tcb.BUS_BEN; off+=2) begin
      for (int unsigned off=0; off<tcb.BUS_BEN; off+=2**tcb.PCK.OFF) begin
        // local variables
        string       id;
        int unsigned size;
        int unsigned len;
        // address
        logic [tcb.BUS.ADR-1:0] adr;
        // endianness
        logic         ndn;
        // local data arrays
        logic [8-1:0] dat [];  // pattern   data array
        logic [8-1:0] tmp [];  // temporary data array
        logic [8-1:0] nul [];  // empty     data array
        // local response
        tcb_rsp_sts_t sts;  // response status
        // local transactions
        tcb_vip_s::transaction_t transaction_w;  // reference write transaction
        tcb_vip_s::transaction_t transaction_r;  // reference read  transaction
        // local transfers
        automatic tcb_vip_s::transfer_queue_t transfer = '{};  // manager transfer queue

        // ID
        id = $sformatf("siz=%0d off=%0d", siz, off);
        $display("DEBUG: ID = '%s'", id);
        // address (stride is twice BUS_BEN, to accommodate unaligned accesses)
        adr = siz * tcb.BUS_BEN * 2;
        // prepare data array
        size = 2**siz;
        dat = new[size];
        for (int unsigned i=0; i<size; i++) begin
          // each byte within a transfer has an unique value
          dat[i] = {siz[4-1:0], off[4-1:0] + i[4-1:0]};
        end
        // expected response status
        sts = '0;

        // write/read transaction
        //                       ndn , adr    , wdt          rdt, sts
        transaction_w = '{req: '{1'b0, adr+off, dat}, rsp: '{nul, sts}};
        transaction_r = '{req: '{1'b0, adr+off, nul}, rsp: '{dat, sts}};
        // manager transfer queue
        len  = 0;
        len += obj.put_transaction(transfer, transaction_w, id);
        len += obj.put_transaction(transfer, transaction_r, id);

        // drive manager bus
        begin: parameterized_test_man
          obj.transfer_sequencer(transfer);
        end: parameterized_test_man

        // parse manager transfer queues into transactions
        len  = 0;
        len += obj.get_transaction(transfer, transaction_w);
        len += obj.get_transaction(transfer, transaction_r);
        // compare read data against write data
        assert (transaction_r.rsp.rdt == dat) else $error("Read data not matching previously written data (id = '%s')", id);
      end
    end
  endtask: test_parameterized

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin: test
    // reset sequence
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    test_aligned;
    if (PCK.ALN != tcb.BUS_MAX) begin
      test_misaligned;
    end
    test_parameterized;

    // end of test
    repeat (4) @(posedge clk);
    $finish();
  end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_protocol_checker chk (
    .tcb (tcb)
  );

  // SDRAM memory model subordinate
  sram_model #(
    .ADR  (MEM_ADR),
    .DAT  (MEM_DAT)
  ) mem [MEM_CEN-1:0] (
    .clk  (clk),
    .cen  (mem_cen),
    .wen  (mem_wen),
    .adr  (mem_adr),
    .wdt  (mem_wdt),
    .rdt  (mem_rdt)
  );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_misaligned_memory_controller #(
    .HSK      (HSK),
    .BUS      (BUS),
    .PCK      (PCK)
  ) dut (
    // TCB interface
    .tcb      (tcb),
    // SRAM interface
    .mem_cen  (mem_cen),
    .mem_wen  (mem_wen),
    .mem_adr  (mem_adr),
    .mem_wdt  (mem_wdt),
    .mem_rdt  (mem_rdt)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
`ifdef VERILATOR
    $dumpfile("test.fst");
`else
    $dumpfile("test.vcd");
`endif
    $dumpvars;
  end

endmodule: tcb_lib_misaligned_memory_controller_tb
