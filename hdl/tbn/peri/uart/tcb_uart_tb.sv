////////////////////////////////////////////////////////////////////////////////
// TCB UART testbench
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

module tcb_uart_tb
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,
  int unsigned DBW = 32,
  // RW channels
  string IFT = "CRW"
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well in Vivado 2023.1 thus this workaround

  // physical interface parameter
  localparam tcb_par_phy_t PHY1 = '{
    // signal bus widths
    SLW: TCB_PAR_PHY_DEF.SLW,
    ABW: ABW,
    DBW: DBW,
    ALW: $clog2(DBW/TCB_PAR_PHY_DEF.SLW),
    // protocol
    DLY: 0,
    // mode/size/order parameters
    MOD: TCB_PAR_PHY_DEF.MOD,
    SIZ: TCB_PAR_PHY_DEF.SIZ,
    ORD: TCB_PAR_PHY_DEF.ORD
  };

  localparam tcb_par_phy_t PHY = TCB_PAR_PHY_DEF;

  // GPIO width
  localparam int unsigned GW = 32;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // UART data width
  localparam int unsigned UDW = 8;
 
  // UART baudrate
  localparam int unsigned TX_BDR = 4;         // TX baudrate
  localparam int unsigned RX_BDR = 4;         // RX baudrate
  localparam int unsigned RX_SMP = RX_BDR/2;  // RX sample

  // TX string
  localparam string TX_STR = "Hello, World!";
  localparam int    TX_LEN = TX_STR.len();
  // RX string
  byte rx_str [TX_LEN];

  // system signals
  logic clk;  // clock
  logic rst;  // reset
/*
  // TCB interface
  tcb_if #(.PHY (PHY)) tcb_man     (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY)) tcb_man_wrc (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY)) tcb_man_rdc (.clk (clk), .rst (rst));
*/
  // TODO: the above code should be used instead
  // TCB interfaces
  tcb_if tcb_man     (.clk (clk), .rst (rst));
  tcb_if tcb_man_wrc (.clk (clk), .rst (rst));
  tcb_if tcb_man_rdc (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_transfer_c #(.PHY (PHY)) tcb_s;

  // TCB class objects
  tcb_s obj_man;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [PHY.DBW-1:0] rdt;  // read data
  tcb_rsp_sts_def_t   sts;  // status response

  logic [ 8-1:0] rdt8 ;  //  8-bit read data
  logic [16-1:0] rdt16;  // 16-bit read data
  logic [32-1:0] rdt32;  // 32-bit read data

  // UART signals
  logic uart_rxd;  // receive
  logic uart_txd;  // transmit

  // interrupts
  logic irq_tx;    // TX FIFO load is below limit
  logic irq_rx;    // RX FIFO load is above limit

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // time dispaly formatting
    $timeformat(-9, 3, "ns", 12);
    // connect virtual interfaces
    obj_man = new("MAN", tcb_man);
    // reset sequence
    rst <= 1'b1;
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    // write configuration
    $display("(%t) INFO: writing configuration begin.", $time);
    obj_man.write32('h08, 32'(TX_BDR-1), sts);  // TX baudrate
    obj_man.write32('h28, 32'(RX_BDR-1), sts);  // RX baudrate
    obj_man.write32('h2C, 32'(RX_SMP-1), sts);  // RX sample
    obj_man.write32('h30, 32'(TX_LEN-1), sts);  // RX IRQ level
    $display("(%t) INFO: writing configuration end.", $time);
    repeat (1) @(posedge clk);

    // read/check configuration
    $display("(%t) INFO: reading/checking configuration begin.", $time);
    obj_man.check32('h08, 32'(TX_BDR-1), '0);  // TX baudrate
    obj_man.check32('h28, 32'(RX_BDR-1), '0);  // RX baudrate
    obj_man.check32('h2C, 32'(RX_SMP-1), '0);  // RX sample
    obj_man.check32('h30, 32'(TX_LEN-1), '0);  // RX IRQ level
    $display("(%t) INFO: reading/checking configuration end.", $time);
    repeat (1) @(posedge clk);

    // write TX data
    $display("(%t) INFO: writing TX data begin.", $time);
    for (int unsigned i=0; i<TX_LEN; i++) begin
      obj_man.write32('h00, 32'(TX_STR[i]), sts);
    end
    $display("(%t) INFO: writing TX data end.", $time);

    // wait for RX IRQ
    $display("(%t) INFO: writing RX IRQ begin.", $time);
    do begin
      @(posedge clk);
    end while (!irq_rx);
    $display("(%t) INFO: writing RX IRQ end.", $time);

    // read RX data
    $display("(%t) INFO: reading RX data begin.", $time);
    for (int unsigned i=0; i<TX_LEN; i++) begin
      obj_man.read32('h20, rdt, sts);
      rx_str[i] = rdt[UDW-1:0];
    end
    $display("(%t) INFO: reading RX data end.", $time);

    // checking if TX and RX data arrays are the same
    if (string'(rx_str) != TX_STR) begin
      $display("ERROR: RX '%s' differs from TX '%s'", rx_str, TX_STR);
      $display("FAILURE");
    end else begin
      $display("SUCCESS");
    end

    // end simulation
    repeat (2) @(posedge clk);
    $finish();
  end

  // timeout (in case RX IRQ is not triggered)
  initial
  begin
    repeat (TX_LEN*10*TX_BDR + 100) @(posedge clk);
    $display("ERROR: RX IRQ not triggered.");
    $display("FAILURE");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  generate
  if (IFT == "CRW")
  begin: crw

  // TCB UART
  tcb_crw_uart #(
    .DW       (UDW)
  ) uart (
    // UART signals
    .uart_txd (uart_txd),
    .uart_rxd (uart_rxd),
    // TCB interface
    .tcb      (tcb_man),
    // interrupts
    .irq_tx   (irq_tx),
    .irq_rx   (irq_rx)
  );

  end: crw
  else if (IFT == "IRW")
  begin: irw

  // TCB independent channel splitter
  tcb_lib_common2independent crw2irw (
    // CRW subordinate port
    .tcb_crw_sub (tcb_man),
    // IRW manager ports
    .tcb_rdc_man (tcb_man_rdc),
    .tcb_wrc_man (tcb_man_wrc)
  );

  // TCB UART
  tcb_irw_uart #(
    .DW       (UDW)
  ) uart (
    // UART signals
    .uart_txd (uart_txd),
    .uart_rxd (uart_rxd),
    // TCB IRW interface
    .tcb_wrc  (tcb_man_wrc),
    .tcb_rdc  (tcb_man_rdc),
    // interrupts
    .irq_tx   (irq_tx),
    .irq_rx   (irq_rx)
  );

  end: irw
  endgenerate

  // UART loopback
  assign uart_rxd = uart_txd;

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_uart_tb
