////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP (Verification IP) manager/monitor/subordinate TestBench
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

module tcb_lite_vip_tb #(
    // configuration parameters
    parameter int unsigned DELAY =  1,  // response delay
    parameter int unsigned WIDTH = 32,  // data/address width (only 32/64 are supported)
    parameter bit [WIDTH-1] MASK = '1,  // address mask
    parameter bit           MODE = '1   // bus mode (0-logarithmic size, 1-byte enable)
);

    localparam bit VIP = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals
    logic clk;  // clock
    logic rst;  // reset

    // testbench status signals
    string       testname;  // test name
    int unsigned errorcnt;  // ERROR counter

    // TCB interfaces
    tcb_lite_if #(DELAY, WIDTH, MASK, MODE, VIP) tcb (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// reference data for tests
////////////////////////////////////////////////////////////////////////////////

    // data organized into packed bytes
    typedef logic [tcb.WIDTH-1:0] data_t;

    // created data for tests
    function automatic data_t data_test_f (
        input logic [8/2-1:0] val = 'x
    );
        for (int unsigned i=0; i<tcb.WIDTH/8; i++) begin
            data_test_f[i] = {val, i[8/2-1:0]};
        end
    endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// manager/subordinate VIP devices
////////////////////////////////////////////////////////////////////////////////

    // VIP manager
    tcb_lite_vip_manager #(
//        .QUEUE (QUEUE)
    ) man (
        .tcb (tcb)
    );

    // VIP manager
    tcb_lite_vip_subordinate #(
//        .QUEUE (QUEUE)
    ) sub (
        .tcb (tcb)
    );

    tcb_lite_vip_protocol_checker chk (
        .tcb (tcb)
    );


////////////////////////////////////////////////////////////////////////////////
// test nonblocking API
////////////////////////////////////////////////////////////////////////////////

    task automatic test_nonblocking;
    endtask: test_nonblocking

////////////////////////////////////////////////////////////////////////////////
// test blocking API
////////////////////////////////////////////////////////////////////////////////

    task automatic test_blocking;
    endtask: test_blocking

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    // clock
    initial          clk = 1'b1;
    always #(20ns/2) clk = ~clk;

    // test sequence
    initial
    begin
        // reset sequence
        rst = 1'b1;
        repeat (2) @(posedge clk);
        rst = 1'b0;
        repeat (1) @(posedge clk);

        // tests
        test_nonblocking;
        test_blocking;

        repeat (2) @(posedge clk);
        if (errorcnt>0)  $display("FAILURE: there were %d errors.", errorcnt);
        else             $display("SUCCESS.");
        $finish();
    end

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        $dumpfile("test.fst");
        $dumpvars;
    end

endmodule: tcb_lite_vip_tb
