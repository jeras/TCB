////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library priority/round-robin arbiter
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

module tcb_lite_lib_arbiter #(
    // arbitration priority mode
    parameter  string       MOD = "FX",  // "FX" - fixed priority, "RR" - round robin (TODO)
    // interconnect parameters (manager interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN),
    // interface priorities (lower number is higher priority)
    parameter  bit unsigned [IFL-1:0] PRI [IFN-1:0]
)(
    // TCB interfaces
    tcb_lite_if.sub sub [IFN-1:0],   // TCB subordinate interfaces (manager devices connect here)
    // control
    output logic [IFL-1:0] sel  // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report priority duplication
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // interface signal copies which can be indexed
    logic           tcb_vld [IFN-1:0];  // valid
    logic           tcb_trn [IFN-1:0];  // transfer
    logic           tcb_lck [IFN-1:0];  // lock
    // select signal
    logic [IFL-1:0] sel_cmb;  // combinational
    logic [IFL-1:0] sel_reg;  // registered
    logic           sel_lck;  // locked

    // extract valid and transfer from TCB interfaces
    generate
    for (genvar i=0; i<IFN; i++) begin: map
        assign tcb_vld[i] = sub[i].vld;
        assign tcb_trn[i] = sub[i].trn;
        assign tcb_lck[i] = sub[i].req.lck;
    end: map
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// fixed priority arbiter
////////////////////////////////////////////////////////////////////////////////

    typedef logic select_t [IFN-1:0];

    // priority reorder
    function automatic select_t reorder (
        logic                  val [IFN-1:0],  // input
        bit unsigned [IFL-1:0] ord [IFN-1:0]   // order
    );
        for (int unsigned i=0; i<IFN; i++) begin
            reorder[i] = val[ord[i]];
        end
    endfunction: reorder

    // priority encode
    function automatic logic [IFL-1:0] encode (select_t val);
        encode = 'x;  // optimization of undefined encodings
        for (int i=IFN; i>=0; i--) begin
            if (val[i])  encode = i[IFL-1:0];
        end
    endfunction: encode

    // combinational select
    assign sel_cmb = PRI[encode(reorder(tcb_vld, PRI))];

    // locking
    always_ff @(posedge sub[0].clk, posedge sub[0].rst)
    if (sub[0].rst) begin
        sel_lck <= 1'b0;
    end else begin
        if (tcb_trn[sel_cmb]) begin
            sel_lck <= tcb_lck[sel_cmb];
        end

    end

    // registered select
    always_ff @(posedge sub[0].clk)
    if (tcb_trn[sel_cmb] & tcb_lck[sel_cmb]) begin
        sel_reg <= sel_cmb;
    end

    // multiplexer between combinational and registered priority
    assign sel = sel_lck ? sel_reg : sel_cmb;

endmodule: tcb_lite_lib_arbiter
