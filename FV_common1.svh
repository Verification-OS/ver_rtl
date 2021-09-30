
`pragma protect begin
`protect

`ifndef _FV_COMMON1_VH
`define _FV_COMMON1_VH

// =============================
// FV modules `defines (macros)

/* maybe play with this to speed things up once the queues have been coded for wrap-around pointers (which are not right now)
`ifdef FV_ENABLE_DUP
 `ifdef FV_ENABLE_CMT 
  `define FV_IF_INSTR_QUEUE_DEPTH 256
 `else
  // Note: needs to be more if going deeper?
  `define FV_IF_INSTR_QUEUE_DEPTH 32
 `endif
`else
 // Note: queue not used if not FV_ENABLE_DUP so can probably drop to 4 or 2, but EX Q needs to be deeper
 `define FV_IF_INSTR_QUEUE_DEPTH 8
`endif
*/
`define FV_IF_INSTR_QUEUE_DEPTH 256
`define FV_IF_INSTR_QUEUE_POINTER_WIDTH $clog2(`FV_IF_INSTR_QUEUE_DEPTH)

// Note: doesn't depend on IF Q size, but longest latency instr (including ld/st) + pipeline depth
`define FV_EX_INSTR_QUEUE_DEPTH (2*`FV_IF_INSTR_QUEUE_DEPTH)
`define FV_EX_INSTR_QUEUE_POINTER_WIDTH $clog2(`FV_EX_INSTR_QUEUE_DEPTH)

// Note: depend on IF Q size, but longest latency instr (including ld/st) + pipeline depth?
`define FV_CF_INSTR_QUEUE_DEPTH (2*`FV_IF_INSTR_QUEUE_DEPTH)
`define FV_CF_INSTR_QUEUE_POINTER_WIDTH $clog2(`FV_CF_INSTR_QUEUE_DEPTH)

// sets the size of the shift register that is used for aligning the commit signal with RF writes
`define FV_COMMIT_TO_RF_WR_DELAY_MAX 20
   
// =============================
// FV_ENABLE_DUP

`ifdef FV_ENABLE_DUP

 `define FV_SPLIT_RF_DMEM_SPACE

 `ifdef FV_ENABLE_CMT
   `define FV_NO_BUBBLE
 `else
// KNOB
  `define FV_RND_BUBBLE
 `endif

// KNOB
//  `define FV_DUP_NO_RND_MIX

  `ifdef FV_DUP_NO_RND_MIX
// the following needs FV_DUP_NO_RND_MIX to be defined, too?
// KNOB
//   `define FV_DUP_DO_ONE_SET
  `endif

`endif //  `ifdef FV_ENABLE_DUP

// =============================
// FV_ENABLE_CF

`ifdef FV_ENABLE_CF

// Note2:  w.o. DUP, CF doesn't do bubbles as instr_queue is bypassed
// KNOB
 `ifdef FV_ENABLE_CMT
   `define FV_NO_BUBBLE
 `else
  `define FV_RND_BUBBLE
 `endif

`endif //  `ifdef FV_ENABLE_CF

// =============================
// FV_ENABLE_CMT

// Note2: where do we set the limit and why? does it speed things up?
// affects FV_MAX_CLOCK_COUNTER
`define FV_CMT_CHECK_CLK_COUNT 1000

// =============================
// FV_ENABLE_SI

`ifdef FV_ENABLE_SI

 `define FV_SYMBOLIC_INITIAL_STATE
 `define FV_ENABLE_CF

`endif

// enable EX queue if either DUP or CF is enabled
`ifdef FV_ENABLE_DUP
 `ifndef FV_NO_EX_QUEUE
  `define FV_ENABLE_EX_QUEUE
 `endif
`elsif  FV_ENABLE_CF
 `ifndef FV_NO_EX_QUEUE
  `define FV_ENABLE_EX_QUEUE
 `endif
`endif

`endif //  `ifndef _FV_COMMON1_VH

`endprotect
`pragma protect end
