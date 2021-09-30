
// =====================
// ISA-dependent defines

`define FV_INCLUDE_RISCV
`define FV_INCLUDE_RV32M
// Note: FENCE instr causes kill after commit; fix and add back
//`define FV_INCLUDE_MISC_MEM

// Note1: the commit signal doesn't get asserted for ECALL?
`define FV_EXCLUDE_ECALL_EBREAK

// =======================
// ISA-independent defines

`define FV_DUT_PATH riscv_wrapper
`ifdef FV_INCLUDE_RVF
 `define FV_DUT_HAS_RF2
`endif
`define DMEM_SIZE 128
`ifdef FV_IMEM_WIDTH_128
 `define FV_IF_BUS_WIDTH 128
 `define FV_RISCY_INSTR_RDATA_WIDTH 128
 // no bubble in the middle of instructions in one cycle, RND bubble still works
 `define FV_NO_BUBBLE
`else
 `define FV_RISCY_INSTR_RDATA_WIDTH 32
`endif

`define FV_NUM_RF_WR_PORTS 2
`define FV_NUM_RF2_WR_PORTS 2

`define FV_IF_INSTR_BUS_USED
`define FV_HOLD_OUTPUT_UNDER_STALL
// the following is really 2 but commit (from ID) gets flopped once already
// The real FV_COMMIT_TO_RF_WR_DELAY it is 2 for loads and 1 for everything else
// BUT since commit (from ID) gets flopped once already so setting to 0
// AND DUP_sync_ready and reg compare on sync cannot work because of variable latency
`define FV_COMMIT_TO_RF_WR_DELAY 0
`define FV_NO_DUP_SYNC_READY

`define FV_FLOP_INSTR_OUTPUTS
`ifdef FV_FLOP_INSTR_OUTPUTS
 `define FV_SI_FE_PIPE_DELAY 1
`else
 `define FV_SI_FE_PIPE_DELAY 0
`endif

// ECALL and EBREAK destination addresses , for riscy ECALL=0x0, EBREAK=0x0
`define FV_RV_DST_ADDR_ECALL  32'h0
`define FV_RV_DST_ADDR_EBREAK 32'h0

// CMT settings
`ifdef FV_EXCLUDE_RV32M_DIV
// Note: find the right params
 `define FV_CMT_CHECK_WARMUP_COUNT 32'd7
 `define FV_CMT_CHECK_MAX_LATENCY 32'd7
`else
// Note: find the right params
 `define FV_CMT_CHECK_WARMUP_COUNT 32'd38
 `define FV_CMT_CHECK_MAX_LATENCY 32'd37
`endif // !`ifdef FV_EXCLUDE_RV32M_DIV

`define FV_SI_SRC_CAPTURE_CYCLE 4

//Note0: cannot do this for >2 pipe stages
//`undef FV_JAL_RD_OR
//`define FV_JAL_RD_CAN_OVERRIDE
// stay within IMEM address range and instr alignment
//`define FV_JAL_RD_OR_VALUE 32'hdeadbea8

