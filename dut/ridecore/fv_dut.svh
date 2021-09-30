
// =====================
// ISA-dependent defines

`define FV_INCLUDE_RISCV
`define FV_INCLUDE_RV32M
`define FV_EXCLUDE_RV32M_DIV

// =======================
// ISA-independent defines

`define FV_DUT_PATH top
`define DMEM_SIZE 128

`ifdef FV_SUPER_SCALAR_2
 `define FV_IF_BUS_WIDTH 64
`endif

`define FV_MAX_COMMIT_PER_CYCLE 2
`define FV_NUM_RF_WR_PORTS 2

`define FV_RIDECORE_REMOVE_NEGEDGE
`define FV_RIDECORE_DISABLE_BRANCH_PREDICTION
`define FV_EXCLUDE_DEGENERATE_JAL

`define FV_NO_OUTPUT_WHEN_KILL
//`define FV_HOLD_OUTPUT_UNDER_STALL
`define FV_COMMIT_TO_RF_WR_DELAY 0
//`define FV_FLOP_INSTR_OUTPUTS
`ifdef FV_FLOP_INSTR_OUTPUTS
 `define FV_SI_FE_PIPE_DELAY 1
`else
 `define FV_SI_FE_PIPE_DELAY 0
`endif

//Note0: how to override in RRF?
`undef FV_JAL_RD_OR

// Note: remove once CF is implemented for RIDECORE
`define FV_NO_EX_QUEUE

// Note: what is the following setting for 2-way?
`define FV_CMT_CHECK_WARMUP_COUNT 32'd8
`define FV_CMT_CHECK_MAX_LATENCY 32'd8
`define FV_SI_SRC_CAPTURE_CYCLE 1

// ECALL and EBREAK are not supported by ridecore, just dummy destination addresses
`define FV_RV_DST_ADDR_ECALL  32'h0
`define FV_RV_DST_ADDR_EBREAK 32'h0

// Note: TBD likely cannot OR because >2 pipe stages
`define FV_JAL_RD_CAN_OVERRIDE
// stay within IMEM address range and instr alignment
`define FV_JAL_RD_OR_VALUE 32'hdeadbea8

// turned the following fixes into bugs that can be enabled for regressions
//`define FV_RIDECORE_FIX_1000 -> BUG_31
//`define FV_RIDECORE_FIX_1001 -> BUG_26 (rs_alu), BUG_27(rs_mul), BUG_28(rs_ldst), BUG_29(rs_branch)
//`define FV_RIDECORE_FIX_1002 -> BUG_30
