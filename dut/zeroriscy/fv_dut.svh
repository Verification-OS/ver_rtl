
// =====================
// ISA-dependent defines

`define FV_INCLUDE_RISCV
`define FV_INCLUDE_RV32M

// Note1: kill cannot be always associated with the correct CF in EX queue
`define FV_EXCLUDE_ECALL_EBREAK

// =======================
// ISA-independent defines

`define FV_DUT_PATH riscv_wrapper
`define DMEM_SIZE 128

`define FV_HOLD_OUTPUT_UNDER_STALL
`define FV_COMMIT_TO_RF_WR_DELAY 0

`define FV_IF_INSTR_BUS_USED

`define FV_FLOP_INSTR_OUTPUTS
`ifdef FV_FLOP_INSTR_OUTPUTS
 `define FV_SI_FE_PIPE_DELAY 1
`else
 `define FV_SI_FE_PIPE_DELAY 0
`endif

// ECALL and EBREAK destination addresses , ECALL=0x88, EBREAK=0xc0
`define FV_RV_DST_ADDR_ECALL  32'h0088
`define FV_RV_DST_ADDR_EBREAK 32'h00c0

// CMT settings
`ifdef FV_EXCLUDE_RV32M_DIV
  // without DIV, MUL is the longest instruction and takes 4 cycles
 `define FV_CMT_CHECK_WARMUP_COUNT 32'd7
 `define FV_CMT_CHECK_MAX_LATENCY 32'd5
`else
 `define FV_CMT_CHECK_WARMUP_COUNT 32'd38
 `define FV_CMT_CHECK_MAX_LATENCY 32'd37
`endif // !`ifdef FV_EXCLUDE_RV32M_DIV

`define FV_SI_SRC_CAPTURE_CYCLE 4

`define FV_JAL_RD_CAN_OVERRIDE
// stay within IMEM address range and instr alignment
`define FV_JAL_RD_OR_VALUE 32'hdeadbea8
