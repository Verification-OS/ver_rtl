
// =====================
// ISA-dependent defines

`define FV_INCLUDE_RISCV
`define FV_INCLUDE_RV32M
`define FV_INCLUDE_RV64M
`define FV_INCLUDE_RV64
// leave the following for -o inc_rva
//`define FV_INCLUDE_RVA
// Note: FENCE instr causes kill after commit; fix and add back
//`define FV_INCLUDE_MISC_MEM

// Note0: branch prediction not supported yet so need to exclude all JMP and BR
`define FV_EXCLUDE_JMP_BR

// Note1: the commit signal doesn't get asserted for ECAL
`define FV_EXCLUDE_ECALL_EBREAK
// Note
`ifdef FV_INCLUDE_RVA
 `ifdef FV_ENABLE_DUP
  `define FV_LIMIT_LS_BASE_R0
 `endif
`endif

`ifdef FV_INCLUDE_RVF
 `define FV_INCLUDE_RVD
`endif

// =======================
// ISA-independent defines

`define FV_DUT_PATH ariane_ara_wrapper
`define FV_DUT_HAS_RF2
`define FV_DUT_HAS_RF3
`define FV_DUT_VRF_VLEN `VLEN
`define DMEM_SIZE 128
`define FV_DUT_MEM_DATA_WIDTH 64
`ifdef FV_IMEM_WIDTH_64
 `define FV_IF_BUS_WIDTH 64
 `define FV_DUT_INSTR_RDATA_WIDTH 64
 // no bubble in the middle of instructions in one cycle, RND bubble still works
 `define FV_NO_BUBBLE
`else
 `define FV_DUT_INSTR_RDATA_WIDTH 32
`endif

`define FV_MAX_COMMIT_PER_CYCLE 2
`define FV_NUM_RF_WR_PORTS 2
`define FV_NUM_RF2_WR_PORTS 2
`define FV_NUM_RF3_WR_PORTS 1

// define the following if JAL does not cause a IF_kill signal (takes effect in early pipe stage)
`define FV_DUT_DIRECT_JMPS_NO_KILL
// define the following if atomics always flush (kill) the pipeline
`define FV_DUT_ATOMICS_ALWAYS_FLUSH
// define one of the following two CSR related flush (kill) cases
//   - first one when all CSR instructions cause flush (kill) even if just doing read
//   - second one when only CSR do a write operation to the register cause flush (kill)
//`define FV_DUT_CSR_ALWAYS_FLUSH
`define FV_DUT_CSR_WRITE_ALWAYS_FLUSH

`define FV_IF_INSTR_BUS_USED
`define FV_HOLD_OUTPUT_UNDER_STALL
`define FV_COMMIT_TO_RF_WR_DELAY 0
`define FV_NO_DUP_SYNC_READY

`define FV_FLOP_INSTR_OUTPUTS
`ifdef FV_FLOP_INSTR_OUTPUTS
 `define FV_SI_FE_PIPE_DELAY 1
`else
 `define FV_SI_FE_PIPE_DELAY 0
`endif

`ifndef FV_INCLUDE_IF_STAGE
 `define FV_NO_OUTPUT_WHEN_KILL
`endif

// splitting instr/data address space
`define FV_DUT_INSTR_ADDRESS_BASE  64'h1_0000
`define FV_DUT_INSTR_ADDRESS_LIMIT 64'h1_ffff
`define FV_DUT_NUM_MEM_REGIONS 8
`define FV_DUT_DATA_ADDRESS_BASE   64'h0_0000
`define FV_DUT_DATA_ADDRESS_LIMIT  64'h0_ffff

// Note: TBD for cva6
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
 `define FV_CMT_CHECK_WARMUP_COUNT 32'd32
 `define FV_CMT_CHECK_MAX_LATENCY 32'd37
`endif // !`ifdef FV_EXCLUDE_RV32M_DIV

`define FV_SI_SRC_CAPTURE_CYCLE 4

//Note0: cannot do this for >2 pipe stages
//`undef FV_JAL_RD_OR
//`define FV_JAL_RD_CAN_OVERRIDE
// stay within IMEM address range and instr alignment
//`define FV_JAL_RD_OR_VALUE 32'hdeadbea8

// knobs; Note turn into run.sh options
`define FV_DUT_DISABLE_ICACHE
`define FV_DUT_DISABLE_DCACHE
// disable branch prediction
// the following is used in frontend.sv; didn't work as JAL doesn't get the correct next PC?
`define FV_DUT_DISABLE_BP
  
