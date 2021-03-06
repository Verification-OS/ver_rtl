
`protect

// Note: this is just a place (copy from zeroriscy) holder SI latencies file for RIDECORE; numbers TBD
`ifndef _FV_SI_LATENCIES_DUT_SVH
`define _FV_SI_LATENCIES_DUT_SVH

`define FV_SI_LATENCY_ALU  (2 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_ADD  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SUB  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SLL  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SLT  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SLTU `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_XOR  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SRL  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_SRA  `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_OR   `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_AND  `FV_SI_LATENCY_ALU

`define FV_SI_LATENCY_LUI   `FV_SI_LATENCY_ALU
`define FV_SI_LATENCY_AUIPC `FV_SI_LATENCY_ALU

`define FV_SI_LATENCY_MUL_ALL (5 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_MUL    `FV_SI_LATENCY_MUL_ALL
`define FV_SI_LATENCY_MULH   `FV_SI_LATENCY_MUL_ALL
`define FV_SI_LATENCY_MULHSU `FV_SI_LATENCY_MUL_ALL
`define FV_SI_LATENCY_MULHU  `FV_SI_LATENCY_MUL_ALL

`define FV_SI_LATENCY_DIV_ALL (38 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_DIV  `FV_SI_LATENCY_DIV_ALL
`define FV_SI_LATENCY_DIVU `FV_SI_LATENCY_DIV_ALL
`define FV_SI_LATENCY_REM  `FV_SI_LATENCY_DIV_ALL
`define FV_SI_LATENCY_REMU `FV_SI_LATENCY_DIV_ALL

`define FV_SI_LATENCY_LB (3 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_LH (4 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_LW (4 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_LBU (3 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_LHU (4 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_SB (3 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_SH (4 + `FV_SI_FE_PIPE_DELAY)
`define FV_SI_LATENCY_SW (4 + `FV_SI_FE_PIPE_DELAY)

`define FV_SI_LATENCY_JMP (3 + `FV_SI_FE_PIPE_DELAY)

`endif //  `ifndef _FV_SI_LATENCIES_DUT_SVH

`endprotect
