
`pragma protect begin
`protect

`ifndef _FV_ISA_VH
`define _FV_ISA_VH

// RISC-V instruction set based on riscv-spec-v2.2.pdf downloadable from https://riscv.org/specifications/
// See tables in Sec. 19.

// Width-related constants
`define FV_RV32_INSTR_WIDTH     32
`define FV_RV32_INSTR_ADDR_WIDTH 32
`define FV_RV32_OPCODE_WIDTH    7
// NOTE: even in RV32E, the reg addr width is 5 and just its MSB in the instr. is 0 in the standard
`define FV_RV32_REG_ADDR_WIDTH  5
`define FV_RV32_REG_WIDTH       32
`define FV_RV32_IMM5_WIDTH      5
`define FV_RV32_IMM7_WIDTH      7
`define FV_RV32_IMM12_WIDTH     12
`define FV_RV32_SHAMT_WIDTH     5
`define FV_RV32_FUNCT3_WIDTH    3
`define FV_RV32_FUNCT7_WIDTH    7
`define FV_RV32_FUNCT12_WIDTH   12

// instruction fields bit locations
`define FV_RV32_INSTR_FIELD_OPCODE  6:0
`define FV_RV32_INSTR_FIELD_RD      11:7
`define FV_RV32_INSTR_FIELD_RS1     19:15
`define FV_RV32_INSTR_FIELD_RS2     24:20
`define FV_RV32_INSTR_FIELD_IMM5    11:7
`define FV_RV32_INSTR_FIELD_IMM7    31:25
`define FV_RV32_INSTR_FIELD_IMM12   31:20
`define FV_RV32_INSTR_FIELD_SHAMT   24:20
`define FV_RV32_INSTR_FIELD_FUNCT3  14:12
`define FV_RV32_INSTR_FIELD_FUNCT7  31:25
`define FV_RV32_INSTR_FIELD_FUNCT12 31:20

`define FV_RVZICSR_IMM5_WIDTH       5
`define FV_RVZICSR_INSTR_FIELD_IMM5 19:15

// NOP is encoded as ADDI x0, x0, 0
`define FV_RV_INSTR_NOP       `FV_RV32_INSTR_WIDTH'h00000013
`define FV_RV_INSTR_NOP_SYNC  `FV_RV32_INSTR_WIDTH'ha5a00013
`define FV_RV_INSTR_NOP_FLUSH `FV_RV32_INSTR_WIDTH'hfff00013

/////////////////
// Opcodes

`define FV_RV_OPCODE_LOAD      7'b0000011
`define FV_RV_OPCODE_STORE     7'b0100011
`define FV_RV_OPCODE_MADD      7'b1000011
`define FV_RV_OPCODE_BRANCH    7'b1100011

`define FV_RV_OPCODE_LOAD_FP   7'b0000111
`define FV_RV_OPCODE_STORE_FP  7'b0100111 
`define FV_RV_OPCODE_MSUB      7'b1000111
`define FV_RV_OPCODE_JALR      7'b1100111

`define FV_RV_OPCODE_CUSTOM_0  7'b0001011
`define FV_RV_OPCODE_CUSTOM_1  7'b0101011
`define FV_RV_OPCODE_NMSUB     7'b1001011
// reserved                 7'b1101011

`define FV_RV_OPCODE_MISC_MEM  7'b0001111
`define FV_RV_OPCODE_AMO       7'b0101111
`define FV_RV_OPCODE_NMADD     7'b1001111
`define FV_RV_OPCODE_JAL       7'b1101111

`define FV_RV_OPCODE_OP_IMM    7'b0010011
`define FV_RV_OPCODE_OP        7'b0110011
`define FV_RV_OPCODE_OP_FP     7'b1010011
`define FV_RV_OPCODE_SYSTEM    7'b1110011

`define FV_RV_OPCODE_AUIPC     7'b0010111
`define FV_RV_OPCODE_LUI       7'b0110111
// reserved for RVV         7'b1010111
// reserved                 7'b1110111

`define FV_RV_OPCODE_OP_IMM_32 7'b0011011
`define FV_RV_OPCODE_OP_32     7'b0111011
`define FV_RV_OPCODE_CUSTOM_2  7'b1011011
`define FV_RV_OPCODE_CUSTOM_3  7'b1111011

/////////////////////////////
// instruction encoding types

`define FV_RV_INSTR_TYPE_R {rv_funct7,                rv_rs2, rv_rs1, rv_funct3,         rv_rd,                   rv_opcode}
`define FV_RV_INSTR_TYPE_I {rv_imm[11:0],                     rv_rs1, rv_funct3,         rv_rd,                   rv_opcode}
`define FV_RV_INSTR_TYPE_S {rv_imm[11:5],             rv_rs2, rv_rs1, rv_funct3,         rv_imm[4:0],             rv_opcode}
`define FV_RV_INSTR_TYPE_B {rv_imm[12], rv_imm[10:5], rv_rs2, rv_rs1, rv_funct3,         rv_imm[4:1], rv_imm[11], rv_opcode}
`define FV_RV_INSTR_TYPE_U {rv_imm[31:12],                                               rv_rd,                   rv_opcode}
`define FV_RV_INSTR_TYPE_J {rv_imm[20], rv_imm[10:1],         rv_imm[11], rv_imm[19:12], rv_rd,                   rv_opcode}
    
/////////////////////////////
// RV32I base instruction set
/////////////////////////////

// branch FUNCT3 encodings
`define FV_RV32I_FUNCT3_BEQ  3'b000
`define FV_RV32I_FUNCT3_BNE  3'b001
`define FV_RV32I_FUNCT3_BLT  3'b100
`define FV_RV32I_FUNCT3_BGE  3'b101
`define FV_RV32I_FUNCT3_BLTU 3'b110
`define FV_RV32I_FUNCT3_BGEU 3'b111

// load/store FUNCT3 encodings
`define FV_RV32I_FUNCT3_LB  3'b000
`define FV_RV32I_FUNCT3_LH  3'b001
`define FV_RV32I_FUNCT3_LW  3'b010
`define FV_RV32I_FUNCT3_LBU 3'b100
`define FV_RV32I_FUNCT3_LHU 3'b101
`define FV_RV32I_FUNCT3_SB  3'b000
`define FV_RV32I_FUNCT3_SH  3'b001
`define FV_RV32I_FUNCT3_SW  3'b010

`define FV_RV64I_FUNCT3_LWU  3'b110
`define FV_RV64I_FUNCT3_LD   3'b011
`define FV_RV64I_FUNCT3_SD   3'b011

// FLH and FSH are not used yet (not in 2021 spec)
`define FV_RVF_FUNCT3_FLH   3'b001
`define FV_RVF_FUNCT3_FSH   3'b001

`define FV_RVF_FUNCT3_FLW   3'b010
`define FV_RVF_FUNCT3_FSW   3'b010

`define FV_RVD_FUNCT3_FLD   3'b011
`define FV_RVD_FUNCT3_FSD   3'b011
   
`define FV_RVQ_FUNCT3_FLQ   3'b100
`define FV_RVQ_FUNCT3_FSQ   3'b100
   
// arithmetic/logic FUNCT3 encodings
`define FV_RV32I_FUNCT3_ADD_SUB 3'b000
`define FV_RV32I_FUNCT3_SLL     3'b001
`define FV_RV32I_FUNCT3_SLT     3'b010
`define FV_RV32I_FUNCT3_SLTU    3'b011
`define FV_RV32I_FUNCT3_XOR     3'b100
`define FV_RV32I_FUNCT3_SRL_SRA 3'b101
`define FV_RV32I_FUNCT3_OR      3'b110
`define FV_RV32I_FUNCT3_AND     3'b111

// arithmetic/logic FUNCT7 encodings
`define FV_RV32_FUNCT7_SLLI  7'b0000000
`define FV_RV32_FUNCT7_SRLI  7'b0000000
`define FV_RV32_FUNCT7_SRAI  7'b0100000
`define FV_RV32_FUNCT7_ADD   7'b0000000
`define FV_RV32_FUNCT7_SUB   7'b0100000
`define FV_RV32_FUNCT7_SLL   7'b0000000
`define FV_RV32_FUNCT7_SLT   7'b0000000
`define FV_RV32_FUNCT7_SLTU  7'b0000000
`define FV_RV32_FUNCT7_XOR   7'b0000000
`define FV_RV32_FUNCT7_SRL   7'b0000000
`define FV_RV32_FUNCT7_SRA   7'b0100000
`define FV_RV32_FUNCT7_OR    7'b0000000
`define FV_RV32_FUNCT7_AND   7'b0000000

// MISC_MEM (opcode) FUNCT3 encodings
`define FV_RV32I_FUNCT3_FENCE   3'b000
`define FV_RV32I_FUNCT3_FENCE_I 3'b001

// PRIV FUNCT12 encodings
`define FV_RV32I_FUNCT12_ECALL  12'b000000000000
`define FV_RV32I_FUNCT12_EBREAK 12'b000000000001
`define FV_RV32I_FUNCT12_ERET   12'b000100000000

`define FV_RV_INSTR_ECALL  {`FV_RV32I_FUNCT12_ECALL,  13'b0, `FV_RV_OPCODE_SYSTEM}
`define FV_RV_INSTR_EBREAK {`FV_RV32I_FUNCT12_EBREAK, 13'b0, `FV_RV_OPCODE_SYSTEM}

// SYSTEM (opcode) FUNCT3 encodings
`define FV_RV32I_FUNCT3_PRIV   3'b000
`define FV_RV32I_FUNCT3_CSRRW  3'b001
`define FV_RV32I_FUNCT3_CSRRS  3'b010
`define FV_RV32I_FUNCT3_CSRRC  3'b011
`define FV_RV32I_FUNCT3_CSRRWI 3'b101
`define FV_RV32I_FUNCT3_CSRRSI 3'b110
`define FV_RV32I_FUNCT3_CSRRCI 3'b111

`define FV_RVF_CSR_FFLAGS     12'h001
`define FV_RVF_CSR_FRM        12'h002
`define FV_RVF_CSR_FCSR       12'h003

`define FV_RV32I_CSR_CYCLE    12'hC00
`define FV_RV32I_CSR_TIME     12'hC01
`define FV_RV32I_CSR_INSTRET  12'hC02
`define FV_RV32I_CSR_CYCLEH   12'hC80
`define FV_RV32I_CSR_TIMEH    12'hC81
`define FV_RV32I_CSR_INSTRETH 12'hC82

/////////////////////////////
// RV32M base instruction set
/////////////////////////////
`define FV_RV32M_FUNCT7_MUL_DIV 7'b0000001

`define FV_RV32M_FUNCT3_MUL    3'b000
`define FV_RV32M_FUNCT3_MULH   3'b001
`define FV_RV32M_FUNCT3_MULHSU 3'b010
`define FV_RV32M_FUNCT3_MULHU  3'b011
`define FV_RV32M_FUNCT3_DIV    3'b100
`define FV_RV32M_FUNCT3_DIVU   3'b101
`define FV_RV32M_FUNCT3_REM    3'b110
`define FV_RV32M_FUNCT3_REMU   3'b111

//////////////////////////////
//////////////////////////////
// RV32C 

`define FV_RV32C_INSTR_WIDTH     16
`define FV_RV32C_OPCODE_WIDTH    2
`define FV_RV32C_REG_ADDR_WIDTH  5
`define FV_RV32C_REGP_ADDR_WIDTH 3
`define FV_RV32C_FUNCT2_L_WIDTH  2
`define FV_RV32C_FUNCT2_H_WIDTH  2
`define FV_RV32C_FUNCT3_WIDTH    3
`define FV_RV32C_FUNCT4_WIDTH    4
`define FV_RV32C_FUNCT6_WIDTH    6

// instruction fields bit locations
`define FV_RV32C_INSTR_FIELD_OPCODE  1:0
// same as RS1: `define FV_RV32C_INSTR_FIELD_RD      11:7
`define FV_RV32C_INSTR_FIELD_RD      11:7
`define FV_RV32C_INSTR_FIELD_RS1     11:7
`define FV_RV32C_INSTR_FIELD_RS2     6:2
// for CIW and CL instructions
`define FV_RV32C_INSTR_FIELD_RDP     4:2
// use RS1P for RDP in CA and CB instructions
`define FV_RV32C_INSTR_FIELD_RS1P    9:7
`define FV_RV32C_INSTR_FIELD_RS2P    4:2
// same as RS1P in CA instructions `define FV_RV32C_INSTR_FIELD_RDP     9:7
`define FV_RV32C_INSTR_FIELD_FUNCT2_L 6:5
`define FV_RV32C_INSTR_FIELD_FUNCT2_H 11:10
`define FV_RV32C_INSTR_FIELD_FUNCT3   15:13
`define FV_RV32C_INSTR_FIELD_FUNCT4   15:12
`define FV_RV32C_INSTR_FIELD_FUNCT6   15:10

/////////////////
// Opcodes

`define FV_RV32C_OPCODE_C0      2'b00
`define FV_RV32C_OPCODE_C1      2'b01
`define FV_RV32C_OPCODE_C2      2'b10

/////////////////
// quadrant 0 (opcode = C0) 

// NOTE: some of the following coding are the same because the function depends
// RV32/64/128 support, or operand special values

`define FV_RV32C_FUNCT3_ILLEGAL   3'b000
`define FV_RV32C_FUNCT3_CADDI4SPN 3'b000
`define FV_RV32C_FUNCT3_CFLD      3'b001
`define FV_RV32C_FUNCT3_CLQ       3'b001
`define FV_RV32C_FUNCT3_CLW       3'b010
`define FV_RV32C_FUNCT3_CFLW      3'b011
`define FV_RV32C_FUNCT3_CLD       3'b011
`define FV_RV32C_FUNCT3_reserved  3'b100
`define FV_RV32C_FUNCT3_CFSD      3'b101 
`define FV_RV32C_FUNCT3_CSQ       3'b101
`define FV_RV32C_FUNCT3_CSW       3'b110
`define FV_RV32C_FUNCT3_CFSW      3'b111
`define FV_RV32C_FUNCT3_CSD       3'b111

/////////////////
// quadrant 1 (opcode = C1)    

// NOTE: some of the following coding are the same because the function depends on 
// RV32/64/128 support, and/or other fields and/or operand special values

// picking one of many possible bit combinations that would be CNOP
`define FV_RV32C_INSTR_CNOP       `FV_RV32C_INSTR_WIDTH'h0001
// Note: should we add RV32C_NOP_SYNC/FLUSH?

`define FV_RV32C_FUNCT3_CNOP      3'b000
`define FV_RV32C_FUNCT3_CADDI     3'b000
`define FV_RV32C_FUNCT3_CJAL      3'b001
`define FV_RV32C_FUNCT3_CADDIW    3'b001
`define FV_RV32C_FUNCT3_CLI       3'b010
`define FV_RV32C_FUNCT3_CADDI16SP 3'b011
`define FV_RV32C_FUNCT3_CLUI      3'b011
`define FV_RV32C_FUNCT3_CSRLI     3'b100
`define FV_RV32C_FUNCT6_CSRLI64   6'b100000
`define FV_RV32C_FUNCT3_CSRAI     3'b100
`define FV_RV32C_FUNCT6_CSRAI64   6'b100001
`define FV_RV32C_FUNCT3_CANDI     3'b100
`define FV_RV32C_FUNCT6_CSUB      6'b100011
`define FV_RV32C_FUNCT6_CXOR      6'b100011
`define FV_RV32C_FUNCT6_COR       6'b100011
`define FV_RV32C_FUNCT6_CAND      6'b100011
`define FV_RV32C_FUNCT6_CSUBW     6'b100111
`define FV_RV32C_FUNCT6_CADDW     6'b100111
`define FV_RV32C_FUNCT6_reserved  6'b100111
`define FV_RV32C_FUNCT3_CJ        3'b101
`define FV_RV32C_FUNCT3_CBEQZ     3'b110
`define FV_RV32C_FUNCT3_CBNEZ     3'b111

`define FV_RV32C_FUNCT2_H_CSRLI   2'b00
`define FV_RV32C_FUNCT2_H_CSRAI   2'b01
`define FV_RV32C_FUNCT2_H_CANDI   2'b10

`define FV_RV32C_FUNCT2_L_CSUB      2'b00
`define FV_RV32C_FUNCT2_L_CXOR      2'b01
`define FV_RV32C_FUNCT2_L_COR       2'b10
`define FV_RV32C_FUNCT2_L_CAND      2'b11
`define FV_RV32C_FUNCT2_L_CSUBW     2'b00
`define FV_RV32C_FUNCT2_L_CADDW     2'b01
`define FV_RV32C_FUNCT2_L_reserved1 2'b10
`define FV_RV32C_FUNCT2_L_reserved2 2'b11

/////////////////
// quadrant 2 (opcode = C2)    

// NOTE: some of the following coding are the same because the function depends on 
// RV32/64/128 support, and/or other fields and/or operand special values

`define FV_RV32C_FUNCT3_CSLLI     3'b000
`define FV_RV32C_FUNCT4_CSLLI64   4'b0000
`define FV_RV32C_FUNCT3_CFLDSP    3'b001
`define FV_RV32C_FUNCT3_CLQSP     3'b001
`define FV_RV32C_FUNCT3_CLWSP     3'b010
`define FV_RV32C_FUNCT3_CFLWSP    3'b011
`define FV_RV32C_FUNCT3_CLDSP     3'b011
`define FV_RV32C_FUNCT3_C2100     3'b100
`define FV_RV32C_FUNCT4_CJR       4'b1000
`define FV_RV32C_FUNCT4_CMV       4'b1000
`define FV_RV32C_FUNCT4_CEBREAK   4'b1001
`define FV_RV32C_FUNCT4_CJALR     4'b1001
`define FV_RV32C_FUNCT4_CADD      4'b1001
`define FV_RV32C_FUNCT3_CFSDSP    3'b101
`define FV_RV32C_FUNCT3_CSQSP     3'b101
`define FV_RV32C_FUNCT3_CSWSP     3'b110
`define FV_RV32C_FUNCT3_CFSWSP    3'b111
`define FV_RV32C_FUNCT3_CSDSP     3'b111

/////////////////////////////
// RV64I base instruction set
/////////////////////////////
`define FV_RV64_INSTR_ADDR_WIDTH 64
`define FV_RV64_REG_WIDTH        64

`define FV_RV64_SHAMT_WIDTH     6
`define FV_RV64_SHAMTW_WIDTH    5
`define FV_RV64_FUNCT6_WIDTH    6

`define FV_RV64_INSTR_FIELD_SHAMT   25:20
`define FV_RV64_INSTR_FIELD_SHAMTW  24:20
`define FV_RV64_INSTR_FIELD_FUNCT6  31:26

`define FV_RV64_FUNCT6_SLLI  6'b000000
`define FV_RV64_FUNCT6_SRLI  6'b000000
`define FV_RV64_FUNCT6_SRAI  6'b010000
   
/////////////////////////////
// RV32/64A instruction extensions
/////////////////////////////

`define FV_RV32A_FUNCT5_WIDTH    5
`define FV_RV32A_INSTR_FIELD_FUNCT5  31:27

`define FV_RV32A_FUNCT3_W  3'b010
`define FV_RV64A_FUNCT3_D  3'b011

`define FV_RV32A_FUNCT5_LR       5'b00010
`define FV_RV32A_FUNCT5_SC       5'b00011
`define FV_RV32A_FUNCT5_AMOSWAP  5'b00001
`define FV_RV32A_FUNCT5_AMOADD   5'b00000
`define FV_RV32A_FUNCT5_AMOXOR   5'b00100
`define FV_RV32A_FUNCT5_AMOAND   5'b01100
`define FV_RV32A_FUNCT5_AMOOR    5'b01000
`define FV_RV32A_FUNCT5_AMOMIN   5'b10000
`define FV_RV32A_FUNCT5_AMOMAX   5'b10100
`define FV_RV32A_FUNCT5_AMOMINU  5'b11000
`define FV_RV32A_FUNCT5_AMOMAXU  5'b11100

/////////////////////////////
// RVF, RVD, RVQ instruction extensions
/////////////////////////////

`define FV_RVF_REG_WIDTH           32
`define FV_RVD_REG_WIDTH           64
`define FV_RVQ_REG_WIDTH           128

`define FV_RVF_RM_WIDTH            3
`define FV_RVF_FUNCT2_WIDTH        2
`define FV_RVF_FUNCT12_WIDTH       12
   
`define FV_RVF_INSTR_FIELD_RM      14:12
`define FV_RVF_INSTR_FIELD_RS3     31:27
`define FV_RVF_INSTR_FIELD_FUNCT2  26:25
`define FV_RVF_INSTR_FIELD_FUNCT12 31:20

`define FV_RVF_FUNCT2_SINGLE         2'b00
`define FV_RVD_FUNCT2_DOUBLE         2'b01
`define FV_RVQ_FUNCT2_QUAD           2'b11
`define FV_RVF_FUNCT7_SINGLE    7'b0000000
`define FV_RVD_FUNCT7_DOUBLE    7'b0000001
`define FV_RVQ_FUNCT7_QUAD      7'b0000011
`define FV_RVF_FUNCT12_SINGLE  12'b000000000000
`define FV_RVD_FUNCT12_DOUBLE  12'b000000100000
`define FV_RVQ_FUNCT12_QUAD    12'b000001100000

`define FV_RVF_FUNCT7_FADD      7'b0000000
`define FV_RVF_FUNCT7_FSUB      7'b0000100
`define FV_RVF_FUNCT7_FMUL      7'b0001000
`define FV_RVF_FUNCT7_FDIV      7'b0001100
`define FV_RVF_FUNCT12_FSQRT   12'b010110000000
`define FV_RVF_FUNCT7_FSGNJ     7'b0010000
`define FV_RVF_FUNCT7_FMIN_MAX  7'b0010100
`define FV_RVF_FUNCT7_FCMP      7'b1010000
`define FV_RVF_FUNCT12_FCLASS  12'b111000000000

`define FV_RVF_FUNCT12_FCVTWS  12'b110000000000
`define FV_RVF_FUNCT12_FCVTWUS 12'b110000000001
`define FV_RVF_FUNCT12_FMVXW   12'b111000000000
`define FV_RVF_FUNCT12_FCVTSW  12'b110100000000
`define FV_RVF_FUNCT12_FCVTSWU 12'b110100000001
`define FV_RVF_FUNCT12_FMVWX   12'b111100000000

`define FV_RVD_FUNCT12_FCVTSD  12'b010000000001
`define FV_RVD_FUNCT12_FCVTDS  12'b010000100000
`define FV_RVD_FUNCT12_FCVTWD  12'b110000100000
`define FV_RVD_FUNCT12_FCVTWUD 12'b110000100001
`define FV_RVD_FUNCT12_FCVTDW  12'b110100100000
`define FV_RVD_FUNCT12_FCVTDWU 12'b110100100001

`define FV_RVQ_FUNCT12_FCVTSQ  12'b010000000011
`define FV_RVQ_FUNCT12_FCVTQS  12'b010001100000
`define FV_RVQ_FUNCT12_FCVTDQ  12'b010000100011
`define FV_RVQ_FUNCT12_FCVTQD  12'b010001100001
`define FV_RVQ_FUNCT12_FCVTWQ  12'b110001100000
`define FV_RVQ_FUNCT12_FCVTWUQ 12'b110001100001
`define FV_RVQ_FUNCT12_FCVTQW  12'b110101100000
`define FV_RVQ_FUNCT12_FCVTQWU 12'b110101100001

// RV64F/D/Q
`define FV_RVF_FUNCT12_FCVTLS  12'b110000000010
`define FV_RVF_FUNCT12_FCVTLUS 12'b110000000011
`define FV_RVF_FUNCT12_FCVTSL  12'b110100000010
`define FV_RVF_FUNCT12_FCVTSLU 12'b110100000011

`define FV_RVD_FUNCT12_FCVTLD  12'b110000100010
`define FV_RVD_FUNCT12_FCVTLUD 12'b110000100011
`define FV_RVD_FUNCT12_FMVXD   12'b111000100000
`define FV_RVD_FUNCT12_FCVTDL  12'b110100100010
`define FV_RVD_FUNCT12_FCVTDLU 12'b110100100011
`define FV_RVD_FUNCT12_FMVDX   12'b111100100000

`define FV_RVQ_FUNCT12_FCVTLQ  12'b110001100010
`define FV_RVQ_FUNCT12_FCVTLUQ 12'b110001100011
`define FV_RVQ_FUNCT12_FCVTQL  12'b110101100010
`define FV_RVQ_FUNCT12_FCVTQLU 12'b110101100011

`define FV_RVF_FUNCT3_RM_RNE    3'b000
`define FV_RVF_FUNCT3_RM_RTZ    3'b001
`define FV_RVF_FUNCT3_RM_RDN    3'b010
`define FV_RVF_FUNCT3_RM_RUP    3'b011
`define FV_RVF_FUNCT3_RM_RMM    3'b100
`define FV_RVF_FUNCT3_RM_RESRV1 3'b101
`define FV_RVF_FUNCT3_RM_RESRV2 3'b110
`define FV_RVF_FUNCT3_RM_DYN    3'b111

`define FV_RVF_FUNCT3_SGNJ      3'b000
`define FV_RVF_FUNCT3_SGNJN     3'b001
`define FV_RVF_FUNCT3_SGNJX     3'b010

`define FV_RVF_FUNCT3_MIN       3'b000
`define FV_RVF_FUNCT3_MAX       3'b001

`define FV_RVF_FUNCT3_FMV       3'b000

`define FV_RVF_FUNCT3_FEQ       3'b010
`define FV_RVF_FUNCT3_FLT       3'b001
`define FV_RVF_FUNCT3_FLE       3'b000

`define FV_RVF_FUNCT3_FCLASS    3'b001
   
/////////////////////////////
// RVD instruction extensions

   
// when RV128, define the RV64 so the ifdef's in RVC instr_constraint are simplified
`ifdef FV_INCLUDE_RV128
 `ifndef FV_INCLUDE_RV64
  `define FV_INCLUDE_RV64
 `endif
`endif
   
/////////////////////////////
// RVV instruction extensions
/////////////////////////////

`ifdef FV_DUT_VRF_VLEN
 `define FV_RVV_REG_WIDTH    `FV_DUT_VRF_VLEN
`else
 // default per spec. version 0.10
 `define FV_RVV_REG_WIDTH    128
`endif

`define FV_RV_OPCODE_RVV       7'b1010111

`define FV_RVV_FUNCT3_OPIVV  3'b000
`define FV_RVV_FUNCT3_OPFVV  3'b001
`define FV_RVV_FUNCT3_OPMVV  3'b010
`define FV_RVV_FUNCT3_OPIVI  3'b011
`define FV_RVV_FUNCT3_OPIVX  3'b100
`define FV_RVV_FUNCT3_OPFVF  3'b101
`define FV_RVV_FUNCT3_OPMVX  3'b110
`define FV_RVV_FUNCT3_SETVL  3'b111

`define FV_RVV_FUNCT6_WIDTH  6
`define FV_RVV_VM_WIDTH      1
`define FV_RVV_MOP_WIDTH     2
   
`define FV_RVV_INSTR_FIELD_FUNCT6  31:26
`define FV_RVV_INSTR_FIELD_NF      31:29
`define FV_RVV_INSTR_FIELD_MEW     28:28
`define FV_RVV_INSTR_FIELD_MOP     27:26
`define FV_RVV_INSTR_FIELD_VM      25:25
`define FV_RVV_INSTR_FIELD_LUMOP   24:20
`define FV_RVV_INSTR_FIELD_SUMOP   24:20

`define FV_RVV_MOP_UNIT_STRIDE        2'b00
`define FV_RVV_MOP_INDEXED_UNORDERED  2'b01
`define FV_RVV_MOP_STRIDED            2'b10
`define FV_RVV_MOP_INDEXED_ORDERED    2'b11

`define FV_RVV_VM_MASKED           1'b0
`define FV_RVV_VM_UNMASKED         1'b1

   
`define FV_RVV_FUNCT6_VADD      6'b000000


//////////////////////////////
// map ISA-dependent defines to ISA-independent defines

`define FV_INSTR_WIDTH      `FV_RV32_INSTR_WIDTH
`define FV_INSTR_NOP        `FV_RV_INSTR_NOP
`define FV_INSTR_NOP_SYNC   `FV_RV_INSTR_NOP_SYNC
`define FV_INSTR_NOP_FLUSH  `FV_RV_INSTR_NOP_FLUSH
`define FV_OPCODE_WIDTH     `FV_RV32_OPCODE_WIDTH
`define FV_REG_ADDR_WIDTH   `FV_RV32_REG_ADDR_WIDTH
`ifdef FV_INCLUDE_RV64
 `define FV_REG_WIDTH        `FV_RV64_REG_WIDTH
 `define FV_INSTR_ADDR_WIDTH `FV_RV64_INSTR_ADDR_WIDTH
 `define FV_MEM_ADDR_WIDTH   64
 `define FV_SHAMT_WIDTH      `FV_RV64_SHAMT_WIDTH
`else
 `define FV_REG_WIDTH        `FV_RV32_REG_WIDTH
 `define FV_INSTR_ADDR_WIDTH `FV_RV32_INSTR_ADDR_WIDTH
 `define FV_MEM_ADDR_WIDTH   32
 `define FV_SHAMT_WIDTH      `FV_RV32_SHAMT_WIDTH
`endif

`ifdef FV_INCLUDE_RVF
 `define FV_RF2_ENABLE
`endif

`ifdef FV_INCLUDE_RVD
 `define FV_REG2_WIDTH        `FV_RVD_REG_WIDTH
`else
 `define FV_REG2_WIDTH        `FV_RVF_REG_WIDTH
`endif

`ifdef FV_INCLUDE_RVV
 `define FV_RF3_ENABLE
`endif

`define FV_REG3_WIDTH         `FV_RVV_REG_WIDTH   
   
// RV64M includes RV32M
`ifdef FV_INCLUDE_RV64M
 `ifndef FV_INCLUDE_RV32M
  `define FV_INCLUDE_RV32M
 `endif
`endif

`ifdef FV_INCLUDE_RVC
 `define FV_MIN_INSTR_WIDTH  16
`else
 `define FV_MIN_INSTR_WIDTH  `FV_INSTR_WIDTH
`endif

// =============
// NOTE: the following can be defined in fv_dut.vh if needed
// Note: are the following `defines ISA-independent?  If yes, should they be moved to a different header file?
`ifndef FV_IF_BUS_WIDTH
   // default to 32-bit wide instruction fetch
 `define FV_IF_BUS_WIDTH      32
`endif

`ifndef FV_DUT_MEM_DATA_WIDTH
 `define FV_DUT_MEM_DATA_WIDTH 32
`endif

`ifndef FV_DUT_NUM_MEM_REGIONS
 `define FV_DUT_NUM_MEM_REGIONS 1
`endif
   
`ifndef FV_IF_MAX_INSTR_PER_CYCLE
 `define FV_IF_MAX_INSTR_PER_CYCLE (`FV_IF_BUS_WIDTH/`FV_MIN_INSTR_WIDTH)
`endif

`ifndef FV_MAX_COMMIT_PER_CYCLE
   `define FV_MAX_COMMIT_PER_CYCLE 1
`endif
 
`ifndef FV_NUM_RF_WR_PORTS
   `define FV_NUM_RF_WR_PORTS 1
`endif
`ifndef FV_NUM_RF2_WR_PORTS
   `define FV_NUM_RF2_WR_PORTS 1
`endif
`ifndef FV_NUM_RF3_WR_PORTS
   `define FV_NUM_RF3_WR_PORTS 1
`endif

`ifndef FV_SI_DMEM_REGION
   `define FV_SI_DMEM_REGION 0
`endif
   
// =============
 
`ifdef FV_RV32E
 `define FV_NUM_RF_REGS 16
`else
 `define FV_NUM_RF_REGS 32
`endif
`define FV_NUM_RF2_REGS 32
`define FV_NUM_RF3_REGS 32

`ifdef FV_DUP_BR
 `ifdef FV_JAL_RD_CAN_OVERRIDE
   // KNOB
  `define FV_JAL_RD_OR
  `define FV_NUM_RS_PAIRS (`FV_NUM_RF_REGS/2)
   // r1 and r1' can be compared
  `define FV_DUP_PAIR_R1
 `else
   // Note: always x1 or conditional on RVC?
  `ifdef FV_INCLUDE_RVC
   // use x1 because that's the implicit rd in C.JAL/R
   `define FV_LIMIT_JAL_RD 1
  `else
   `define FV_LIMIT_JAL_RD 0
   // r1 and r1' can be compared
   `define FV_DUP_PAIR_R1
  `endif
  `define FV_NUM_RS_PAIRS ((`FV_NUM_RF_REGS/2)-1)
 `endif
`else // !`ifdef FV_DUP_BR
   // Note: always x1 or conditional on RVC?
 `ifdef FV_INCLUDE_RVC
   // use x1 because that's the implicit rd in C.JAL/R
  `define FV_LIMIT_JAL_RD 1
 `else
  `define FV_LIMIT_JAL_RD 0
   // r1 and r1' can be compared
  `define FV_DUP_PAIR_R1
 `endif
 `define FV_NUM_RS_PAIRS (`FV_NUM_RF_REGS/2)
`endif //  `ifdef FV_DUP_BR

`define FV_NUM_RD_PAIRS  (`FV_NUM_RF_REGS/2)

`define FV_DUP_NEW_PAIRING
`ifdef FV_INCLUDE_RVC
   // have to enforce new pairing
 `ifndef FV_DUP_NEW_PAIRING
  `define FV_DUP_NEW_PAIRING
 `endif
`endif
   
// used for duplicate atomics instruction rs1 which is the effective address 
`ifdef FV_DUP_NEW_PAIRING
 `define FV_DUP_R0P      4
`else
 `define FV_DUP_R0P      (`FV_NUM_RF_REGS/2)
`endif

// if NOT FV_INCLUDE_RVA, then r0 and r0' can be compared
`ifndef FV_INCLUDE_RVA
 `define FV_DUP_PAIR_R0
`endif
   
   // struct for si-FV property signals
   typedef struct {
      logic [`FV_INSTR_WIDTH-1:0]      si_instr;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] si_pc;
      logic [`FV_REG_WIDTH-1:0] 	   si_rs1_value;
      logic [`FV_REG_WIDTH-1:0] 	   si_rs2_value;
      logic [`FV_REG_WIDTH-1:0] 	   si_imm12_signed_ext;
      logic [`FV_SHAMT_WIDTH-1:0]      si_shamt;

      logic [(`FV_REG_WIDTH*2)-1:0]    si_mul_result;
      logic [(`FV_REG_WIDTH*2)-1:0]    si_mulsu_result;
      logic [(`FV_REG_WIDTH*2)-1:0]    si_mulu_result;

      logic [`FV_REG_WIDTH-1:0] 	   si_div_result;
      logic [`FV_REG_WIDTH-1:0] 	   si_divu_result;
      logic [`FV_REG_WIDTH-1:0] 	   si_rem_result;
      logic [`FV_REG_WIDTH-1:0] 	   si_remu_result;

      logic [`FV_REG_WIDTH-1:0] 	   si_rf_probe_rd_value;
      logic [`FV_REG_WIDTH-1:0] 	   si_dmem_ld_value;
`ifdef FV_INCLUDE_RV64
      logic [`FV_REG_WIDTH-1:0] 	   si_dmem_ld_value_32b_sign_extended;
`endif
      logic [63:0] 			   si_dmem_8byte_value;
      logic [63:0] 			   si_expected_dmem_8byte_value;

      logic 	  si_check_ADDI;
      logic 	  si_check_SLTI;
      logic 	  si_check_SLTIU;
      logic 	  si_check_XORI;
      logic 	  si_check_ORI;
      logic 	  si_check_ANDI;
      logic 	  si_check_SLLI;
      logic 	  si_check_SRLI;
      logic 	  si_check_SRAI;
      logic 	  si_check_ADD;
      logic 	  si_check_SUB;
      logic 	  si_check_SLL;
      logic 	  si_check_SLT;
      logic 	  si_check_SLTU;
      logic 	  si_check_XOR;
      logic 	  si_check_SRL;
      logic 	  si_check_SRA;
      logic 	  si_check_OR;
      logic 	  si_check_AND;
      logic 	  si_check_MUL;
      logic 	  si_check_MULH;
      logic 	  si_check_MULHSU;
      logic 	  si_check_MULHU;
      logic 	  si_check_DIV;
      logic 	  si_check_DIVU;
      logic 	  si_check_REM;
      logic 	  si_check_REMU;
      logic 	  si_check_LUI;
      logic 	  si_check_AUIPC;
      logic 	  si_check_LB;
      logic 	  si_check_LH;
      logic 	  si_check_LW;
      logic 	  si_check_LBU;
      logic 	  si_check_LHU;
      logic 	  si_check_SB;
      logic 	  si_check_SH;
      logic 	  si_check_SW;
      logic 	  si_check_JAL;
      logic 	  si_check_JALR;

`ifdef FV_INCLUDE_RV64
      logic 	  si_check_LWU;
      logic 	  si_check_LD;
      logic 	  si_check_SD;
      logic 	  si_check_ADDIW;
      logic 	  si_check_SLLIW;
      logic 	  si_check_SRLIW;
      logic 	  si_check_SRAIW;
      logic 	  si_check_ADDW;
      logic 	  si_check_SUBW;
      logic 	  si_check_SLLW;
      logic 	  si_check_SRLW;
      logic 	  si_check_SRAW;

      logic 	  si_check_MULW;
      logic 	  si_check_DIVW;
      logic 	  si_check_DIVUW;
      logic 	  si_check_REMW;
      logic 	  si_check_REMUW;
`endif

`ifdef FV_INCLUDE_RVA
      logic 	  si_check_LRW;
      logic 	  si_check_SCW;
      logic 	  si_check_AMOSWAPW;
      logic 	  si_check_AMOADDW;
      logic 	  si_check_AMOXORW;
      logic 	  si_check_AMOANDW;
      logic 	  si_check_AMOORW;
      logic 	  si_check_AMOMINW;
      logic 	  si_check_AMOMAXW;
      logic 	  si_check_AMOMINUW;
      logic 	  si_check_AMOMAXUW;
 `ifdef FV_INCLUDE_RV64
      logic 	  si_check_LRD;
      logic 	  si_check_SCD;
      logic 	  si_check_AMOSWAPD;
      logic 	  si_check_AMOADDD;
      logic 	  si_check_AMOXORD;
      logic 	  si_check_AMOANDD;
      logic 	  si_check_AMOORD;
      logic 	  si_check_AMOMIND;
      logic 	  si_check_AMOMAXD;
      logic 	  si_check_AMOMINUD;
      logic 	  si_check_AMOMAXUD;
 `endif
`endif
   } si_prop_signals_t;

`endif //  `ifndef _FV_ISA_VH

`endprotect
`pragma protect end
