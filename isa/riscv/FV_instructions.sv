
module FV_instructions
  #(parameter DECODER = 1)
   (
    input [`FV_INSTR_WIDTH-1:0] instruction
    );

   // extract instruction fields
   wire [`FV_RV32_OPCODE_WIDTH-1:0]   opcode = instruction[`FV_RV32_INSTR_FIELD_OPCODE];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rd     = instruction[`FV_RV32_INSTR_FIELD_RD];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rs1    = instruction[`FV_RV32_INSTR_FIELD_RS1];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rs2    = instruction[`FV_RV32_INSTR_FIELD_RS2];
   wire [`FV_RV32_IMM5_WIDTH-1:0]     imm5   = instruction[`FV_RV32_INSTR_FIELD_IMM5];
   wire [`FV_RV32_IMM7_WIDTH-1:0]     imm7   = instruction[`FV_RV32_INSTR_FIELD_IMM7];
   wire [`FV_RV32_IMM12_WIDTH-1:0]    imm12  = instruction[`FV_RV32_INSTR_FIELD_IMM12];
   wire [`FV_RV32_FUNCT3_WIDTH-1:0]   funct3 = instruction[`FV_RV32_INSTR_FIELD_FUNCT3];
   wire [`FV_RV32_FUNCT7_WIDTH-1:0]   funct7 = instruction[`FV_RV32_INSTR_FIELD_FUNCT7];
`ifdef FV_INCLUDE_RV64
   wire [`FV_RV64_SHAMT_WIDTH-1:0]    shamt  = instruction[`FV_RV64_INSTR_FIELD_SHAMT];
   wire [`FV_RV64_SHAMTW_WIDTH-1:0]   shamtw = instruction[`FV_RV64_INSTR_FIELD_SHAMTW];
   wire [`FV_RV64_FUNCT6_WIDTH-1:0]   funct6 = instruction[`FV_RV64_INSTR_FIELD_FUNCT6];
`else
   wire [`FV_RV32_SHAMT_WIDTH-1:0] 	  shamt  = instruction[`FV_RV32_INSTR_FIELD_SHAMT];
`endif
`ifdef FV_INCLUDE_RVA
   wire [`FV_RV32A_FUNCT5_WIDTH-1:0]  funct5 = instruction[`FV_RV32A_INSTR_FIELD_FUNCT5];
`endif  
`ifdef FV_INCLUDE_RVZICSR
   wire [`FV_RVZICSR_IMM5_WIDTH-1:0] csr_imm5 = instruction[`FV_RVZICSR_INSTR_FIELD_IMM5];
`endif
`ifdef FV_INCLUDE_RVF
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rs3     = instruction[`FV_RVF_INSTR_FIELD_RS3];
   wire [`FV_RVF_RM_WIDTH-1:0]        rm      = instruction[`FV_RVF_INSTR_FIELD_RM];
   wire [`FV_RVF_FUNCT2_WIDTH-1:0]    funct2  = instruction[`FV_RVF_INSTR_FIELD_FUNCT2];
   wire [`FV_RVF_FUNCT12_WIDTH-1:0]   funct12 = instruction[`FV_RVF_INSTR_FIELD_FUNCT12];
`endif
`ifdef FV_INCLUDE_RVV
   wire [`FV_RVV_FUNCT6_WIDTH-1:0]    vfunct6 = instruction[`FV_RVV_INSTR_FIELD_FUNCT6];
   wire [`FV_RVV_VM_WIDTH-1:0]        vm      = instruction[`FV_RVV_INSTR_FIELD_VM];
   wire [`FV_RVV_MOP_WIDTH-1:0]       mop     = instruction[`FV_RVV_INSTR_FIELD_MOP];
`endif

   wire reg_restrict_instr_type_R;
   wire reg_restrict_instr_type_I;
   wire reg_restrict_instr_type_S; // for stores
   wire reg_restrict_instr_type_B; // for branches
   wire reg_restrict_instr_type_U; // for LUI and AUIPC
   wire reg_restrict_instr_type_J;
   wire reg_restrict_instr_type_IJ;
   wire imm_restrict_instr_type_L;
   wire imm_restrict_instr_type_S;   
`ifdef FV_INCLUDE_RVF
   wire reg_restrict_instr_type_R2_f;
   wire reg_restrict_instr_type_R3_f;
   wire reg_restrict_instr_type_R4_f;
   wire reg_restrict_instr_type_L_f;
   wire reg_restrict_instr_type_S_f;
   wire reg_restrict_instr_type_R2_f_i;  // integer rs1, FP rd
   wire reg_restrict_instr_type_R2_i_f;  // FP rs1, integer rd
   wire reg_restrict_instr_type_R3_i_ff; // FP rs1/2, integer rd
`endif

if (DECODER==1) begin
   // no restrictions if used as an instruction decoder
   assign reg_restrict_instr_type_R  = 1'b1;
   assign reg_restrict_instr_type_I  = 1'b1;
   assign reg_restrict_instr_type_S  = 1'b1;
   assign reg_restrict_instr_type_B  = 1'b1;
   assign reg_restrict_instr_type_U  = 1'b1;
   assign reg_restrict_instr_type_J  = 1'b1;
   assign reg_restrict_instr_type_IJ = 1'b1;
   assign imm_restrict_instr_type_L  = 1'b1;
   assign imm_restrict_instr_type_S  = 1'b1;   
`ifdef FV_INCLUDE_RVF
   assign reg_restrict_instr_type_R2_f    = 1'b1;
   assign reg_restrict_instr_type_R3_f    = 1'b1;
   assign reg_restrict_instr_type_R4_f    = 1'b1;
   assign reg_restrict_instr_type_L_f     = 1'b1;
   assign reg_restrict_instr_type_S_f     = 1'b1;
   assign reg_restrict_instr_type_R2_f_i  = 1'b1;
   assign reg_restrict_instr_type_R2_i_f  = 1'b1;
   assign reg_restrict_instr_type_R3_i_ff = 1'b1;
`endif
end else begin // if (DECODER==1)
   // register number restrictions for original instructions (to leave space for duplicate instructions)
   assign reg_restrict_instr_type_R  = ( FV_FUNC_orig_rd_limit(rd) && FV_FUNC_orig_rs_limit(rs1) && FV_FUNC_orig_rs_limit(rs2));
   assign reg_restrict_instr_type_I  = ( FV_FUNC_orig_rd_limit(rd) && FV_FUNC_orig_rs_limit(rs1) );
   assign reg_restrict_instr_type_S  = (                                  FV_FUNC_orig_rs_limit(rs1) && FV_FUNC_orig_rs_limit(rs2)); // for stores
   assign reg_restrict_instr_type_B  = (                                  FV_FUNC_orig_rs_limit(rs1) && FV_FUNC_orig_rs_limit(rs2)); // for branches
   assign reg_restrict_instr_type_U  = ( FV_FUNC_orig_rd_limit(rd) ); // for LUI and AUIPC
   assign reg_restrict_instr_type_J  = ( FV_FUNC_orig_rd_limit_jal(rd) );
   assign reg_restrict_instr_type_IJ = ( FV_FUNC_orig_rd_limit_jal(rd) && FV_FUNC_orig_rs_limit(rs1) );

   // immediate value restrictions
   // Note: limit to lower half of a 128B memory
   // Note: change to functions and parameterize to accomodate other memory sizes or address bits
   assign imm_restrict_instr_type_L  = 
`ifdef FV_SPLIT_RF_DMEM_SPACE
			 ((imm12[11:6] == 6'b000000) && (imm12[1:0] == 2'b00));
`else
			 1'b1; // no restrictions
`endif
   assign imm_restrict_instr_type_S  = 
`ifdef FV_SPLIT_RF_DMEM_SPACE
			 ((imm7[6:1]   == 6'b000000) && (imm5[1:0]   == 2'b00));
`else
			 1'b1; // no restrictions
`endif
   
`ifdef FV_INCLUDE_RVF
   assign reg_restrict_instr_type_R2_f = ( FV_FUNC_orig_frsd_limit(rd) && FV_FUNC_orig_frsd_limit(rs1) );
   assign reg_restrict_instr_type_R3_f = ( FV_FUNC_orig_frsd_limit(rd) && FV_FUNC_orig_frsd_limit(rs1) && FV_FUNC_orig_frsd_limit(rs2));
   assign reg_restrict_instr_type_R4_f = ( FV_FUNC_orig_frsd_limit(rd) && FV_FUNC_orig_frsd_limit(rs1) && FV_FUNC_orig_frsd_limit(rs2) && FV_FUNC_orig_frsd_limit(rs3));
   assign reg_restrict_instr_type_L_f  = ( FV_FUNC_orig_frsd_limit(rd) && FV_FUNC_orig_rs_limit(rs1) );
   assign reg_restrict_instr_type_S_f  = (                                    FV_FUNC_orig_rs_limit(rs1) && FV_FUNC_orig_frsd_limit(rs2));

   assign reg_restrict_instr_type_R2_f_i  = ( FV_FUNC_orig_frsd_limit(rd) && FV_FUNC_orig_rs_limit(rs1)   ); // integer rs1, FP rd
   assign reg_restrict_instr_type_R2_i_f  = ( FV_FUNC_orig_rd_limit(rd)   && FV_FUNC_orig_frsd_limit(rs1) ); // FP rs1, integer rd
   assign reg_restrict_instr_type_R3_i_ff = ( FV_FUNC_orig_rd_limit(rd)   && FV_FUNC_orig_frsd_limit(rs1) && FV_FUNC_orig_frsd_limit(rs2) ); // FP rs1/2, integer rd

`endif
end // else: !if(DECODER==1)

   // ========
   wire rv32i_alu_type_I = (opcode == `FV_RV_OPCODE_OP_IMM);
`ifdef FV_INCLUDE_RV64
   wire rv64i_alu_type_I32 = (opcode == `FV_RV_OPCODE_OP_IMM_32);
`endif
   
   wire instr_ADDI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB)                                        ) 
	              && (instruction != `FV_RV_INSTR_NOP) 
	              && (instruction != `FV_RV_INSTR_NOP_FLUSH) 
                      && (instruction != `FV_RV_INSTR_NOP_SYNC); // reserved for FV special use
   wire instr_SLTI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SLT)                                            );
   wire instr_SLTIU = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SLTU)                                           );
   wire instr_XORI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_XOR)                                            );
   wire instr_ORI   = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_OR)                                             );
   wire instr_ANDI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_AND)                                            );
`ifdef FV_INCLUDE_RV64
   wire instr_SLLI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SLL)     && (funct6 == `FV_RV64_FUNCT6_SLLI));
   wire instr_SRLI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct6 == `FV_RV64_FUNCT6_SRLI));
   wire instr_SRAI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct6 == `FV_RV64_FUNCT6_SRAI));
`else
   wire instr_SLLI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SLL)     && (funct7 == `FV_RV32_FUNCT7_SLLI));
   wire instr_SRLI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRLI));
   wire instr_SRAI  = rv32i_alu_type_I && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRAI));
`endif
`ifdef FV_INCLUDE_RV64
   wire instr_ADDIW = rv64i_alu_type_I32 && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB)                                        );
   wire instr_SLLIW = rv64i_alu_type_I32 && ((funct3 == `FV_RV32I_FUNCT3_SLL)     && (funct7 == `FV_RV32_FUNCT7_SLLI));
   wire instr_SRLIW = rv64i_alu_type_I32 && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRLI));
   wire instr_SRAIW = rv64i_alu_type_I32 && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRAI));
`endif

   // ========
   wire rv32i_alu_type_R = (opcode == `FV_RV_OPCODE_OP);
`ifdef FV_INCLUDE_RV64
   wire rv64i_alu_type_R32 = (opcode == `FV_RV_OPCODE_OP_32);
`endif

   wire instr_ADD  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB) && (funct7 == `FV_RV32_FUNCT7_ADD) );
   wire instr_SUB  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB) && (funct7 == `FV_RV32_FUNCT7_SUB) );
   wire instr_SLL  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_SLL)     && (funct7 == `FV_RV32_FUNCT7_SLL) );
   wire instr_SLT  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_SLT)     && (funct7 == `FV_RV32_FUNCT7_SLT) );
   wire instr_SLTU = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_SLTU)    && (funct7 == `FV_RV32_FUNCT7_SLTU));
   wire instr_XOR  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_XOR)     && (funct7 == `FV_RV32_FUNCT7_XOR) );
   wire instr_SRL  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRL) );
   wire instr_SRA  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRA) );
   wire instr_OR   = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_OR)      && (funct7 == `FV_RV32_FUNCT7_OR)  );
   wire instr_AND  = rv32i_alu_type_R && ((funct3 == `FV_RV32I_FUNCT3_AND)     && (funct7 == `FV_RV32_FUNCT7_AND) );
`ifdef FV_INCLUDE_RV64
   wire instr_ADDW = rv64i_alu_type_R32 && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB) && (funct7 == `FV_RV32_FUNCT7_ADD) );
   wire instr_SUBW = rv64i_alu_type_R32 && ((funct3 == `FV_RV32I_FUNCT3_ADD_SUB) && (funct7 == `FV_RV32_FUNCT7_SUB) );
   wire instr_SLLW = rv64i_alu_type_R32 && ((funct3 == `FV_RV32I_FUNCT3_SLL)     && (funct7 == `FV_RV32_FUNCT7_SLL) );
   wire instr_SRLW = rv64i_alu_type_R32 && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRL) );
   wire instr_SRAW = rv64i_alu_type_R32 && ((funct3 == `FV_RV32I_FUNCT3_SRL_SRA) && (funct7 == `FV_RV32_FUNCT7_SRA) );
`endif
   
   // ====
   wire rv32m_alu_type_R = (opcode == `FV_RV_OPCODE_OP) && (funct7 == `FV_RV32M_FUNCT7_MUL_DIV);
`ifdef FV_INCLUDE_RV64
   wire rv64m_alu_type_R32 = (opcode == `FV_RV_OPCODE_OP_32) && (funct7 == `FV_RV32M_FUNCT7_MUL_DIV);
`endif
   
   wire instr_MUL    = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_MUL);
   wire instr_MULH   = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_MULH);
   wire instr_MULHSU = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_MULHSU);
   wire instr_MULHU  = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_MULHU);
   wire instr_DIV    = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_DIV);
   wire instr_DIVU   = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_DIVU);
   wire instr_REM    = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_REM);
   wire instr_REMU   = rv32m_alu_type_R && (funct3 == `FV_RV32M_FUNCT3_REMU);
`ifdef FV_INCLUDE_RV64
   wire instr_MULW   = rv64m_alu_type_R32 && (funct3 == `FV_RV32M_FUNCT3_MUL);
   wire instr_DIVW   = rv64m_alu_type_R32 && (funct3 == `FV_RV32M_FUNCT3_DIV);
   wire instr_DIVUW  = rv64m_alu_type_R32 && (funct3 == `FV_RV32M_FUNCT3_DIVU);
   wire instr_REMW   = rv64m_alu_type_R32 && (funct3 == `FV_RV32M_FUNCT3_REM);
   wire instr_REMUW  = rv64m_alu_type_R32 && (funct3 == `FV_RV32M_FUNCT3_REMU);
`endif
   
   // ========
   wire rv32i_ld = (opcode == `FV_RV_OPCODE_LOAD);
  
   wire instr_LB  = rv32i_ld && (funct3 == `FV_RV32I_FUNCT3_LB);
   wire instr_LH  = rv32i_ld && (funct3 == `FV_RV32I_FUNCT3_LH);
   wire instr_LW  = rv32i_ld && (funct3 == `FV_RV32I_FUNCT3_LW);
   wire instr_LBU = rv32i_ld && (funct3 == `FV_RV32I_FUNCT3_LBU);
   wire instr_LHU = rv32i_ld && (funct3 == `FV_RV32I_FUNCT3_LHU);
`ifdef FV_INCLUDE_RV64
   wire instr_LWU = rv32i_ld && (funct3 == `FV_RV64I_FUNCT3_LWU);
   wire instr_LD  = rv32i_ld && (funct3 == `FV_RV64I_FUNCT3_LD);
`endif
   
   // ====
   wire rv32i_st = (opcode == `FV_RV_OPCODE_STORE);

   wire instr_SB = rv32i_st && (funct3 == `FV_RV32I_FUNCT3_SB);
   wire instr_SH = rv32i_st && (funct3 == `FV_RV32I_FUNCT3_SH);
   wire instr_SW = rv32i_st && (funct3 == `FV_RV32I_FUNCT3_SW);
`ifdef FV_INCLUDE_RV64
   wire instr_SD = rv32i_st && (funct3 == `FV_RV64I_FUNCT3_SD);
`endif
   
   // ========
   // jumps == plain and indirect unconditional jump

   // NOTE on: FV_EXCLUDE_DEGENERATE_JAL
   // Even if branch prediction is disabled; a JAL/R to PC+4 can be seen as correct prediction and avoid asserting pipeline kill,
   // so provide the option of avoiding this degenerate case so CF properties can be active
   wire instr_JAL  = (opcode == `FV_RV_OPCODE_JAL)  && reg_restrict_instr_type_J &&
`ifdef FV_EXCLUDE_DEGENERATE_JAL
	(instruction[31:12] != 20'h00400) &&
`endif
	1'b1;

   wire instr_JALR = (opcode == `FV_RV_OPCODE_JALR) && reg_restrict_instr_type_IJ && (funct3 == 3'b0) &&
`ifdef FV_EXCLUDE_DEGENERATE_JAL
	(instruction[31:20] != 12'h004) &&
`endif
	1'b1;
   
   // ========
   // branches == conditional jumps/branches
   wire rv32i_branch = (opcode == `FV_RV_OPCODE_BRANCH);

   wire instr_BEQ  = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BEQ) ;
   wire instr_BNE  = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BNE) ;
   wire instr_BLT  = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BLT) ;
   wire instr_BGE  = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BGE) ;
   wire instr_BLTU = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BLTU);
   wire instr_BGEU = rv32i_branch && (funct3 == `FV_RV32I_FUNCT3_BGEU);

   // ========
   wire instr_LUI   = (opcode == `FV_RV_OPCODE_LUI);
   wire instr_AUIPC = (opcode == `FV_RV_OPCODE_AUIPC);

   // ========
   wire rv32i_misc_mem = (opcode == `FV_RV_OPCODE_MISC_MEM) && 
                         (rd  == `FV_RV32_REG_ADDR_WIDTH'b0) && 
                         (rs1 == `FV_RV32_REG_ADDR_WIDTH'b0);

   wire instr_FENCE   = rv32i_misc_mem && (funct3 == `FV_RV32I_FUNCT3_FENCE)   && (imm12[11:8] == 4'b0);
   // FENCE.I was removed from RV32I to Zifencei instruction extension
   // Note: create a separate define for ifdef'ing?
   wire instr_FENCE_I = rv32i_misc_mem && (funct3 == `FV_RV32I_FUNCT3_FENCE_I) && (imm12 == `FV_RV32_IMM12_WIDTH'b0);
   
`ifdef FV_INCLUDE_RVA

   // NOTE: no restrictions on aq/rl fields valid value combinations
   wire rv32a_w = (opcode == `FV_RV_OPCODE_AMO) && (funct3 == `FV_RV32A_FUNCT3_W);
   wire rv64a_d = (opcode == `FV_RV_OPCODE_AMO) && (funct3 == `FV_RV64A_FUNCT3_D);

   wire instr_LRW      = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_LR) && (rs2 == 0);
   wire instr_SCW      = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_SC);
   wire instr_AMOSWAPW = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOSWAP);
   wire instr_AMOADDW  = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOADD);
   wire instr_AMOXORW  = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOXOR);
   wire instr_AMOANDW  = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOAND);
   wire instr_AMOORW   = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOOR);
   wire instr_AMOMINW  = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOMIN);
   wire instr_AMOMAXW  = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOMAX);
   wire instr_AMOMINUW = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOMINU);
   wire instr_AMOMAXUW = rv32a_w && (funct5 == `FV_RV32A_FUNCT5_AMOMAXU);

 `ifdef FV_INCLUDE_RV64
   wire instr_LRD      = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_LR) && (rs2 == 0);
   wire instr_SCD      = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_SC);
   wire instr_AMOSWAPD = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOSWAP);
   wire instr_AMOADDD  = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOADD);
   wire instr_AMOXORD  = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOXOR);
   wire instr_AMOANDD  = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOAND);
   wire instr_AMOORD   = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOOR);
   wire instr_AMOMIND  = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOMIN);
   wire instr_AMOMAXD  = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOMAX);
   wire instr_AMOMINUD = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOMINU);
   wire instr_AMOMAXUD = rv64a_d && (funct5 == `FV_RV32A_FUNCT5_AMOMAXU);
 `endif //  `ifdef FV_INCLUDE_RV64
`endif //  `ifdef FV_INCLUDE_RVA
		    
`ifdef FV_INCLUDE_RVZICSR
   wire instr_CSRRW    = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRW);
   wire instr_CSRRS    = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRS);
   wire instr_CSRRC    = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRC);
   wire instr_CSRRWI   = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRWI);
   wire instr_CSRRSI   = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRSI);
   wire instr_CSRRCI   = (opcode == `FV_RV_OPCODE_SYSTEM) && (funct3 == `FV_RV32I_FUNCT3_CSRRCI);
`endif
   
   // ========
   wire instr_ECALL  = (instruction == `FV_RV_INSTR_ECALL);
   wire instr_EBREAK = (instruction == `FV_RV_INSTR_EBREAK);

`ifdef FV_INCLUDE_RVF

   // the following are common among RVF/D/Q
   wire rvf_instr_rm            = (rm != `FV_RVF_FUNCT3_RM_RESRV1) && (rm != `FV_RVF_FUNCT3_RM_RESRV2);

   wire rvf_instr_load          = (opcode == `FV_RV_OPCODE_LOAD_FP)  && reg_restrict_instr_type_L_f;
   wire rvf_instr_store         = (opcode == `FV_RV_OPCODE_STORE_FP) && reg_restrict_instr_type_S_f;

   wire rvf_instr_type_R3        = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R3_f;   
   wire rvf_instr_type_R3_i_ff   = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R3_i_ff;   
   wire rvf_instr_type_R3_rm     = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R3_f  && rvf_instr_rm;
   wire rvf_instr_type_R2_rm     = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R2_f  && rvf_instr_rm;
   wire rvf_instr_type_R2_f_i    = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R2_f_i;
   wire rvf_instr_type_R2_i_f    = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R2_i_f;
   wire rvf_instr_type_R2_f_i_rm = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R2_f_i && rvf_instr_rm;
   wire rvf_instr_type_R2_i_f_rm = (opcode == `FV_RV_OPCODE_OP_FP) && reg_restrict_instr_type_R2_i_f && rvf_instr_rm;

   // the following are next to each other just for clarity (instead of being behind ifdef RVD/Q)
   wire rvf_instr_type_R4       = reg_restrict_instr_type_R4_f && rvf_instr_rm && (funct2 == `FV_RVF_FUNCT2_SINGLE);
   wire rvd_instr_type_R4       = reg_restrict_instr_type_R4_f && rvf_instr_rm && (funct2 == `FV_RVD_FUNCT2_DOUBLE);
   wire rvq_instr_type_R4       = reg_restrict_instr_type_R4_f && rvf_instr_rm && (funct2 == `FV_RVQ_FUNCT2_QUAD);

   // ==================
   // RV32F instructions
   wire instr_FLW       = rvf_instr_load  && (funct3 == `FV_RVF_FUNCT3_FLW);
   wire instr_FSW       = rvf_instr_store && (funct3 == `FV_RVF_FUNCT3_FSW);
   
   wire instr_FMADDS    = (opcode == `FV_RV_OPCODE_MADD)  && rvf_instr_type_R4;
   wire instr_FMSUBS    = (opcode == `FV_RV_OPCODE_MSUB)  && rvf_instr_type_R4;
   wire instr_FNMSUBS   = (opcode == `FV_RV_OPCODE_NMSUB) && rvf_instr_type_R4;
   wire instr_FNMADDS   = (opcode == `FV_RV_OPCODE_NMADD) && rvf_instr_type_R4;

   wire instr_FADDS     = (funct7  == (`FV_RVF_FUNCT7_FADD     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_rm;
   wire instr_FSUBS     = (funct7  == (`FV_RVF_FUNCT7_FSUB     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_rm;
   wire instr_FMULS     = (funct7  == (`FV_RVF_FUNCT7_FMUL     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_rm;
   wire instr_FDIVS     = (funct7  == (`FV_RVF_FUNCT7_FDIV     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_rm;

   wire instr_FSQRTS    = (funct12 == (`FV_RVF_FUNCT12_FSQRT   | `FV_RVF_FUNCT12_SINGLE)) && rvf_instr_type_R2_rm;
   wire instr_FSGNJS    = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJ);
   wire instr_FSGNJNS   = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJN);
   wire instr_FSGNJXS   = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJX);
   wire instr_FMINS     = (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_MIN);
   wire instr_FMAXS     = (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_MAX);
   wire instr_FCVTWS    = (funct12 ==  `FV_RVF_FUNCT12_FCVTWS                               ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTWUS   = (funct12 ==  `FV_RVF_FUNCT12_FCVTWUS                              ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FMVXW     = (funct12 ==  `FV_RVF_FUNCT12_FMVXW                                ) && rvf_instr_type_R2_i_f  && (funct3 == `FV_RVF_FUNCT3_FMV);
   wire instr_FEQS      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FEQ);
   wire instr_FLTS      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FLT);
   wire instr_FLES      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVF_FUNCT7_SINGLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FLE);
   wire instr_FCLASSS   = (funct12 == (`FV_RVF_FUNCT12_FCLASS  | `FV_RVF_FUNCT12_SINGLE)) && rvf_instr_type_R2_i_f  && (funct3 == `FV_RVF_FUNCT3_FCLASS);
   wire instr_FCVTSW    = (funct12 ==  `FV_RVF_FUNCT12_FCVTSW                               ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FCVTSWU   = (funct12 ==  `FV_RVF_FUNCT12_FCVTSWU                              ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FMVWX     = (funct12 ==  `FV_RVF_FUNCT12_FMVWX                                ) && rvf_instr_type_R2_f_i  && (funct3 == `FV_RVF_FUNCT3_FMV);
  
   // ==================
   // RV64F instructions
 `ifdef FV_INCLUDE_RV64
   wire instr_FCVTLS    = (funct12 == `FV_RVF_FUNCT12_FCVTLS                                ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTLUS   = (funct12 == `FV_RVF_FUNCT12_FCVTLUS                               ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTSL    = (funct12 == `FV_RVF_FUNCT12_FCVTSL                                ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FCVTSLU   = (funct12 == `FV_RVF_FUNCT12_FCVTSLU                               ) && rvf_instr_type_R2_f_i_rm;
 `endif

   // ==================
   // RV32D instructions
 `ifdef FV_INCLUDE_RVD
   wire instr_FLD       = rvf_instr_load  && (funct3 == `FV_RVD_FUNCT3_FLD);
   wire instr_FSD       = rvf_instr_store && (funct3 == `FV_RVD_FUNCT3_FSD);

   wire instr_FMADDD    = (opcode == `FV_RV_OPCODE_MADD)  && rvd_instr_type_R4;
   wire instr_FMSUBD    = (opcode == `FV_RV_OPCODE_MSUB)  && rvd_instr_type_R4;
   wire instr_FNMSUBD   = (opcode == `FV_RV_OPCODE_NMSUB) && rvd_instr_type_R4;
   wire instr_FNMADDD   = (opcode == `FV_RV_OPCODE_NMADD) && rvd_instr_type_R4;

   wire instr_FADDD     = (funct7  == (`FV_RVF_FUNCT7_FADD     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_rm;
   wire instr_FSUBD     = (funct7  == (`FV_RVF_FUNCT7_FSUB     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_rm;
   wire instr_FMULD     = (funct7  == (`FV_RVF_FUNCT7_FMUL     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_rm;
   wire instr_FDIVD     = (funct7  == (`FV_RVF_FUNCT7_FDIV     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_rm;

   wire instr_FSQRTD    = (funct12 == (`FV_RVF_FUNCT12_FSQRT   | `FV_RVD_FUNCT12_DOUBLE)) && rvf_instr_type_R2_rm;
   wire instr_FSGNJD    = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJ);
   wire instr_FSGNJND   = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJN);
   wire instr_FSGNJXD   = (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_SGNJX);
   wire instr_FMIND     = (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_MIN);
   wire instr_FMAXD     = (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3      && (funct3 == `FV_RVF_FUNCT3_MAX);
   wire instr_FCVTSD    = (funct12 ==  `FV_RVD_FUNCT12_FCVTSD                               ) && rvf_instr_type_R2_rm;
   wire instr_FCVTDS    = (funct12 ==  `FV_RVD_FUNCT12_FCVTDS                               ) && rvf_instr_type_R2_rm;
   wire instr_FEQD      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FEQ);
   wire instr_FLTD      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FLT);
   wire instr_FLED      = (funct7  == (`FV_RVF_FUNCT7_FCMP     | `FV_RVD_FUNCT7_DOUBLE) ) && rvf_instr_type_R3_i_ff && (funct3 == `FV_RVF_FUNCT3_FLE);
   wire instr_FCLASSD   = (funct12 == (`FV_RVF_FUNCT12_FCLASS  | `FV_RVD_FUNCT12_DOUBLE)) && rvf_instr_type_R2_i_f  && (funct3 == `FV_RVF_FUNCT3_FCLASS);
   wire instr_FCVTWD    = (funct12 ==  `FV_RVD_FUNCT12_FCVTWD                               ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTWUD   = (funct12 ==  `FV_RVD_FUNCT12_FCVTWUD                              ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTDW    = (funct12 ==  `FV_RVD_FUNCT12_FCVTDW                               ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FCVTDWU   = (funct12 ==  `FV_RVD_FUNCT12_FCVTDWU                              ) && rvf_instr_type_R2_f_i_rm;
   
   // ==================
   // RV64D instructions
  `ifdef FV_INCLUDE_RV64
   wire instr_FCVTLD    = (funct12 == `FV_RVD_FUNCT12_FCVTLD                                ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FCVTLUD   = (funct12 == `FV_RVD_FUNCT12_FCVTLUD                               ) && rvf_instr_type_R2_i_f_rm;
   wire instr_FMVXD     = (funct12 == `FV_RVD_FUNCT12_FMVXD                                 ) && rvf_instr_type_R2_i_f  && (funct3 == `FV_RVF_FUNCT3_FMV);
   wire instr_FCVTDL    = (funct12 == `FV_RVD_FUNCT12_FCVTDL                                ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FCVTDLU   = (funct12 == `FV_RVD_FUNCT12_FCVTDLU                               ) && rvf_instr_type_R2_f_i_rm;
   wire instr_FMVDX     = (funct12 == `FV_RVD_FUNCT12_FMVDX                                 ) && rvf_instr_type_R2_f_i  && (funct3 == `FV_RVF_FUNCT3_FMV);
  `endif
 `endif //  `ifdef FV_INCLUDE_RVD
`endif //  `ifdef FV_INCLUDE_RVF

   // ==================
   // RV vector instructions
`ifdef FV_INCLUDE_RVV

//   wire rvv_instr_type_R3        = (opcode == `FV_RV_OPCODE_RVV) && reg_restrict_instr_type_R3_f;
   wire reg_restrict_instr_type_R3_v = ( FV_FUNC_orig_frsd_limit(rd) &&
					 (rd != 0) &&
					 FV_FUNC_orig_frsd_limit(rs1) && 
					 FV_FUNC_orig_frsd_limit(rs2));
   wire rvv_temp        = (opcode == `FV_RV_OPCODE_RVV) && reg_restrict_instr_type_R3_v && (funct3 == `FV_RVV_FUNCT3_OPIVV);   

   wire instr_VADD = (vfunct6  == `FV_RVV_FUNCT6_VADD) && rvv_temp && (
`ifdef FV_RVV_SUPPORT_UNMASKED
									   (vm == `FV_RVV_VM_UNMASKED) ||
`endif
									   (vm == `FV_RVV_VM_MASKED));
   
`endif

endmodule // FV_instructions

