
module FV_CORE_IF_dup ( input logic clk,
			    input logic [`FV_INSTR_WIDTH-1:0]  instr_in,
			    output logic [`FV_INSTR_WIDTH-1:0] instr_out
			    );

   logic [`FV_INSTR_WIDTH-1:0] instr_in_32;
   
`ifdef FV_INCLUDE_RVC
   logic 			   illegal_rvc, is_compressed;

   FV_CORE_decomp_rvc decomp_rvc(.instr_i(instr_in),
				     .instr_o(instr_in_32),
				     .illegal_instr_o(illegal_rvc),
				     .is_compressed_o(is_compressed)
				     );

 `ifndef FV_ILLEGAL_RVC_INSTR_ALLOWED
   FV_no_illegal_rvc_instr:    assume property (@(posedge clk) (is_compressed == 1) |-> (instr_in != 32'b0));
   FV_SC_no_illegal_rvc_instr: assert property (@(posedge clk) (is_compressed == 1) |-> (illegal_rvc == 0));
 `endif

`else // !`ifdef FV_INCLUDE_RVC
   assign instr_in_32 = instr_in;
`endif // !`ifdef FV_INCLUDE_RVC
   
   // ===========
   // decode
   
   logic [`FV_RV32_OPCODE_WIDTH-1:0]   opcode; assign opcode = instr_in_32[`FV_RV32_INSTR_FIELD_OPCODE];
   logic [`FV_RV32_REG_ADDR_WIDTH-1:0] rd;     assign rd     = instr_in_32[`FV_RV32_INSTR_FIELD_RD];
   logic [`FV_RV32_REG_ADDR_WIDTH-1:0] rs1;    assign rs1    = instr_in_32[`FV_RV32_INSTR_FIELD_RS1];
   logic [`FV_RV32_REG_ADDR_WIDTH-1:0] rs2;    assign rs2    = instr_in_32[`FV_RV32_INSTR_FIELD_RS2];
   logic [`FV_RV32_IMM5_WIDTH-1:0]     imm5;   assign imm5   = instr_in_32[`FV_RV32_INSTR_FIELD_IMM5];
   logic [`FV_RV32_IMM7_WIDTH-1:0]     imm7;   assign imm7   = instr_in_32[`FV_RV32_INSTR_FIELD_IMM7];
   logic [`FV_RV32_IMM12_WIDTH-1:0]    imm12;  assign imm12  = instr_in_32[`FV_RV32_INSTR_FIELD_IMM12];
   logic [`FV_RV32_SHAMT_WIDTH-1:0]    shamt;  assign shamt  = instr_in_32[`FV_RV32_INSTR_FIELD_SHAMT];
   logic [`FV_RV32_FUNCT3_WIDTH-1:0]   funct3; assign funct3 = instr_in_32[`FV_RV32_INSTR_FIELD_FUNCT3];
   logic [`FV_RV32_FUNCT7_WIDTH-1:0]   funct7; assign funct7 = instr_in_32[`FV_RV32_INSTR_FIELD_FUNCT7];
   // funct12 is used in both RVF and RVV
   logic [`FV_RVF_FUNCT12_WIDTH-1:0]   funct12; assign funct12 = instr_in_32[`FV_RVF_INSTR_FIELD_FUNCT12];

   logic 				   dcd_lw;
   logic 				   dcd_sw;
   logic 				   dcd_aluimm;
   logic 				   dcd_alureg; // includes mul/div instructions
   logic 				   dcd_jump;
   logic 				   dcd_jump_indirect;
   logic 				   dcd_branch;
   logic 				   dcd_lui;
   logic 				   dcd_auipc;
   logic 				   dcd_amo;

   assign dcd_lw    = (opcode == `FV_RV_OPCODE_LOAD) &&
                      (
		       (funct3 == `FV_RV32I_FUNCT3_LB)  ||
		       (funct3 == `FV_RV32I_FUNCT3_LH)  ||
		       (funct3 == `FV_RV32I_FUNCT3_LW)  ||
		       (funct3 == `FV_RV32I_FUNCT3_LBU) ||
		       (funct3 == `FV_RV32I_FUNCT3_LHU) ||
`ifdef FV_INCLUDE_RV64
		       (funct3 == `FV_RV64I_FUNCT3_LWU) ||
		       (funct3 == `FV_RV64I_FUNCT3_LD) ||
`endif
		       1'b0
		      );
   
   assign dcd_sw    = (opcode == `FV_RV_OPCODE_STORE) &&
		      (
		       (funct3 == `FV_RV32I_FUNCT3_SB)  ||
		       (funct3 == `FV_RV32I_FUNCT3_SH)  ||
		       (funct3 == `FV_RV32I_FUNCT3_SW)  ||
`ifdef FV_INCLUDE_RV64
		       (funct3 == `FV_RV64I_FUNCT3_SD) ||
`endif
		       1'b0
		      );
      
   assign dcd_aluimm = (opcode == `FV_RV_OPCODE_OP_IMM) ||
`ifdef FV_INCLUDE_RV64
		       (opcode == `FV_RV_OPCODE_OP_IMM_32) ||
`endif
		       1'b0;

   assign dcd_alureg = (opcode == `FV_RV_OPCODE_OP) ||
`ifdef FV_INCLUDE_RV64
		       (opcode == `FV_RV_OPCODE_OP_32) ||
`endif
		       1'b0;
   assign dcd_jump          = (opcode == `FV_RV_OPCODE_JAL);
   assign dcd_jump_indirect = (opcode == `FV_RV_OPCODE_JALR);
   assign dcd_branch        = (opcode == `FV_RV_OPCODE_BRANCH);

   assign dcd_lui           = (opcode == `FV_RV_OPCODE_LUI);
   assign dcd_auipc         = (opcode == `FV_RV_OPCODE_AUIPC);

   logic  dcd_scalar_ldstamo_f;
   assign dcd_scalar_ldstamo_f  = (funct3 == `FV_RVF_FUNCT3_FLH) ||
	                          (funct3 == `FV_RVF_FUNCT3_FLW) ||
	                          (funct3 == `FV_RVD_FUNCT3_FLD) ||
	                          (funct3 == `FV_RVQ_FUNCT3_FLQ);
	
   assign dcd_amo           = (opcode == `FV_RV_OPCODE_AMO) && dcd_scalar_ldstamo_f;

`ifdef FV_INCLUDE_RVF
   logic dcd_rvf_type_R2_f;
   logic dcd_rvf_type_R3_f;
   logic dcd_rvf_type_R4_f;
   logic dcd_rvf_type_R2_f_i;
   logic dcd_rvf_type_R2_i_f;
   logic dcd_rvf_type_R3_i_ff;
   logic dcd_rvf_type_L_f;
   logic dcd_rvf_type_S_f;

   logic [`FV_RV32_REG_ADDR_WIDTH-1:0] rs3;     assign rs3     = instr_in_32[`FV_RVF_INSTR_FIELD_RS3];
   logic [`FV_RVF_RM_WIDTH-1:0]        rm;      assign rm      = instr_in_32[`FV_RVF_INSTR_FIELD_RM];
   logic [`FV_RVF_FUNCT2_WIDTH-1:0]    funct2;  assign funct2  = instr_in_32[`FV_RVF_INSTR_FIELD_FUNCT2];

   assign dcd_rvf_type_R2_f = (opcode == `FV_RV_OPCODE_OP_FP) && 
			      ((funct12 == (`FV_RVF_FUNCT12_FSQRT | `FV_RVF_FUNCT12_SINGLE)) ||
			       (funct12 == (`FV_RVF_FUNCT12_FSQRT | `FV_RVD_FUNCT12_DOUBLE)) ||
			       (funct12 == `FV_RVD_FUNCT12_FCVTSD) ||
			       (funct12 == `FV_RVD_FUNCT12_FCVTDS));

   assign dcd_rvf_type_R3_f = (opcode == `FV_RV_OPCODE_OP_FP) && 
			      ((funct7  == (`FV_RVF_FUNCT7_FADD     | `FV_RVF_FUNCT7_SINGLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FSUB     | `FV_RVF_FUNCT7_SINGLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FMUL     | `FV_RVF_FUNCT7_SINGLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FDIV     | `FV_RVF_FUNCT7_SINGLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVF_FUNCT7_SINGLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVF_FUNCT7_SINGLE)) || 
			       (funct7  == (`FV_RVF_FUNCT7_FADD     | `FV_RVD_FUNCT7_DOUBLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FSUB     | `FV_RVD_FUNCT7_DOUBLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FMUL     | `FV_RVD_FUNCT7_DOUBLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FDIV     | `FV_RVD_FUNCT7_DOUBLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FSGNJ    | `FV_RVD_FUNCT7_DOUBLE)) ||
			       (funct7  == (`FV_RVF_FUNCT7_FMIN_MAX | `FV_RVD_FUNCT7_DOUBLE)) || 
			       1'b0);

   assign dcd_rvf_type_R4_f = (opcode == `FV_RV_OPCODE_MADD)  ||
			      (opcode == `FV_RV_OPCODE_MSUB)  ||
			      (opcode == `FV_RV_OPCODE_NMSUB) ||
			      (opcode == `FV_RV_OPCODE_NMADD);

   assign dcd_rvf_type_R2_f_i = (opcode == `FV_RV_OPCODE_OP_FP) && 
			        ( (funct12 == `FV_RVF_FUNCT12_FCVTSW)  ||
			 	  (funct12 == `FV_RVF_FUNCT12_FCVTSWU) ||
				 ((funct12 == `FV_RVF_FUNCT12_FMVWX) && (funct3 == `FV_RVF_FUNCT3_FMV)) ||
				  (funct12 == `FV_RVF_FUNCT12_FCVTSL)  ||
				  (funct12 == `FV_RVF_FUNCT12_FCVTSLU) ||
				  (funct12 == `FV_RVD_FUNCT12_FCVTDW)  ||
				  (funct12 == `FV_RVD_FUNCT12_FCVTDWU) ||
				  (funct12 == `FV_RVD_FUNCT12_FCVTDL)  ||
				  (funct12 == `FV_RVD_FUNCT12_FCVTDLU) ||
				 ((funct12 == `FV_RVD_FUNCT12_FMVDX) && (funct3 == `FV_RVF_FUNCT3_FMV)));
   
   assign dcd_rvf_type_R2_i_f = (opcode == `FV_RV_OPCODE_OP_FP) && 
			        ( (funct12 ==  `FV_RVF_FUNCT12_FCVTWS)  ||
				  (funct12 ==  `FV_RVF_FUNCT12_FCVTWUS) ||
				 ((funct12 ==  `FV_RVF_FUNCT12_FMVXW                               ) && (funct3 == `FV_RVF_FUNCT3_FMV))    ||
				 ((funct12 == (`FV_RVF_FUNCT12_FCLASS | `FV_RVF_FUNCT12_SINGLE)) && (funct3 == `FV_RVF_FUNCT3_FCLASS)) ||
				  (funct12 ==  `FV_RVF_FUNCT12_FCVTLS)  ||
				  (funct12 ==  `FV_RVF_FUNCT12_FCVTLUS) ||
				 ((funct12 == (`FV_RVF_FUNCT12_FCLASS | `FV_RVD_FUNCT12_DOUBLE)) && (funct3 == `FV_RVF_FUNCT3_FCLASS)) ||
				  (funct12 ==  `FV_RVD_FUNCT12_FCVTWD)  ||
				  (funct12 ==  `FV_RVD_FUNCT12_FCVTWUD) ||
				  (funct12 ==  `FV_RVD_FUNCT12_FCVTLD)  ||
				  (funct12 ==  `FV_RVD_FUNCT12_FCVTLUD) ||
				 ((funct12 ==  `FV_RVD_FUNCT12_FMVXD                               ) && (funct3 == `FV_RVF_FUNCT3_FMV))    ||
			        1'b0);

   assign dcd_rvf_type_R3_i_ff = (opcode == `FV_RV_OPCODE_OP_FP) && 
				 ((funct7  == (`FV_RVF_FUNCT7_FCMP | `FV_RVF_FUNCT7_SINGLE)) ||
				  (funct7  == (`FV_RVF_FUNCT7_FCMP | `FV_RVD_FUNCT7_DOUBLE)));

   assign dcd_rvf_type_L_f  = (opcode == `FV_RV_OPCODE_LOAD_FP)  && dcd_scalar_ldstamo_f;
   assign dcd_rvf_type_S_f  = (opcode == `FV_RV_OPCODE_STORE_FP) && dcd_scalar_ldstamo_f;
`endif //  `ifdef FV_INCLUDE_RVF

`ifdef FV_INCLUDE_RVV
   logic dcd_rvv_type_VL_unit_stride;
   logic dcd_rvv_type_VL_strided;
   logic dcd_rvv_type_VL_indexed;
   logic dcd_rvv_type_VS_unit_stride;
   logic dcd_rvv_type_VS_strided;
   logic dcd_rvv_type_VS_indexed;

   logic dcd_rvv_vamo;

   logic dcd_rvv_opivv;
   logic dcd_rvv_opfvv;
   logic dcd_rvv_opmvv;
   logic dcd_rvv_opivi;
   logic dcd_rvv_opivx;
   logic dcd_rvv_opfvf;
   logic dcd_rvv_opmvx;

   logic dcd_rvv_setvl;

   wire [`FV_RVV_MOP_WIDTH-1:0] mop = instr_in_32[`FV_RVV_INSTR_FIELD_MOP];
   
   assign dcd_rvv_type_VL_unit_stride  = (opcode == `FV_RV_OPCODE_LOAD_FP)  && (!dcd_scalar_ldstamo_f) &&  (mop == `FV_RVV_MOP_UNIT_STRIDE);
   assign dcd_rvv_type_VL_strided      = (opcode == `FV_RV_OPCODE_LOAD_FP)  && (!dcd_scalar_ldstamo_f) &&  (mop == `FV_RVV_MOP_STRIDED);
   assign dcd_rvv_type_VL_indexed      = (opcode == `FV_RV_OPCODE_LOAD_FP)  && (!dcd_scalar_ldstamo_f) && ((mop == `FV_RVV_MOP_INDEXED_UNORDERED) ||
												               (mop == `FV_RVV_MOP_INDEXED_ORDERED));

   assign dcd_rvv_type_VS_unit_stride  = (opcode == `FV_RV_OPCODE_STORE_FP) && (!dcd_scalar_ldstamo_f) &&  (mop == `FV_RVV_MOP_UNIT_STRIDE);
   assign dcd_rvv_type_VS_strided      = (opcode == `FV_RV_OPCODE_STORE_FP) && (!dcd_scalar_ldstamo_f) &&  (mop == `FV_RVV_MOP_STRIDED);
   assign dcd_rvv_type_VS_indexed      = (opcode == `FV_RV_OPCODE_STORE_FP) && (!dcd_scalar_ldstamo_f) && ((mop == `FV_RVV_MOP_INDEXED_UNORDERED) ||
												               (mop == `FV_RVV_MOP_INDEXED_ORDERED));

   assign dcd_rvv_vamo  = (opcode == `FV_RV_OPCODE_AMO) && (!dcd_scalar_ldstamo_f);

   assign dcd_rvv_opivv = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPIVV);
   assign dcd_rvv_opfvv = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPFVV);
   assign dcd_rvv_opmvv = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPMVV);
   assign dcd_rvv_opivi = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPIVI);
   assign dcd_rvv_opivx = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPIVX);
   assign dcd_rvv_opfvf = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPFVF);
   assign dcd_rvv_opmvx = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_OPMVX);
      
   assign dcd_rvv_setvl = (opcode == `FV_RV_OPCODE_RVV) && (funct3 == `FV_RVV_FUNCT3_SETVL);

`endif

   // ===========
   // change the instruction fields
   
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_lw;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_sw;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_alureg;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_aluimm;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_jump;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_jump_indirect;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_branch;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_lui_auipc;
   wire [`FV_INSTR_WIDTH-1:0]   dup_instr_amo;

   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_rd;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_rs1;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_rs2;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] amo_rs1;
   wire [`FV_RV32_IMM7_WIDTH-1:0]     dup_imm7;
   wire [`FV_RV32_IMM12_WIDTH-1:0]    dup_imm12;

   assign dup_rd  = FV_FUNC_dup_reg(rd);
   assign dup_rs1 = FV_FUNC_dup_reg(rs1);
   assign dup_rs2 = FV_FUNC_dup_reg(rs2);
   assign amo_rs1 = `FV_DUP_R0P;
   
// limit to upper half of a 128B memory
// Note: accomodate any memory size
   assign dup_imm12 = {6'b000001, imm12[5:0]};
   assign dup_imm7 =  {6'b000001, imm7[0:0]};  // signed bit is always zero for lw,sw instructions
   
   assign dup_instr_lw            = {dup_imm12,         dup_rs1, funct3, dup_rd, opcode};
   assign dup_instr_sw            = {dup_imm7, dup_rs2, dup_rs1, funct3, imm5,   opcode};
   assign dup_instr_aluimm        = {imm12,             dup_rs1, funct3, dup_rd, opcode};
   assign dup_instr_alureg        = {funct7,   dup_rs2, dup_rs1, funct3, dup_rd, opcode};
   assign dup_instr_jump          = {instr_in_32[31:12],                 dup_rd, opcode}; // for JAL (same as LUI/AUIPC but keep separate in case they differ)
   assign dup_instr_jump_indirect = {imm12,             dup_rs1, funct3, dup_rd, opcode}; // for JALR (jump_indirect)
   assign dup_instr_branch        = {imm7,     dup_rs2, dup_rs1, funct3, imm5,   opcode};
   assign dup_instr_lui_auipc     = {instr_in_32[31:12],                 dup_rd, opcode}; // same for LUI and AUIPC

// Note: temporarily use R0 only for rs1 and R0P for rs1 of dup instr
   assign dup_instr_amo           = {funct7,   dup_rs2, amo_rs1, funct3, dup_rd, opcode};

   wire 				  dcd_rvf;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr;
   wire 				  dcd_rvv;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr;
 				  
`ifdef FV_INCLUDE_RVF
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R2_f;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R3_f;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R4_f;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R2_f_i;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R2_i_f;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_R3_i_ff;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_L_f;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvf_instr_S_f;

   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_frd;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_frs1;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_frs2;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_frs3;

   assign dup_frd  = FV_FUNC_dup_freg(rd);
   assign dup_frs1 = FV_FUNC_dup_freg(rs1);
   assign dup_frs2 = FV_FUNC_dup_freg(rs2);
   assign dup_frs3 = FV_FUNC_dup_freg(rs3);
   
   assign dup_rvf_instr_R2_f    = {funct12,                    dup_frs1, funct3, dup_frd, opcode};
   assign dup_rvf_instr_R3_f    = {funct7,           dup_frs2, dup_frs1, funct3, dup_frd, opcode};
   assign dup_rvf_instr_R4_f    = {dup_frs3, funct2, dup_frs2, dup_frs1, funct3, dup_frd, opcode};
   assign dup_rvf_instr_R2_f_i  = {funct12,                    dup_rs1,  funct3, dup_frd, opcode};
   assign dup_rvf_instr_R2_i_f  = {funct12,                    dup_frs1, funct3, dup_rd,  opcode};
   assign dup_rvf_instr_R3_i_ff = {funct7,           dup_frs2, dup_frs1, funct3, dup_rd,  opcode};
   assign dup_rvf_instr_L_f     = {dup_imm12,                  dup_rs1,  funct3, dup_frd, opcode};
   assign dup_rvf_instr_S_f     = {dup_imm7,         dup_frs2, dup_rs1,  funct3, imm5,    opcode};

   assign dcd_rvf = dcd_rvf_type_R2_f ||
		    dcd_rvf_type_R3_f ||
		    dcd_rvf_type_R4_f ||
		    dcd_rvf_type_R2_f_i ||
		    dcd_rvf_type_R2_i_f ||
		    dcd_rvf_type_R3_i_ff ||
		    dcd_rvf_type_L_f ||
		    dcd_rvf_type_S_f;

   assign dup_rvf_instr =  dcd_rvf_type_R2_f    ? dup_rvf_instr_R2_f    :
			  (dcd_rvf_type_R3_f    ? dup_rvf_instr_R3_f    :
			  (dcd_rvf_type_R4_f    ? dup_rvf_instr_R4_f    :
			  (dcd_rvf_type_R2_f_i  ? dup_rvf_instr_R2_f_i  :
			  (dcd_rvf_type_R2_i_f  ? dup_rvf_instr_R2_i_f  :
			  (dcd_rvf_type_R3_i_ff ? dup_rvf_instr_R3_i_ff :
			  (dcd_rvf_type_L_f     ? dup_rvf_instr_L_f     :
			  (dcd_rvf_type_S_f     ? dup_rvf_instr_S_f     :
			   instr_in_32)))))));

`else // !`ifdef FV_INCLUDE_RVF
   assign dcd_rvf       =  0;
   assign dup_rvf_instr = '0; // don't care
`endif

`ifdef FV_INCLUDE_RVV
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VL_unit_stride;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VL_strided;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VL_indexed;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VS_unit_stride;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VS_strided;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_type_VS_indexed;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_vamo;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opivv;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opfvv;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opmvv;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opivi;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opivx;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opfvf;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_opmvx;
   wire [`FV_INSTR_WIDTH-1:0] 	  dup_rvv_instr_setvl;

   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_vrd;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_vrs1;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_vrs2;
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] dup_vrs3, vrs3;

   assign vrs3     = rd; // same instruction field
   assign dup_vrd  = FV_FUNC_dup_vreg(rd);
   assign dup_vrs1 = FV_FUNC_dup_vreg(rs1);
   assign dup_vrs2 = FV_FUNC_dup_vreg(rs2);
   assign dup_vrs3 = FV_FUNC_dup_vreg(vrs3);
   
   // Note0: vector ld/st DUP memory address split scheme needs to be devised and implemeted
   assign dup_rvv_instr_type_VL_unit_stride = {funct12,           dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_type_VL_strided     = {funct7,  dup_rs2,  dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_type_VL_indexed     = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_type_VS_unit_stride = {funct12,           dup_rs1,  funct3, dup_vrs3, opcode};
   assign dup_rvv_instr_type_VS_strided     = {funct7,  dup_rs2,  dup_rs1,  funct3, dup_vrs3, opcode};
   assign dup_rvv_instr_type_VS_indexed     = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrs3, opcode};
   assign dup_rvv_instr_vamo                = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opivv               = {funct7,  dup_vrs2, dup_vrs1, funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opfvv               = {funct7,  dup_vrs2, dup_vrs1, funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opmvv               = {funct7,  dup_vrs2, dup_vrs1, funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opivi               = {funct7,  dup_vrs2, rs1,      funct3, dup_vrd,  opcode}; // rs1 is actually the simm5 field which remains the same
   assign dup_rvv_instr_opivx               = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opfvf               = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrd,  opcode};
   assign dup_rvv_instr_opmvx               = {funct7,  dup_vrs2, dup_rs1,  funct3, dup_vrd,  opcode};
   // do some of the decoding for SETVL here
   assign dup_rvv_instr_setvl               =  (instr_in_32[31] == 0)        ? {funct12,          dup_rs1,  funct3, dup_rd, opcode} :
					      ((instr_in_32[31:30] == 2'b11) ? {funct12,          rs1,      funct3, dup_rd, opcode} : // rs1 is actually the uimm5 field which remains the same
					       ((funct7 == 7'b1000000)       ? {funct7,  dup_rs2, dup_rs1,  funct3, dup_rd, opcode} :
					       instr_in_32));

   assign dcd_rvv = dcd_rvv_type_VL_unit_stride ||
		    dcd_rvv_type_VL_strided ||
		    dcd_rvv_type_VL_indexed ||
		    dcd_rvv_type_VS_unit_stride ||
		    dcd_rvv_type_VS_strided ||
		    dcd_rvv_type_VS_indexed ||
		    dcd_rvv_vamo ||
		    dcd_rvv_opivv ||
		    dcd_rvv_opfvv ||
		    dcd_rvv_opmvv ||
		    dcd_rvv_opivi ||
		    dcd_rvv_opivx ||
		    dcd_rvv_opfvf ||
		    dcd_rvv_opmvx ||
		    dcd_rvv_setvl;

   assign dup_rvv_instr =  dcd_rvv_type_VL_unit_stride  ? dup_rvv_instr_type_VL_unit_stride :
			  (dcd_rvv_type_VL_strided      ? dup_rvv_instr_type_VL_strided     :
			  (dcd_rvv_type_VL_indexed      ? dup_rvv_instr_type_VL_indexed     :
			  (dcd_rvv_type_VS_unit_stride  ? dup_rvv_instr_type_VS_unit_stride :
			  (dcd_rvv_type_VS_strided      ? dup_rvv_instr_type_VS_strided     :
			  (dcd_rvv_type_VS_indexed      ? dup_rvv_instr_type_VS_indexed     :
			  (dcd_rvv_vamo                 ? dup_rvv_instr_vamo                :
			  (dcd_rvv_opivv                ? dup_rvv_instr_opivv               :
			  (dcd_rvv_opfvv                ? dup_rvv_instr_opfvv               :
			  (dcd_rvv_opmvv                ? dup_rvv_instr_opmvv               :
			  (dcd_rvv_opivi                ? dup_rvv_instr_opivi               :
			  (dcd_rvv_opivx                ? dup_rvv_instr_opivx               :
			  (dcd_rvv_opfvf                ? dup_rvv_instr_opfvf               :
			  (dcd_rvv_opmvx                ? dup_rvv_instr_opmvx               :
			  (dcd_rvv_setvl                ? dup_rvv_instr_setvl               :
			   instr_in_32))))))))))))));

`else
   assign dcd_rvv       =  0;
   assign dup_rvv_instr = '0; // don't care
`endif
  
   assign instr_out =   dcd_lw                          ? dup_instr_lw : 
		       (dcd_sw                          ? dup_instr_sw : 
		       (dcd_alureg                      ? dup_instr_alureg : 
		       (dcd_aluimm                      ? dup_instr_aluimm :
		       (dcd_jump                        ? dup_instr_jump :
		       (dcd_jump_indirect               ? dup_instr_jump_indirect :
		      ((dcd_lui || dcd_auipc)           ? dup_instr_lui_auipc :
		       (dcd_branch                      ? dup_instr_branch :
		       (dcd_amo                         ? dup_instr_amo    :
		       (dcd_rvf                         ? dup_rvf_instr    :
		       (dcd_rvv                         ? dup_rvv_instr    :
			instr_in_32))))))))));

// Note: add assert property onehot0 on all dcd_* signals

endmodule // FV_CORE_IF_dup
