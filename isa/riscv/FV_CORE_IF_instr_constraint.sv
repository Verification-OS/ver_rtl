
module FV_CORE_IF_instr_constraint(
				       input logic 			     clk,
			               input logic [`FV_INSTR_WIDTH-1:0] instruction
				       );

   FV_instructions #(.DECODER(0)) encoder(.instruction(instruction));
   
   wire include_alu_type_I = encoder.reg_restrict_instr_type_I && 
			     (
`ifndef FV_EXCLUDE_INSTR_ADDI
	       encoder.instr_ADDI || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLTI
	       encoder.instr_SLTI || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLTIU
	       encoder.instr_SLTIU || 
`endif
`ifndef FV_EXCLUDE_INSTR_XORI
	       encoder.instr_XORI || 
// Note0 Note
 `ifdef FV_INCLUDE_RVV
	       encoder.instr_VADD || 
 `endif			      

`endif
`ifndef FV_EXCLUDE_INSTR_ORI
	       encoder.instr_ORI || 
`endif
`ifndef FV_EXCLUDE_INSTR_ANDI
	       encoder.instr_ANDI || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLLI
	       encoder.instr_SLLI || 
`endif
`ifndef FV_EXCLUDE_INSTR_SRLI
	       encoder.instr_SRLI || 
`endif
`ifndef FV_EXCLUDE_INSTR_SRAI
	       encoder.instr_SRAI ||
`endif
`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_ADDIW
	        encoder.instr_ADDIW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SLLIW
	        encoder.instr_SLLIW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SRLIW
		encoder.instr_SRLIW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SRAIW
		encoder.instr_SRAIW ||
 `endif
`endif
			      1'b0);

   wire include_alu_type_R = encoder.reg_restrict_instr_type_R && 
			     (
`ifndef FV_EXCLUDE_INSTR_ADD
	       encoder.instr_ADD || 
`endif
`ifndef FV_EXCLUDE_INSTR_SUB
	       encoder.instr_SUB || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLL
	       encoder.instr_SLL || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLT
	       encoder.instr_SLT || 
`endif
`ifndef FV_EXCLUDE_INSTR_SLTU
	       encoder.instr_SLTU || 
`endif
`ifndef FV_EXCLUDE_INSTR_XOR
	       encoder.instr_XOR || 
`endif
`ifndef FV_EXCLUDE_INSTR_SRL
	       encoder.instr_SRL || 
`endif
`ifndef FV_EXCLUDE_INSTR_SRA
	       encoder.instr_SRA || 
`endif
`ifndef FV_EXCLUDE_INSTR_OR
	       encoder.instr_OR || 
`endif
`ifndef FV_EXCLUDE_INSTR_AND
	       encoder.instr_AND ||
`endif

`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_ADDW
	        encoder.instr_ADDW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SUBW
	        encoder.instr_SUBW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SLLW
	        encoder.instr_SLLW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SRLW
	        encoder.instr_SRLW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_SRAW
	        encoder.instr_SRAW || 
 `endif
`endif //  `ifdef FV_INCLUDE_RV64
			      
`ifdef FV_INCLUDE_RV32M  
 `ifndef FV_EXCLUDE_INSTR_MUL
	        encoder.instr_MUL || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_MULH
	        encoder.instr_MULH || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_MULHSU
	        encoder.instr_MULHSU || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_MULHU
	        encoder.instr_MULHU || 
 `endif

 `ifndef FV_EXCLUDE_RV32M_DIV
  `ifndef FV_EXCLUDE_INSTR_DIV
	         encoder.instr_DIV || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_DIVU
	         encoder.instr_DIVU || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_REM
	         encoder.instr_REM || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_REMU
	         encoder.instr_REMU ||
  `endif
 `endif //  `ifndef FV_EXCLUDE_RV32M_DIV
			      
`endif //  `ifdef FV_INCLUDE_RV32M

`ifdef FV_INCLUDE_RV64M  
 `ifndef FV_EXCLUDE_INSTR_MULW
	        encoder.instr_MULW || 
 `endif
 `ifndef FV_EXCLUDE_RV32M_DIV
  `ifndef FV_EXCLUDE_INSTR_DIVW
	         encoder.instr_DIVW || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_DIVUW
	         encoder.instr_DIVUW || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_REMW
	         encoder.instr_REMW || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_REMUW
	         encoder.instr_REMUW ||
  `endif
 `endif //  `ifndef FV_EXCLUDE_RV32M_DIV
`endif //  `ifdef FV_INCLUDE_RV64M

			      1'b0);

   wire include_ldst = ((
`ifndef FV_EXCLUDE_INSTR_LB
	       encoder.instr_LB || 
`endif
`ifndef FV_EXCLUDE_INSTR_LH
	       encoder.instr_LH || 
`endif
`ifndef FV_EXCLUDE_INSTR_LW
	       encoder.instr_LW || 
`endif
`ifndef FV_EXCLUDE_INSTR_LBU
	       encoder.instr_LBU || 
`endif
`ifndef FV_EXCLUDE_INSTR_LHU
	       encoder.instr_LHU ||
`endif

`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_LWU
		encoder.instr_LWU ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_LD
		encoder.instr_LD  ||
 `endif
`endif

			 1'b0) &&

			 encoder.imm_restrict_instr_type_L &&

`ifdef FV_LIMIT_LS_BASE_R0
			 ((encoder.rs1 == `FV_RV32_REG_ADDR_WIDTH'b0) && FV_FUNC_orig_rd_limit(encoder.rd))
`else
			 encoder.reg_restrict_instr_type_I
`endif
		       ) // loads
	               ||
		       ((
`ifndef FV_EXCLUDE_INSTR_SB
	       encoder.instr_SB || 
`endif
`ifndef FV_EXCLUDE_INSTR_SH
	       encoder.instr_SH || 
`endif
`ifndef FV_EXCLUDE_INSTR_SW
	       encoder.instr_SW ||
`endif

`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_SD
		encoder.instr_SD  ||
 `endif
`endif

			1'b0) &&

			 encoder.imm_restrict_instr_type_S &&

`ifdef FV_LIMIT_LS_BASE_R0
			 ((encoder.rs1 == `FV_RV32_REG_ADDR_WIDTH'b0) && FV_FUNC_orig_rs_limit(encoder.rs2))
`else
			 encoder.reg_restrict_instr_type_S
`endif
			); // stores
   
   // ========
   wire include_NOP = (instruction == `FV_INSTR_NOP);

   wire include_jumps = (
`ifndef FV_EXCLUDE_INSTR_JAL
	       encoder.instr_JAL || 
`endif
`ifndef FV_EXCLUDE_INSTR_JALR
	       encoder.instr_JALR ||
`endif

			 1'b0);
   
   wire include_branches = encoder.reg_restrict_instr_type_B &&
	                   (
`ifndef FV_EXCLUDE_INSTR_BEQ
	       encoder.instr_BEQ || 
`endif
`ifndef FV_EXCLUDE_INSTR_BNE
	       encoder.instr_BNE || 
`endif
`ifndef FV_EXCLUDE_INSTR_BLT
	       encoder.instr_BLT || 
`endif
`ifndef FV_EXCLUDE_INSTR_BGE
	       encoder.instr_BGE || 
`endif
`ifndef FV_EXCLUDE_INSTR_BLTU
	       encoder.instr_BLTU || 
`endif
`ifndef FV_EXCLUDE_INSTR_BGEU
	       encoder.instr_BGEU ||
`endif
			    1'b0);

   wire include_type_U = (
`ifndef FV_EXCLUDE_INSTR_LUI
	       encoder.instr_LUI ||
`endif
`ifndef FV_EXCLUDE_INSTR_AUIPC
// Note: we could have AUIPC duplicated and get checked by CF like dup JAL
 `ifndef FV_SPLIT_RF_DMEM_SPACE
               encoder.instr_AUIPC || 
 `endif
`endif
			  1'b0) &&
	                 encoder.reg_restrict_instr_type_U;

   wire include_misc_mem = (
`ifndef FV_EXCLUDE_INSTR_FENCE
	       encoder.instr_FENCE || 
`endif
`ifndef FV_EXCLUDE_INSTR_FENCE_I
	       encoder.instr_FENCE_I ||
`endif
			    1'b0);

`ifdef FV_INCLUDE_RVA
`ifdef FV_ENABLE_DUP
// Note: temporarily use R0 only for rs1 and R0P for rs1 of dup instr
   wire reg_restrict_instr_type_R_amo = ( FV_FUNC_orig_rd_limit(encoder.rd) && (encoder.rs1 == 0) && FV_FUNC_orig_rs_limit(encoder.rs2));

   wire include_atomics = reg_restrict_instr_type_R_amo && 
`else
   wire include_atomics = encoder.reg_restrict_instr_type_R && 
`endif
	                  (
 `ifndef FV_EXCLUDE_INSTR_LRW
		encoder.instr_LRW      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_SCW
		encoder.instr_SCW      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOSWAPW
		encoder.instr_AMOSWAPW ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOADDW
		encoder.instr_AMOADDW  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOXORW
		encoder.instr_AMOXORW  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOANDW
		encoder.instr_AMOANDW  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOORW
		encoder.instr_AMOORW   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMINW
		encoder.instr_AMOMINW  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMAXW
		encoder.instr_AMOMAXW  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMINUW
		encoder.instr_AMOMINUW ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMAXUW
		encoder.instr_AMOMAXUW ||
 `endif
			   
 `ifdef FV_INCLUDE_RV64

 `ifndef FV_EXCLUDE_INSTR_LRD
		encoder.instr_LRD      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_SCD
		encoder.instr_SCD      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOSWAPD
		encoder.instr_AMOSWAPD ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOADDD
		encoder.instr_AMOADDD  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOXORD
		encoder.instr_AMOXORD  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOANDD
		encoder.instr_AMOANDD  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOORD
		encoder.instr_AMOORD   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMIND
		encoder.instr_AMOMIND  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMAXD
		encoder.instr_AMOMAXD  ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMINUD
		encoder.instr_AMOMINUD ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_AMOMAXUD
		encoder.instr_AMOMAXUD ||
 `endif
			   
 `endif //  `ifdef FV_INCLUDE_RV64
			   
			   1'b0);
			    
`endif //  `ifdef FV_INCLUDE_RVA

   
   // ========
   // CSR instructions weres removed from RV32I to Zicsr instruction extension
   // NOTE: support is currently ONLY for CSRRW of frm field of fcsr register
   //       and this is either writing x0 to it, or writing a valid immediate value to it
   // Note: create a separate define for ifdef'ing (EXCLUDE/INCLUDE) each register?
   // Note: no uimm[4:0] value restrictions?
`ifdef FV_INCLUDE_RVZICSR
// Note: rewrite the following to use the instr_CSR* in the new FV_instructions
   wire include_csr = (encoder.opcode == `FV_RV_OPCODE_SYSTEM) &&
// Note: limit to rd=0 for FV; temporary?
`ifndef FV_ENABLE_SI
		      (encoder.rd == `FV_RV32_REG_ADDR_WIDTH'b0) &&
`endif
		      ((
// Note: maybe allow any rs1 for si-FV for these, but for FV, any rs1 value could lead to invalid value
`ifdef FV_ENABLE_SI
		        encoder.reg_restrict_instr_type_I && // Note not all rs1 values are valid to write?
`else 
		        (encoder.rs1 == `FV_RV32_REG_ADDR_WIDTH'b0) &&
`endif
			(
			 (encoder.funct3 == `FV_RV32I_FUNCT3_CSRRW)  ||
			 (encoder.funct3 == `FV_RV32I_FUNCT3_CSRRS)  ||
			 (encoder.funct3 == `FV_RV32I_FUNCT3_CSRRC)
			)
		       ) ||
		       ( // uimm[4:0] can be any value
		        ((encoder.funct3 == `FV_RV32I_FUNCT3_CSRRWI) && 
			 ((encoder.csr_imm5[4:3] == 2'b0) &&
			  (encoder.csr_imm5[2:0] != `FV_RVF_FUNCT3_RM_RESRV1) &&
			  (encoder.csr_imm5[2:0] != `FV_RVF_FUNCT3_RM_RESRV2) &&
			  (encoder.csr_imm5[2:0] != `FV_RVF_FUNCT3_RM_DYN)
			  )
			 ) ||
// Note		        (encoder.funct3 == `FV_RV32I_FUNCT3_CSRRSI) ||
// Note		        (encoder.funct3 == `FV_RV32I_FUNCT3_CSRRCI) ||
			 1'b0
		       )
		      ) 
			&&
	              (
/* Note3? these are no longer considered mandatory
   maybe add si-FV for these, otherwise what do we check?		       
		       (encoder.imm12 == `FV_RV32I_CSR_CYCLE)    ||
		       (encoder.imm12 == `FV_RV32I_CSR_TIME)     ||
		       (encoder.imm12 == `FV_RV32I_CSR_INSTRET)  ||
		       (encoder.imm12 == `FV_RV32I_CSR_CYCLEH)   ||
		       (encoder.imm12 == `FV_RV32I_CSR_TIMEH)    ||
		       (encoder.imm12 == `FV_RV32I_CSR_INSTRETH) ||
 */
`ifdef FV_INCLUDE_RVF
// Note		       (encoder.imm12 == `FV_RVF_CSR_FFLAGS)     ||
		       (encoder.imm12 == `FV_RVF_CSR_FRM)        ||
// Note		       (encoder.imm12 == `FV_RVF_CSR_FCSR)       ||
`endif
		       1'b0
		       );
`endif //  `ifdef FV_INCLUDE_RVZICSR

   wire include_ecall_ebreak = (
`ifndef FV_EXCLUDE_INSTR_ECALL
	       encoder.instr_ECALL || 
`endif
`ifndef FV_EXCLUDE_INSTR_EBREAK
 `ifndef FV_ENABLE_CMT
// Note: keep EBREAK out of CMT or add back?
// wake up from EBREAK needs a special signal; in riscy/zero-riscy, debug_resume can be tied to  for that
	       encoder.instr_EBREAK ||  
 `endif
`endif
				1'b0
				);

// Note: add xRET instructions and send them only if in ISR?
   
`ifdef FV_INCLUDE_RVF
   wire include_alu_rvf =
 `ifndef FV_EXCLUDE_INSTR_FMADDS
                encoder.instr_FMADDS    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMSUBS
                encoder.instr_FMSUBS    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FNMSUBS
                encoder.instr_FNMSUBS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FNMADDS
                encoder.instr_FNMADDS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FADDS
                encoder.instr_FADDS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FSUBS
                encoder.instr_FSUBS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMULS
                encoder.instr_FMULS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FDIVS
                encoder.instr_FDIVS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FSQRTS
                encoder.instr_FSQRTS    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FSGNJS
                encoder.instr_FSGNJS    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FSGNJNS
                encoder.instr_FSGNJNS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FSGNJXS
                encoder.instr_FSGNJXS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMINS
                encoder.instr_FMINS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMAXS
                encoder.instr_FMAXS     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FCVTWS
                encoder.instr_FCVTWS    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FCVTWUS
                encoder.instr_FCVTWUS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMVXW
                encoder.instr_FMVXW     ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FEQS
                encoder.instr_FEQS      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FLTS
                encoder.instr_FLTS      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FLES
                encoder.instr_FLES      ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FCLASSS
                encoder.instr_FCLASSS   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FCVTSW
                encoder.instr_FCVTSW    ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FCVTSWU
                encoder.instr_FCVTSWU   ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_FMVWX
                encoder.instr_FMVWX     ||
 `endif
   
   // ==================
   // RV64F instructions
 `ifdef FV_INCLUDE_RV64
  `ifndef FV_EXCLUDE_INSTR_FCVTLS
                 encoder.instr_FCVTLS    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTLUS
                 encoder.instr_FCVTLUS   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTSL
                 encoder.instr_FCVTSL    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTSLU
                 encoder.instr_FCVTSLU   ||
  `endif
 `endif //  `ifdef FV_INCLUDE_RV64

 `ifdef FV_INCLUDE_RVD
  `ifndef FV_EXCLUDE_INSTR_FMADDD
                 encoder.instr_FMADDD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FMSUBD
                 encoder.instr_FMSUBD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FNMSUBD
                 encoder.instr_FNMSUBD   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FNMADDD
                 encoder.instr_FNMADDD   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FADDD
                 encoder.instr_FADDD     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FSUBD
                 encoder.instr_FSUBD     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FMULD
                 encoder.instr_FMULD     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FDIVD
                 encoder.instr_FDIVD     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FSQRTD
                 encoder.instr_FSQRTD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FSGNJD
                 encoder.instr_FSGNJD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FSGNJND
                 encoder.instr_FSGNJND   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FSGNJXD
                 encoder.instr_FSGNJXD   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FMIND
                 encoder.instr_FMIND     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FMAXD
                 encoder.instr_FMAXD     ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTSD
                 encoder.instr_FCVTSD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTDS
                 encoder.instr_FCVTDS    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FEQD
                 encoder.instr_FEQD      ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FLTD
                 encoder.instr_FLTD      ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FLED
                 encoder.instr_FLED      ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCLASSD
                 encoder.instr_FCLASSD   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTWD 
                 encoder.instr_FCVTWD    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTWUD
                 encoder.instr_FCVTWUD   ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTDW
                 encoder.instr_FCVTDW    ||
  `endif
  `ifndef FV_EXCLUDE_INSTR_FCVTDWU
                 encoder.instr_FCVTDWU   ||
  `endif
   
   // ==================
   // RV64D instructions
  `ifdef FV_INCLUDE_RV64
   `ifndef FV_EXCLUDE_INSTR_FCVTLD
                  encoder.instr_FCVTLD    ||
   `endif
   `ifndef FV_EXCLUDE_INSTR_FCVTLUD
                  encoder.instr_FCVTLUD   ||
   `endif
   `ifndef FV_EXCLUDE_INSTR_FMVXD
                  encoder.instr_FMVXD     ||
   `endif
   `ifndef FV_EXCLUDE_INSTR_FCVTDL
                  encoder.instr_FCVTDL    ||
   `endif
   `ifndef FV_EXCLUDE_INSTR_FCVTDLU
                  encoder.instr_FCVTDLU   ||
   `endif
   `ifndef FV_EXCLUDE_INSTR_FMVDX
                  encoder.instr_FMVDX     ||
   `endif
  `endif //  `ifdef FV_INCLUDE_RV64
			 
 `endif //  `ifdef FV_INCLUDE_RVD
			 
			      1'b0;

   wire include_ldst_rvf = ((
 `ifndef FV_EXCLUDE_INSTR_FLW
		encoder.instr_FLW || 
 `endif
 `ifdef FV_INCLUDE_RVD
  `ifndef FV_EXCLUDE_INSTR_FLD
		 encoder.instr_FLD || 
  `endif
 `endif
			 1'b0) &&

			 encoder.imm_restrict_instr_type_L &&

 `ifdef FV_LIMIT_LS_BASE_R0
			 (encoder.rs1 == `FV_RV32_REG_ADDR_WIDTH'b0)
 `else
			 1'b1
 `endif
		       ) // loads
	               ||
		       ((
 `ifndef FV_EXCLUDE_INSTR_FSW
		encoder.instr_FSW || 
 `endif
 `ifdef FV_INCLUDE_RVD
  `ifndef FV_EXCLUDE_INSTR_FSD
		 encoder.instr_FSD || 
  `endif
 `endif
			1'b0) &&

			 encoder.imm_restrict_instr_type_S &&

 `ifdef FV_LIMIT_LS_BASE_R0
			 (encoder.rs1 == `FV_RV32_REG_ADDR_WIDTH'b0)
 `else
			 1'b1
 `endif
			); // stores
`endif //  `ifdef FV_INCLUDE_RVF
   

`ifdef FV_INCLUDE_RVC

   logic include_alu_type_I_rvc;
   logic include_alu_type_R_rvc;
   logic include_ldst_rvc;
   logic include_jumps_rvc;
   logic include_branches_rvc;
   logic include_misc_rvc;
   logic include_ebreak_rvc;
   logic include_NOP_rvc;

   // RVC covers all RISC-V compressed instrutions based on RV64 or RV128 defines
   FV_CORE_IF_instr_constraint_rvc rvc(.*,
					   .instruction(instruction[`FV_RV32C_INSTR_WIDTH-1:0])
					   );

   always @(posedge clk) begin
      // force the upper half of the instructions to all 0s for compressed instructions
  `ifdef FV_ENABLE_SC_DEBUG
      FV_IF_instr_constr_compressed_MSBs_0:         
  `else
      FV_if_con1:
  `endif
      assume property ((instruction[1:0] != 2'b11) |-> (instruction[`FV_INSTR_WIDTH-1:`FV_RV32C_INSTR_WIDTH] == {(`FV_INSTR_WIDTH-`FV_RV32C_INSTR_WIDTH){1'b0}}));
   end
`endif
  
   always @(posedge clk) begin
  `ifdef FV_ENABLE_SC_DEBUG
      FV_IF_instr_constr_include_OR:         
  `else
      FV_if_con2:
  `endif
      assume property (include_alu_type_I     || 
		       include_alu_type_R     || 
		       include_ldst           ||
 `ifdef FV_INCLUDE_RVC
		       include_alu_type_I_rvc || 
		       include_alu_type_R_rvc || 
		       include_ldst_rvc       ||
 `endif
 `ifdef FV_INCLUDE_RVF
 // each includes all RVF/D/Q if enabled
		       include_alu_rvf        ||
		       include_ldst_rvf       ||
 `endif
 `ifndef FV_EXCLUDE_JMP_BR
		       include_jumps          ||
		       include_branches       ||
  `ifdef FV_INCLUDE_RVC
		       include_jumps_rvc      ||
		       include_branches_rvc   ||
  `endif
 `endif
	               include_type_U         ||
 `ifdef FV_INCLUDE_MISC_MEM
		       include_misc_mem       ||
 `endif
 `ifdef FV_INCLUDE_RVC
		       include_misc_rvc       ||
 `endif
 `ifdef FV_INCLUDE_RVA
		       include_atomics        ||
 `endif
 `ifdef FV_INCLUDE_RVZICSR
		       include_csr            ||
 `endif
 `ifndef FV_EXCLUDE_ECALL_EBREAK
		       include_ecall_ebreak   ||
  `ifdef FV_INCLUDE_RVC
		       include_ebreak_rvc     ||
  `endif
 `endif
 `ifdef FV_INCLUDE_RVC
		       include_NOP_rvc        ||
 `endif
		       include_NOP
		       );

   end

   // Note: add assertions to check out code correctness
   // - the instr_*   above should be 1-hot if we have done the encoding properly
   // - the include_* above should be 1-hot if we have done the encoding properly
   // - if an instruction is included, its instr_<instr> should be assertible if the encoding is not over constrained   

   FV_SC_instr_constr_1hot: assert property (@(posedge clk) $onehot({
								       include_alu_type_I     , 
								       include_alu_type_R     , 
								       include_ldst           ,
`ifdef FV_INCLUDE_RVC
								       include_alu_type_I_rvc , 
								       include_alu_type_R_rvc , 
								       include_ldst_rvc       ,
`endif
`ifdef FV_INCLUDE_RVF
// each includes all RVF/D/Q if enabled
								       include_alu_rvf        ,
								       include_ldst_rvf       ,
`endif
`ifndef FV_EXCLUDE_JMP_BR
								       include_jumps          ,
								       include_branches       ,
 `ifdef FV_INCLUDE_RVC
								       include_jumps_rvc      ,
								       include_branches_rvc   ,
 `endif
`endif
								       include_type_U         ,
`ifdef FV_INCLUDE_MISC_MEM
								       include_misc_mem       ,
`endif
`ifdef FV_INCLUDE_RVC
								       include_misc_rvc       ,
`endif
`ifdef FV_INCLUDE_RVA
								       include_atomics        ,
`endif
`ifdef FV_INCLUDE_RVZICSR
								       include_csr            ,
`endif
`ifndef FV_EXCLUDE_ECALL_EBREAK
								       include_ecall_ebreak   ,
 `ifdef FV_INCLUDE_RVC
								       include_ebreak_rvc     ,
 `endif
`endif
`ifdef FV_INCLUDE_RVC
								       include_NOP_rvc        ,
`endif
								       include_NOP
                                                                       }));

   
endmodule // FV_CORE_IF_instr_constraint

