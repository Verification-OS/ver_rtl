
module FV_CORE_IF_instr_constraint_rvc(
					   input [`FV_RV32C_INSTR_WIDTH-1:0] instruction,

					   output logic include_alu_type_I_rvc,
					   output logic include_alu_type_R_rvc,
					   output logic include_ldst_rvc,
					   output logic include_jumps_rvc,
					   output logic include_branches_rvc,
					   output logic include_misc_rvc,
					   output logic include_ebreak_rvc,
					   output logic include_NOP_rvc
					   );

   FV_instructions_rvc #(.DECODER(0)) encoder(.instruction(instruction));
   
   // ========

   assign include_alu_type_I_rvc = (
`ifndef FV_EXCLUDE_INSTR_CADDI4SPN
	       encoder.instr_CADDI4SPN || 
`endif
`ifndef FV_EXCLUDE_INSTR_CADDI
	       encoder.instr_CADDI || 
`endif
`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_CADDIW
	        encoder.instr_CADDIW || 
 `endif
`endif
`ifndef FV_EXCLUDE_INSTR_CADDI16SP
	       encoder.instr_CADDI16SP || 
`endif

`ifndef FV_EXCLUDE_INSTR_CSRLI
	       encoder.instr_CSRLI || 
`endif
`ifndef FV_EXCLUDE_INSTR_CSRAI
	       encoder.instr_CSRAI ||
`endif
`ifndef FV_EXCLUDE_INSTR_CANDI
	       encoder.instr_CANDI || 
`endif
`ifndef FV_EXCLUDE_INSTR_CSLLI
	       encoder.instr_CSLLI || 
`endif

`ifdef FV_INCLUDE_RV128
 `ifndef FV_EXCLUDE_INSTR_CSRLI64
	        encoder.instr_CSRLI64 || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CSRAI64
	        encoder.instr_CSRAI64 ||
 `endif
 `ifndef FV_EXCLUDE_INSTR_CSLLI64
	        encoder.instr_CSLLI64 || 
 `endif
`endif //  `ifdef FV_INCLUDE_RV128
				    
			      1'b0);

   // ========

   assign include_alu_type_R_rvc = (
`ifndef FV_EXCLUDE_INSTR_CSUB
	       encoder.instr_CSUB || 
`endif
`ifndef FV_EXCLUDE_INSTR_CXOR
	       encoder.instr_CXOR || 
`endif
`ifndef FV_EXCLUDE_INSTR_COR
	       encoder.instr_COR || 
`endif
`ifndef FV_EXCLUDE_INSTR_CAND
	       encoder.instr_CAND ||
`endif
`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_CSUBW
	        encoder.instr_CSUBW || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CADDW
		encoder.instr_CADDW || 
 `endif
`endif
`ifndef FV_EXCLUDE_INSTR_CADD
	       encoder.instr_CADD || 
`endif
			      1'b0);

   // ========

   // limit to lower half of a 128B memory
   // Note: change to accomodate other memory sizes or address bits
   // NOTES:
   // - if not FV_SPLIT_RF_DMEM_SPACE, the immX wires are constant 0; avoids ugly ifdef's
   // - LSB/MSBs are scrambled in the immX fields
   assign include_ldst_rvc = ( // loads
`ifndef FV_EXCLUDE_INSTR_CLW
	      (encoder.instr_CLW   && (encoder.imm5_CL[0]   == 0)) || 
`endif
`ifndef FV_EXCLUDE_INSTR_CLWSP
	      (encoder.instr_CLWSP && (encoder.imm6_CI[1:0] == 0)) || 
`endif
`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_CLD
	       (encoder.instr_CLD   && (encoder.imm5_CL[1:0] == 0)) || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CLDSP
	       (encoder.instr_CLDSP && (encoder.imm6_CI[2:0] == 0)) || 
 `endif
`else
 `ifdef FV_INCLUDE_RVF
  `ifndef FV_EXCLUDE_INSTR_CFLW
	        (encoder.instr_CFLW   && (encoder.imm5_CL[0]   == 0)) || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_CFLWSP
	        (encoder.instr_CFLWSP && (encoder.imm6_CI[1:0] == 0)) || 
  `endif
 `endif
`endif // !`ifdef FV_INCLUDE_RV64
			       
`ifdef FV_INCLUDE_RV128
 `ifndef FV_EXCLUDE_INSTR_CLQ
	       (encoder.instr_CLQ    && (encoder.imm5_CL[2:0] == 0)) || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CLQSP
	       (encoder.instr_CLQSP && (encoder.imm6_CI[3:0] == 0)) || 
 `endif
`else
 `ifdef FV_INCLUDE_RVD
  `ifndef FV_EXCLUDE_INSTR_CFLD
	        (encoder.instr_CFLD   && (encoder.imm5_CL[1:0] == 0)) || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_CFLDSP
	        (encoder.instr_CFLDSP && (encoder.imm6_CI[2:0] == 0)) || 
  `endif
 `endif
`endif // !`ifdef FV_INCLUDE_RV128
			       
			       1'b0)
     ||
			     ( // stores
`ifndef FV_EXCLUDE_INSTR_CSW
	      (encoder.instr_CSW   && (encoder.imm5_CS[0]    == 0)) || 
`endif
`ifndef FV_EXCLUDE_INSTR_CSWSP
	      (encoder.instr_CSWSP && (encoder.imm6_CSS[1:0] == 0)) || 
`endif
`ifdef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_CSD
	       (encoder.instr_CSD   && (encoder.imm5_CS[1:0]  == 0)) || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CSDSP
	       (encoder.instr_CSDSP && (encoder.imm6_CSS[2:0] == 0)) || 
 `endif
`else
 `ifdef FV_INCLUDE_RVF
  `ifndef FV_EXCLUDE_INSTR_CFSW
	        (encoder.instr_CFSW   && (encoder.imm5_CS[0]    == 0)) || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_CFSWSP
	        (encoder.instr_CFSWSP && (encoder.imm6_CSS[1:0] == 0)) || 
  `endif
 `endif
`endif // !`ifdef FV_INCLUDE_RV64
			       
`ifdef FV_INCLUDE_RV128
 `ifndef FV_EXCLUDE_INSTR_CSQ
	       (encoder.instr_CSQ   && (encoder.imm5_CS[2:0]  == 0)) || 
 `endif
 `ifndef FV_EXCLUDE_INSTR_CSQSP
	       (encoder.instr_CSQSP && (encoder.imm6_CSS[3:0] == 0)) || 
 `endif
`else
 `ifdef FV_INCLUDE_RVD
  `ifndef FV_EXCLUDE_INSTR_CFSD
	        (encoder.instr_CFSD   && (encoder.imm5_CS[1:0]  == 0)) || 
  `endif
  `ifndef FV_EXCLUDE_INSTR_CFSDSP
	        (encoder.instr_CFSDSP && (encoder.imm6_CSS[2:0] == 0)) || 
  `endif
 `endif
`endif
			       1'b0);

   // ========
   assign include_NOP_rvc = (
`ifndef FV_EXCLUDE_INSTR_CNOP
	       encoder.instr_CNOP ||
`endif
			     1'b0);

   // ========
   // jumps == plain and indirect unconditional jump
  
   assign include_jumps_rvc = (
`ifndef FV_INCLUDE_RV64
 `ifndef FV_EXCLUDE_INSTR_CJAL
		encoder.instr_CJAL  || 
 `endif
`endif
`ifndef FV_EXCLUDE_INSTR_CJ
	       encoder.instr_CJ    || 
`endif
`ifndef FV_EXCLUDE_INSTR_CJR
	       encoder.instr_CJR   ||
`endif
`ifndef FV_EXCLUDE_INSTR_CJALR
	       encoder.instr_CJALR ||
`endif
			       1'b0);

   // ========
   // branches == conditional jumps/branches

   assign include_branches_rvc = encoder.reg_restrict_instr_type_CB && (
`ifndef FV_EXCLUDE_INSTR_CBEQZ
	       encoder.instr_CBEQZ || 
`endif
`ifndef FV_EXCLUDE_INSTR_CBNEZ
	       encoder.instr_CBNEZ ||
`endif
			    1'b0);

   // ========

   assign include_misc_rvc = (
`ifndef FV_EXCLUDE_INSTR_CLI
	       encoder.instr_CLI  ||
`endif
`ifndef FV_EXCLUDE_INSTR_CLUI
	       encoder.instr_CLUI ||
`endif
`ifndef FV_EXCLUDE_INSTR_CMV
	       encoder.instr_CMV  ||
`endif
			      1'b0);
   
   // ========
   
   assign include_ebreak_rvc = (
`ifndef FV_EXCLUDE_INSTR_CEBREAK
	       encoder.instr_CEBREAK || 
`endif
			       1'b0);

   // Note: add assertions to check out code correctness
   // - instr_* should be 1-hot or 0
   // - the include_* above should be 1-hot OR 0 if we have done the encoding properly
   //   - THE ABOVE IS CHECKED IN PARENT MODULE

endmodule // FV_CORE_IF_instr_constraint_rvc


