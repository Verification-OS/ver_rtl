
module FV_instructions_rvc 
  #(parameter DECODER = 1)
   (
    input [`FV_RV32C_INSTR_WIDTH-1:0] instruction
    );

   // extract instruction fields
   wire [`FV_RV32C_OPCODE_WIDTH-1:0]    opcode   = instruction[`FV_RV32C_INSTR_FIELD_OPCODE];
   wire [`FV_RV32C_REG_ADDR_WIDTH-1:0]  rd       = instruction[`FV_RV32C_INSTR_FIELD_RD];
   wire [`FV_RV32C_REG_ADDR_WIDTH-1:0]  rs1      = instruction[`FV_RV32C_INSTR_FIELD_RS1];
   wire [`FV_RV32C_REG_ADDR_WIDTH-1:0]  rs2      = instruction[`FV_RV32C_INSTR_FIELD_RS2];
   wire [`FV_RV32C_REGP_ADDR_WIDTH-1:0] rdp      = instruction[`FV_RV32C_INSTR_FIELD_RDP];
   wire [`FV_RV32C_REGP_ADDR_WIDTH-1:0] rs1p     = instruction[`FV_RV32C_INSTR_FIELD_RS1P];
   wire [`FV_RV32C_REGP_ADDR_WIDTH-1:0] rs2p     = instruction[`FV_RV32C_INSTR_FIELD_RS2P];
   wire [`FV_RV32C_FUNCT2_L_WIDTH-1:0]  funct2_l = instruction[`FV_RV32C_INSTR_FIELD_FUNCT2_L];
   wire [`FV_RV32C_FUNCT2_H_WIDTH-1:0]  funct2_h = instruction[`FV_RV32C_INSTR_FIELD_FUNCT2_H];
   wire [`FV_RV32C_FUNCT3_WIDTH-1:0]    funct3   = instruction[`FV_RV32C_INSTR_FIELD_FUNCT3];
   wire [`FV_RV32C_FUNCT4_WIDTH-1:0]    funct4   = instruction[`FV_RV32C_INSTR_FIELD_FUNCT4];
   wire [`FV_RV32C_FUNCT6_WIDTH-1:0]    funct6   = instruction[`FV_RV32C_INSTR_FIELD_FUNCT6];
   wire [5:0] 				    imm6     = {instruction[12], instruction[6:2]};
`ifdef FV_SPLIT_RF_DMEM_SPACE
   wire [5:0] 				    imm6_CI  = {instruction[12], instruction[6:2]};
   wire [5:0] 				    imm6_CSS =  instruction[12:7];
   wire [4:0] 				    imm5_CL  = {instruction[12:10], instruction[6:5]};
   wire [4:0] 				    imm5_CS  = {instruction[12:10], instruction[6:5]};
`else
   // by making these constant zeros, the constraints later are trivially true 
   // without restricting 'instruction' and makes the code not cluttered (no 'ifdef).
   wire [5:0] 				    imm6_CI  = 0;
   wire [5:0] 				    imm6_CSS = 0;
   wire [4:0] 				    imm5_CL  = 0;
   wire [4:0] 				    imm5_CS  = 0;
`endif   

   wire reg_restrict_instr_type_CR;
   wire reg_restrict_instr_type_CI;
   wire reg_restrict_instr_type_CI_f;
   wire reg_restrict_instr_type_CSS;
   wire reg_restrict_instr_type_CSS_f;
   wire reg_restrict_instr_type_CIW;
   wire reg_restrict_instr_type_CL;
   wire reg_restrict_instr_type_CS;
   wire reg_restrict_instr_type_CA;
   wire reg_restrict_instr_type_CB;  
   wire reg_restrict_instr_type_CJ;

if (DECODER==1) begin
   // no restrictions if used as an instruction decoder
   assign reg_restrict_instr_type_CR    = 1'b1;
   assign reg_restrict_instr_type_CI    = 1'b1;
   assign reg_restrict_instr_type_CI_f  = 1'b1;
   assign reg_restrict_instr_type_CSS   = 1'b1;
   assign reg_restrict_instr_type_CSS_f = 1'b1;
   assign reg_restrict_instr_type_CIW   = 1'b1;
   assign reg_restrict_instr_type_CL    = 1'b1;
   assign reg_restrict_instr_type_CS    = 1'b1;
   assign reg_restrict_instr_type_CA    = 1'b1;
   assign reg_restrict_instr_type_CB    = 1'b1;  
   assign reg_restrict_instr_type_CJ    = 1'b1;
end else begin // if (DECODER==1)
   assign reg_restrict_instr_type_CR    = (FV_FUNC_orig_rd_limit(rd) && FV_FUNC_orig_rs_limit(rs2)  );
   assign reg_restrict_instr_type_CI    = (FV_FUNC_orig_rd_limit(rd)                                    );
   assign reg_restrict_instr_type_CI_f  = (FV_FUNC_orig_frsd_limit(rd)                                  );
   assign reg_restrict_instr_type_CSS   = (                                 FV_FUNC_orig_rs_limit(rs2)  );
   assign reg_restrict_instr_type_CSS_f = (                                 FV_FUNC_orig_frsd_limit(rs2));
   // 3-bit rsp/rdp
   assign reg_restrict_instr_type_CIW = (                                         FV_FUNC_orig_rvc_regp_limit(rdp ));
   assign reg_restrict_instr_type_CL  = (FV_FUNC_orig_rvc_regp_limit(rs1p) && FV_FUNC_orig_rvc_regp_limit(rdp )); // same for RVF
   assign reg_restrict_instr_type_CS  = (FV_FUNC_orig_rvc_regp_limit(rs1p) && FV_FUNC_orig_rvc_regp_limit(rs2p)); // same for RVF
   assign reg_restrict_instr_type_CA  = (FV_FUNC_orig_rvc_regp_limit(rs1p) && FV_FUNC_orig_rvc_regp_limit(rs2p)); // NOTE: rdp in CA instructions is in rs1p bit field
   assign reg_restrict_instr_type_CB  = (FV_FUNC_orig_rvc_regp_limit(rs1p)                                    );
  
   assign reg_restrict_instr_type_CJ  = 1; // no reg, no restrictions
end // else: !if(DECODER==1)

   // ========
   // ========
   wire rv32c_op_C0 = (opcode == `FV_RV32C_OPCODE_C0);
   wire rv32c_op_C1 = (opcode == `FV_RV32C_OPCODE_C1);
   wire rv32c_op_C2 = (opcode == `FV_RV32C_OPCODE_C2);

   // ========
   // quadrant 0 (opcode = C0) 
   wire instr_CADDI4SPN = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CADDI4SPN) && reg_restrict_instr_type_CIW && (instruction[12:5] != 0)  );
   wire instr_CFLD      = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CFLD     ) && reg_restrict_instr_type_CL);
   wire instr_CLQ       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CLQ      ) && reg_restrict_instr_type_CL);
   wire instr_CLW       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CLW      ) && reg_restrict_instr_type_CL);
   wire instr_CFLW      = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CFLW     ) && reg_restrict_instr_type_CL);
   wire instr_CLD       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CLD      ) && reg_restrict_instr_type_CL);
   wire instr_CFSD      = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CFSD     ) && reg_restrict_instr_type_CS);
   wire instr_CSQ       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CSQ      ) && reg_restrict_instr_type_CS);
   wire instr_CSW       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CSW      ) && reg_restrict_instr_type_CS);
   wire instr_CFSW      = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CFSW     ) && reg_restrict_instr_type_CS);
   wire instr_CSD       = rv32c_op_C0 && ((funct3 == `FV_RV32C_FUNCT3_CSD      ) && reg_restrict_instr_type_CS);
       
   // ========
   // quadrant 1 (opcode = C1) 
   wire instr_CNOP      = (instruction == `FV_RV32C_INSTR_CNOP);
   wire instr_CADDI     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CADDI    ) && reg_restrict_instr_type_CI && (imm6 != 0) && (rd!=0));
   wire instr_CJAL      = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CJAL     )                              );
   wire instr_CADDIW    = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CADDIW   ) && reg_restrict_instr_type_CI && (rd!=0));
   wire instr_CLI       = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CLI      ) && reg_restrict_instr_type_CI && (rd!=0));
   wire instr_CADDI16SP = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CADDI16SP) && (rd == 2)                  && (imm6 != 0));
   wire instr_CLUI      = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CLUI     ) && reg_restrict_instr_type_CI && (imm6 != 0) && (rd!=0) && (rd!=2));

   wire instr_CSRLI     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CSRLI    ) && reg_restrict_instr_type_CB && (imm6 != 0) && (funct2_h == `FV_RV32C_FUNCT2_H_CSRLI) && (instruction[12]==0));
   wire instr_CSRLI64   = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CSRLI    ) && reg_restrict_instr_type_CB && (imm6 == 0) && (funct2_h == `FV_RV32C_FUNCT2_H_CSRLI) && (instruction[12]==0));
   wire instr_CSRAI     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CSRAI    ) && reg_restrict_instr_type_CB && (imm6 != 0) && (funct2_h == `FV_RV32C_FUNCT2_H_CSRAI) && (instruction[12]==0));
   wire instr_CSRAI64   = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CSRAI    ) && reg_restrict_instr_type_CB && (imm6 == 0) && (funct2_h == `FV_RV32C_FUNCT2_H_CSRAI) && (instruction[12]==0));
   wire instr_CANDI     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CANDI    ) && reg_restrict_instr_type_CB                && (funct2_h == `FV_RV32C_FUNCT2_H_CANDI));

   wire instr_CSUB      = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_CSUB     ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_CSUB));
   wire instr_CXOR      = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_CXOR     ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_CXOR));
   wire instr_COR       = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_COR      ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_COR));
   wire instr_CAND      = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_CAND     ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_CAND));
   wire instr_CSUBW     = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_CSUBW    ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_CSUBW));
   wire instr_CADDW     = rv32c_op_C1 && ((funct6 == `FV_RV32C_FUNCT6_CADDW    ) && reg_restrict_instr_type_CA && (funct2_l == `FV_RV32C_FUNCT2_L_CADDW));

   wire instr_CJ        = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CJ       ) && reg_restrict_instr_type_CJ); // reg_restrict_instr_type_CJ is 1

   wire instr_CBEQZ     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CBEQZ    ) && reg_restrict_instr_type_CB);
   wire instr_CBNEZ     = rv32c_op_C1 && ((funct3 == `FV_RV32C_FUNCT3_CBNEZ    ) && reg_restrict_instr_type_CB);
		       
   // ========
   // quadrant 2 (opcode = C2) 
   wire instr_CSLLI     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CSLLI    ) && reg_restrict_instr_type_CI && (imm6 != 0) && (rd!=0) && (instruction[12]==0));
   wire instr_CSLLI64   = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CSLLI    ) && reg_restrict_instr_type_CI && (imm6 == 0) && (rd!=0) && (instruction[12]==0));
   
   wire instr_CFLDSP    = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CFLDSP   ) && reg_restrict_instr_type_CI_f);
   wire instr_CLQSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CLQSP    ) && reg_restrict_instr_type_CI && (rd!=0));

   wire instr_CLWSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CLWSP    ) && reg_restrict_instr_type_CI && (rd!=0));

   wire instr_CFLWSP    = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CFLWSP   ) && reg_restrict_instr_type_CI_f);
   wire instr_CLDSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CLDSP    ) && reg_restrict_instr_type_CI && (rd!=0));

   wire instr_CJR       = rv32c_op_C2 && ((funct4 == `FV_RV32C_FUNCT4_CJR      ) && reg_restrict_instr_type_CR && (rs1!=0) && (rs2==0));
   wire instr_CMV       = rv32c_op_C2 && ((funct4 == `FV_RV32C_FUNCT4_CMV      ) && reg_restrict_instr_type_CR && (rd!=0)  && (rs2!=0));
   wire instr_CEBREAK   = rv32c_op_C2 && ((funct4 == `FV_RV32C_FUNCT4_CEBREAK  ) && reg_restrict_instr_type_CR && (rd==0)  && (rs2==0));
   wire instr_CJALR     = rv32c_op_C2 && ((funct4 == `FV_RV32C_FUNCT4_CJALR    ) && reg_restrict_instr_type_CR && (rs1!=0) && (rs2==0));
   wire instr_CADD      = rv32c_op_C2 && ((funct4 == `FV_RV32C_FUNCT4_CADD     ) && reg_restrict_instr_type_CR && (rd!=0)  && (rs2!=0));

   wire instr_CFSDSP    = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CFSDSP   ) && reg_restrict_instr_type_CSS_f);
   wire instr_CSQSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CSQSP    ) && reg_restrict_instr_type_CSS);

   wire instr_CSWSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CSWSP    ) && reg_restrict_instr_type_CSS);

   wire instr_CFSWSP    = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CFSWSP   ) && reg_restrict_instr_type_CSS_f);
   wire instr_CSDSP     = rv32c_op_C2 && ((funct3 == `FV_RV32C_FUNCT3_CSDSP    ) && reg_restrict_instr_type_CSS);
	       
endmodule // FV_instructions_rvc
