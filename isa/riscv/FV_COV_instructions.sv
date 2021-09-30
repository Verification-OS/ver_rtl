
module FV_COV_instructions(
			       input logic 			     clk,
			       input logic 			     instr_valid,
			       input logic [`FV_INSTR_WIDTH-1:0] instr
			       );

   FV_instructions decoder(.instruction(instr));
`ifdef FV_INCLUDE_RVC
   FV_instructions_rvc decoder_rvc(.instruction(instr[15:0]));
`endif

   FV_Cover_instr_ADDI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_ADDI);
   FV_Cover_instr_SLTI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SLTI);
   FV_Cover_instr_SLTIU: cover property (@(posedge clk) instr_valid |-> decoder.instr_SLTIU);
   FV_Cover_instr_XORI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_XORI);
   FV_Cover_instr_ORI:   cover property (@(posedge clk) instr_valid |-> decoder.instr_ORI);
   FV_Cover_instr_ANDI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_ANDI);
   FV_Cover_instr_SLLI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SLLI);
   FV_Cover_instr_SRLI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SRLI);
   FV_Cover_instr_SRAI:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SRAI);
`ifdef FV_INCLUDE_RV64
   FV_Cover_instr_ADDIW: cover property (@(posedge clk) instr_valid |-> decoder.instr_ADDIW);
   FV_Cover_instr_SLLIW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SLLIW);
   FV_Cover_instr_SRLIW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SRLIW);
   FV_Cover_instr_SRAIW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SRAIW);
`endif

`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CADDI4SPN: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADDI4SPN);
   FV_Cover_instr_CADDI:     cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADDI);
 `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_CADDIW:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADDIW);
 `endif
   FV_Cover_instr_CADDI16SP: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADDI16SP);
   FV_Cover_instr_CSRLI:     cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSRLI);
   FV_Cover_instr_CSRAI:     cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSRAI);
   FV_Cover_instr_CANDI:     cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CANDI);
   FV_Cover_instr_CSLLI:     cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSLLI);
`endif //  `ifdef FV_INCLUDE_RVC

// =======================

   FV_Cover_instr_ADD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_ADD);
   FV_Cover_instr_SUB:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SUB);
   FV_Cover_instr_SLL:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SLL);
   FV_Cover_instr_SLT:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SLT);
   FV_Cover_instr_SLTU: cover property (@(posedge clk) instr_valid |-> decoder.instr_SLTU);
   FV_Cover_instr_XOR:  cover property (@(posedge clk) instr_valid |-> decoder.instr_XOR);
   FV_Cover_instr_SRL:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SRL);
   FV_Cover_instr_SRA:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SRA);
   FV_Cover_instr_OR:   cover property (@(posedge clk) instr_valid |-> decoder.instr_OR);
   FV_Cover_instr_AND:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AND);
`ifdef FV_INCLUDE_RV64
   FV_Cover_instr_ADDW: cover property (@(posedge clk) instr_valid |-> decoder.instr_ADDW);
   FV_Cover_instr_SUBW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SUBW);
   FV_Cover_instr_SLLW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SLLW);
   FV_Cover_instr_SRLW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SRLW);
   FV_Cover_instr_SRAW: cover property (@(posedge clk) instr_valid |-> decoder.instr_SRAW);
`endif

`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CSUB:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSUB);
   FV_Cover_instr_CXOR:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CXOR);
   FV_Cover_instr_COR:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_COR);
   FV_Cover_instr_CAND:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CAND);
 `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_CSUBW: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSUBW);
   FV_Cover_instr_CADDW: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADDW);
 `endif
   FV_Cover_instr_CADD:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CADD);
`endif //  `ifdef FV_INCLUDE_RVC

// =======================

   FV_Cover_instr_LUI:   cover property (@(posedge clk) instr_valid |-> decoder.instr_LUI);
   FV_Cover_instr_AUIPC: cover property (@(posedge clk) instr_valid |-> decoder.instr_AUIPC);
`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CNOP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CNOP);
   FV_Cover_instr_CLI:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLI);
   FV_Cover_instr_CLUI:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLUI);
   FV_Cover_instr_CMV:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CMV);
`endif

// =======================

   FV_Cover_instr_MUL:    cover property (@(posedge clk) instr_valid |-> decoder.instr_MUL);
   FV_Cover_instr_MULH:   cover property (@(posedge clk) instr_valid |-> decoder.instr_MULH);
   FV_Cover_instr_MULHSU: cover property (@(posedge clk) instr_valid |-> decoder.instr_MULHSU);
   FV_Cover_instr_MULHU:  cover property (@(posedge clk) instr_valid |-> decoder.instr_MULHU);
   FV_Cover_instr_DIV:    cover property (@(posedge clk) instr_valid |-> decoder.instr_DIV);
   FV_Cover_instr_DIVU:   cover property (@(posedge clk) instr_valid |-> decoder.instr_DIVU);
   FV_Cover_instr_REM:    cover property (@(posedge clk) instr_valid |-> decoder.instr_REM);
   FV_Cover_instr_REMU:   cover property (@(posedge clk) instr_valid |-> decoder.instr_REMU);
`ifdef FV_INCLUDE_RV64
   FV_Cover_instr_MULW:   cover property (@(posedge clk) instr_valid |-> decoder.instr_MULW);
   FV_Cover_instr_DIVW:   cover property (@(posedge clk) instr_valid |-> decoder.instr_DIVW);
   FV_Cover_instr_DIVUW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_DIVUW);
   FV_Cover_instr_REMW:   cover property (@(posedge clk) instr_valid |-> decoder.instr_REMW);
   FV_Cover_instr_REMUW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_REMUW);
`endif

// =======================

   FV_Cover_instr_LB:  cover property (@(posedge clk) instr_valid |-> decoder.instr_LB);
   FV_Cover_instr_LH:  cover property (@(posedge clk) instr_valid |-> decoder.instr_LH);
   FV_Cover_instr_LW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_LW);
   FV_Cover_instr_LBU: cover property (@(posedge clk) instr_valid |-> decoder.instr_LBU);
   FV_Cover_instr_LHU: cover property (@(posedge clk) instr_valid |-> decoder.instr_LHU);
   FV_Cover_instr_SB:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SB);
   FV_Cover_instr_SH:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SH);
   FV_Cover_instr_SW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SW);
`ifdef FV_INCLUDE_RV64
   FV_Cover_instr_LWU: cover property (@(posedge clk) instr_valid |-> decoder.instr_LWU);
   FV_Cover_instr_LD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_LD);
   FV_Cover_instr_SD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_SD);
`endif

`ifdef FV_INCLUDE_RVF
   FV_Cover_instr_FLW: cover property (@(posedge clk) instr_valid |-> decoder.instr_FLW);
   FV_Cover_instr_FSW: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSW);
 `ifdef FV_INCLUDE_RVD
   FV_Cover_instr_FLD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FLD);
   FV_Cover_instr_FSD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSD);
 `endif //  `ifdef FV_INCLUDE_RVD
`endif //  `ifdef FV_INCLUDE_RVF

`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CLW:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLW);
   FV_Cover_instr_CSW:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSW);
   FV_Cover_instr_CLWSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLWSP);
   FV_Cover_instr_CSWSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSWSP);
 `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_CLD:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLD);
   FV_Cover_instr_CSD:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSD);
   FV_Cover_instr_CLDSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLDSP);
   FV_Cover_instr_CSDSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSDSP);
 `else
  `ifdef FV_INCLUDE_RVF
   FV_Cover_instr_CFLW:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFLW);
   FV_Cover_instr_CFSW:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFSW);
   FV_Cover_instr_CFLWSP: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFLWSP);
   FV_Cover_instr_CFSWSP: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFSWSP);
  `endif
 `endif
 `ifdef FV_INCLUDE_RV128
   FV_Cover_instr_CLQ:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLQ);
   FV_Cover_instr_CSQ:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSQ);
   FV_Cover_instr_CLQSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CLQSP);
   FV_Cover_instr_CSQSP:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CSQSP);
 `else
  `ifdef FV_INCLUDE_RVD
   FV_Cover_instr_CFLD:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFLD);
   FV_Cover_instr_CFSD:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFSD);
   FV_Cover_instr_CFLDSP: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFLDSP);
   FV_Cover_instr_CFSDSP: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CFSDSP);
  `endif
 `endif
`endif //  `ifdef FV_INCLUDE_RVC

// ================================

   FV_Cover_instr_BEQ:   cover property (@(posedge clk) instr_valid |-> decoder.instr_BEQ);
   FV_Cover_instr_BNE:   cover property (@(posedge clk) instr_valid |-> decoder.instr_BNE);
   FV_Cover_instr_BLT:   cover property (@(posedge clk) instr_valid |-> decoder.instr_BLT);
   FV_Cover_instr_BGE:   cover property (@(posedge clk) instr_valid |-> decoder.instr_BGE);
   FV_Cover_instr_BLTU:  cover property (@(posedge clk) instr_valid |-> decoder.instr_BLTU);
   FV_Cover_instr_BGEU:  cover property (@(posedge clk) instr_valid |-> decoder.instr_BGEU);
   FV_Cover_instr_JAL:   cover property (@(posedge clk) instr_valid |-> decoder.instr_JAL);
   FV_Cover_instr_JALR:  cover property (@(posedge clk) instr_valid |-> decoder.instr_JALR);
`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CBEQZ: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CBEQZ);
   FV_Cover_instr_CBNEZ: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CBNEZ);
  `ifndef FV_INCLUDE_RV64
   FV_Cover_instr_CJAL:  cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CJAL);
  `endif
   FV_Cover_instr_CJ:    cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CJ);
   FV_Cover_instr_CJR:   cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CJR);
   FV_Cover_instr_CJALR: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CJALR);
`endif

// =======================

   FV_Cover_instr_ECALL:   cover property (@(posedge clk) instr_valid |-> decoder.instr_ECALL);
   FV_Cover_instr_EBREAK:  cover property (@(posedge clk) instr_valid |-> decoder.instr_EBREAK);
`ifdef FV_INCLUDE_RVC
   FV_Cover_instr_CEBREAK: cover property (@(posedge clk) instr_valid |-> decoder_rvc.instr_CEBREAK);
`endif

// =======================

   FV_Cover_instr_FENCE:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FENCE);
   FV_Cover_instr_FENCE_I: cover property (@(posedge clk) instr_valid |-> decoder.instr_FENCE_I);

// =======================

`ifdef FV_INCLUDE_RVA
   FV_Cover_instr_LRW:      cover property (@(posedge clk) instr_valid |-> decoder.instr_LRW);
   FV_Cover_instr_SCW:      cover property (@(posedge clk) instr_valid |-> decoder.instr_SCW);
   FV_Cover_instr_AMOSWAPW: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOSWAPW);
   FV_Cover_instr_AMOADDW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOADDW);
   FV_Cover_instr_AMOXORW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOXORW);
   FV_Cover_instr_AMOANDW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOANDW);
   FV_Cover_instr_AMOORW:   cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOORW);
   FV_Cover_instr_AMOMINW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMINW);
   FV_Cover_instr_AMOMAXW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMAXW);
   FV_Cover_instr_AMOMINUW: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMINUW);
   FV_Cover_instr_AMOMAXUW: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMAXUW);
 `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_LRD:      cover property (@(posedge clk) instr_valid |-> decoder.instr_LRD);
   FV_Cover_instr_SCD:      cover property (@(posedge clk) instr_valid |-> decoder.instr_SCD);
   FV_Cover_instr_AMOSWAPD: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOSWAPD);
   FV_Cover_instr_AMOADDD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOADDD);
   FV_Cover_instr_AMOXORD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOXORD);
   FV_Cover_instr_AMOANDD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOANDD);
   FV_Cover_instr_AMOORD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOORD);
   FV_Cover_instr_AMOMIND:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMIND);
   FV_Cover_instr_AMOMAXD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMAXD);
   FV_Cover_instr_AMOMINUD: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMINUD);
   FV_Cover_instr_AMOMAXUD: cover property (@(posedge clk) instr_valid |-> decoder.instr_AMOMAXUD);
 `endif //  `ifdef FV_INCLUDE_RV64
`endif //  `ifdef FV_INCLUDE_RVA

// =======================

`ifdef FV_INCLUDE_RVF
   FV_Cover_instr_FMADDS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FMADDS);
   FV_Cover_instr_FMSUBS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FMSUBS);
   FV_Cover_instr_FNMSUBS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FNMSUBS);
   FV_Cover_instr_FNMADDS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FNMADDS);
   FV_Cover_instr_FADDS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FADDS);
   FV_Cover_instr_FSUBS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FSUBS);
   FV_Cover_instr_FMULS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMULS);
   FV_Cover_instr_FDIVS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FDIVS);
   FV_Cover_instr_FSQRTS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FSQRTS);
   FV_Cover_instr_FSGNJS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJS);
   FV_Cover_instr_FSGNJNS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJNS);
   FV_Cover_instr_FSGNJXS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJXS);
   FV_Cover_instr_FMINS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMINS);
   FV_Cover_instr_FMAXS:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMAXS);
   FV_Cover_instr_FCVTWS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTWS);
   FV_Cover_instr_FCVTWUS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTWUS);
   FV_Cover_instr_FMVXW:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMVXW);
   FV_Cover_instr_FEQS:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FEQS);
   FV_Cover_instr_FLTS:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FLTS);
   FV_Cover_instr_FLES:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FLES);
   FV_Cover_instr_FCLASSS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCLASSS);
   FV_Cover_instr_FCVTSW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTSW);
   FV_Cover_instr_FCVTSWU: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTSWU);
   FV_Cover_instr_FMVWX:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMVWX);
 `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_FCVTLS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTLS);
   FV_Cover_instr_FCVTLUS: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTLUS);
   FV_Cover_instr_FCVTSL:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTSL);
   FV_Cover_instr_FCVTSLU: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTSLU);
 `endif
 `ifdef FV_INCLUDE_RVD
   FV_Cover_instr_FMADDD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FMADDD);
   FV_Cover_instr_FMSUBD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FMSUBD);
   FV_Cover_instr_FNMSUBD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FNMSUBD);
   FV_Cover_instr_FNMADDD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FNMADDD);
   FV_Cover_instr_FADDD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FADDD);
   FV_Cover_instr_FSUBD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FSUBD);
   FV_Cover_instr_FMULD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMULD);
   FV_Cover_instr_FDIVD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FDIVD);
   FV_Cover_instr_FSQRTD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FSQRTD);
   FV_Cover_instr_FSGNJD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJD);
   FV_Cover_instr_FSGNJND: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJND);
   FV_Cover_instr_FSGNJXD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FSGNJXD);
   FV_Cover_instr_FMIND:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMIND);
   FV_Cover_instr_FMAXD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMAXD);
   FV_Cover_instr_FCVTSD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTSD);
   FV_Cover_instr_FCVTDS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTDS);
   FV_Cover_instr_FEQD:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FEQD);
   FV_Cover_instr_FLTD:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FLTD);
   FV_Cover_instr_FLED:    cover property (@(posedge clk) instr_valid |-> decoder.instr_FLED);
   FV_Cover_instr_FCLASSD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCLASSD);
   FV_Cover_instr_FCVTWD : cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTWD );
   FV_Cover_instr_FCVTWUD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTWUD);
   FV_Cover_instr_FCVTDW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTDW);
   FV_Cover_instr_FCVTDWU: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTDWU);
  `ifdef FV_INCLUDE_RV64
   FV_Cover_instr_FCVTLD:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTLD);
   FV_Cover_instr_FCVTLUD: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTLUD);
   FV_Cover_instr_FMVXD:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMVXD);
   FV_Cover_instr_FCVTDL:  cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTDL);
   FV_Cover_instr_FCVTDLU: cover property (@(posedge clk) instr_valid |-> decoder.instr_FCVTDLU);
   FV_Cover_instr_FMVDX:   cover property (@(posedge clk) instr_valid |-> decoder.instr_FMVDX);
  `endif
 `endif //  `ifdef FV_INCLUDE_RVD
`endif //  `ifdef FV_INCLUDE_RVF

`ifdef FV_INCLUDE_RVZICSR
   FV_Cover_instr_CSRRW:  cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRW);
   FV_Cover_instr_CSRRS:  cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRS);
   FV_Cover_instr_CSRRC:  cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRC);
   FV_Cover_instr_CSRRWI: cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRWI);
   FV_Cover_instr_CSRRSI: cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRSI);
   FV_Cover_instr_CSRRCI: cover property (@(posedge clk) instr_valid |-> decoder.instr_CSRRCI);
`endif

endmodule // FV_COV_instructions

