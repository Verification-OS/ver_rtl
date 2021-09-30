
module FV_PROP_si(
		      input logic clk,
		      input si_prop_signals_t ps
		      );

`include "FV_SI_latencies_dut.svh"

`ifdef FV_INCLUDE_RV64
   wire [63:0] si_expected_dmem_ld_value = ps.si_dmem_ld_value_32b_sign_extended;   
`else
   wire [31:0] si_expected_dmem_ld_value = ps.si_dmem_ld_value[31:0];
`endif   
   
   always @(posedge clk) begin

      FV_si_check_ADDI:  assert property((ps.si_check_ADDI)  |-> ##(`FV_SI_LATENCY_ADD)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  +           ps.si_imm12_signed_ext)));
      FV_si_check_SLTI:  assert property((ps.si_check_SLTI ) |-> ##(`FV_SI_LATENCY_SLT)  (        ps.si_rf_probe_rd_value  == (  $signed(ps.si_rs1_value) <   $signed(ps.si_imm12_signed_ext))));
      FV_si_check_SLTIU: assert property((ps.si_check_SLTIU) |-> ##(`FV_SI_LATENCY_SLTU) (        ps.si_rf_probe_rd_value  == ($unsigned(ps.si_rs1_value) < $unsigned(ps.si_imm12_signed_ext))));
      FV_si_check_XORI:  assert property((ps.si_check_XORI ) |-> ##(`FV_SI_LATENCY_XOR)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  ^           ps.si_imm12_signed_ext)));
      FV_si_check_ORI:   assert property((ps.si_check_ORI  ) |-> ##(`FV_SI_LATENCY_OR)   (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  |           ps.si_imm12_signed_ext)));
      FV_si_check_ANDI:  assert property((ps.si_check_ANDI ) |-> ##(`FV_SI_LATENCY_AND)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  &           ps.si_imm12_signed_ext)));
      FV_si_check_SLLI:  assert property((ps.si_check_SLLI ) |-> ##(`FV_SI_LATENCY_SLL)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  <<          ps.si_shamt)));
      FV_si_check_SRLI:  assert property((ps.si_check_SRLI ) |-> ##(`FV_SI_LATENCY_SRL)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  >>          ps.si_shamt)));
      FV_si_check_SRAI:  assert property((ps.si_check_SRAI ) |-> ##(`FV_SI_LATENCY_SRA)  ($signed(ps.si_rf_probe_rd_value) == (  $signed(ps.si_rs1_value) >>>         ps.si_shamt)));
      
      FV_si_check_ADD:  assert property((ps.si_check_ADD ) |-> ##(`FV_SI_LATENCY_ADD)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  +           ps.si_rs2_value)));
      FV_si_check_SUB:  assert property((ps.si_check_SUB ) |-> ##(`FV_SI_LATENCY_SUB)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  -           ps.si_rs2_value)));
      FV_si_check_SLL:  assert property((ps.si_check_SLL ) |-> ##(`FV_SI_LATENCY_SLL)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  <<          ps.si_rs2_value[`FV_SHAMT_WIDTH-1:0])));
      FV_si_check_SLT:  assert property((ps.si_check_SLT ) |-> ##(`FV_SI_LATENCY_SLT)  (        ps.si_rf_probe_rd_value  == (  $signed(ps.si_rs1_value) <   $signed(ps.si_rs2_value))));
      FV_si_check_SLTU: assert property((ps.si_check_SLTU) |-> ##(`FV_SI_LATENCY_SLTU) (        ps.si_rf_probe_rd_value  == ($unsigned(ps.si_rs1_value) < $unsigned(ps.si_rs2_value))));
      FV_si_check_XOR:  assert property((ps.si_check_XOR ) |-> ##(`FV_SI_LATENCY_XOR)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  ^           ps.si_rs2_value)));
      FV_si_check_SRL:  assert property((ps.si_check_SRL ) |-> ##(`FV_SI_LATENCY_SRL)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  >>          ps.si_rs2_value[`FV_SHAMT_WIDTH-1:0])));
      FV_si_check_SRA:  assert property((ps.si_check_SRA ) |-> ##(`FV_SI_LATENCY_SRA)  ($signed(ps.si_rf_probe_rd_value) == (  $signed(ps.si_rs1_value) >>>         ps.si_rs2_value[`FV_SHAMT_WIDTH-1:0])));
      FV_si_check_OR:   assert property((ps.si_check_OR  ) |-> ##(`FV_SI_LATENCY_OR)   (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  |           ps.si_rs2_value)));
      FV_si_check_AND:  assert property((ps.si_check_AND ) |-> ##(`FV_SI_LATENCY_AND)  (        ps.si_rf_probe_rd_value  == (          ps.si_rs1_value  &           ps.si_rs2_value)));

  `ifdef FV_INCLUDE_RV32M  
      FV_si_check_MUL:    assert property((ps.si_check_MUL   ) |-> ##(`FV_SI_LATENCY_MUL)    (ps.si_rf_probe_rd_value  == ($unsigned(ps.si_rs1_value) * $unsigned(ps.si_rs2_value))));
      FV_si_check_MULH:   assert property((ps.si_check_MULH  ) |-> ##(`FV_SI_LATENCY_MULH)   (ps.si_rf_probe_rd_value  ==   ps.si_mul_result[63:32]));
      FV_si_check_MULHSU: assert property((ps.si_check_MULHSU) |-> ##(`FV_SI_LATENCY_MULHSU) (ps.si_rf_probe_rd_value  == ps.si_mulsu_result[63:32]));
      FV_si_check_MULHU:  assert property((ps.si_check_MULHU ) |-> ##(`FV_SI_LATENCY_MULHU)  (ps.si_rf_probe_rd_value  ==  ps.si_mulu_result[63:32]));
   `ifndef FV_EXCLUDE_RV32M_DIV
      FV_si_check_DIV:  assert property((ps.si_check_DIV ) |-> ##(`FV_SI_LATENCY_DIV)  (((ps.si_rs2_value == 0) && (ps.si_rf_probe_rd_value  == 32'hffffffff)) || 
											      ((ps.si_rs2_value != 0) && (ps.si_rf_probe_rd_value  == ps.si_div_result  ))));
      FV_si_check_DIVU: assert property((ps.si_check_DIVU) |-> ##(`FV_SI_LATENCY_DIVU) (((ps.si_rs2_value == 0) && (ps.si_rf_probe_rd_value  == 32'hffffffff)) || 
											      ((ps.si_rs2_value != 0) && (ps.si_rf_probe_rd_value  == ps.si_divu_result ))));
      FV_si_check_REM:  assert property((ps.si_check_REM ) |-> ##(`FV_SI_LATENCY_REM)  (((ps.si_rs2_value == 0) && (ps.si_rf_probe_rd_value  == ps.si_rs1_value)) || 
											      ((ps.si_rs2_value != 0) && (ps.si_rf_probe_rd_value  == ps.si_rem_result  ))));
      FV_si_check_REMU: assert property((ps.si_check_REMU) |-> ##(`FV_SI_LATENCY_REMU) (((ps.si_rs2_value == 0) && (ps.si_rf_probe_rd_value  == ps.si_rs1_value)) || 
											      ((ps.si_rs2_value != 0) && (ps.si_rf_probe_rd_value  == ps.si_remu_result ))));
   `endif
  `endif //  `ifdef FV_INCLUDE_RV32M

      FV_si_check_LUI:   assert property((ps.si_check_LUI  ) |-> ##(`FV_SI_LATENCY_LUI)   (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-32){ps.si_instr[31]}}, ps.si_instr[31:12], 12'b0}));
      FV_si_check_AUIPC: assert property((ps.si_check_AUIPC) |-> ##(`FV_SI_LATENCY_AUIPC) (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-32){ps.si_instr[31]}}, ps.si_instr[31:12], 12'b0} + ps.si_pc));
      
      FV_si_check_LB:  assert property((ps.si_check_LB ) |-> ##(`FV_SI_LATENCY_LB)  (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH- 8){ps.si_dmem_ld_value[7] }}, ps.si_dmem_ld_value[7:0]}));
      FV_si_check_LH:  assert property((ps.si_check_LH ) |-> ##(`FV_SI_LATENCY_LH)  (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-16){ps.si_dmem_ld_value[15]}}, ps.si_dmem_ld_value[15:0]}));
      FV_si_check_LW:  assert property((ps.si_check_LW ) |-> ##(`FV_SI_LATENCY_LW)  (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-32){ps.si_dmem_ld_value[31]}}, ps.si_dmem_ld_value[31:0]}));
      FV_si_check_LBU: assert property((ps.si_check_LBU) |-> ##(`FV_SI_LATENCY_LBU) (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH- 8){1'b0}}                   , ps.si_dmem_ld_value[7:0]}));
      FV_si_check_LHU: assert property((ps.si_check_LHU) |-> ##(`FV_SI_LATENCY_LHU) (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-16){1'b0}}                   , ps.si_dmem_ld_value[15:0]}));

      FV_si_check_SB:  assert property((ps.si_check_SB)  |-> ##(`FV_SI_LATENCY_SB) (ps.si_dmem_8byte_value == ps.si_expected_dmem_8byte_value));
      FV_si_check_SH:  assert property((ps.si_check_SH)  |-> ##(`FV_SI_LATENCY_SH) (ps.si_dmem_8byte_value == ps.si_expected_dmem_8byte_value));
      FV_si_check_SW:  assert property((ps.si_check_SW)  |-> ##(`FV_SI_LATENCY_SW) (ps.si_dmem_8byte_value == ps.si_expected_dmem_8byte_value));

      // NOTE: The following JAL/JALR checks only check the return address saving in rd register.  Correct next PC is checked by the FV_CF property in the parent module.
      FV_si_check_JAL:  assert property((ps.si_check_JAL ) |-> ##(`FV_SI_LATENCY_JMP) (ps.si_rf_probe_rd_value  == (ps.si_pc + 4)));
      FV_si_check_JALR: assert property((ps.si_check_JALR) |-> ##(`FV_SI_LATENCY_JMP) (ps.si_rf_probe_rd_value  == (ps.si_pc + 4)));

/* 
  NOTE1: The following control-flow instructions are checked by the FV_CF property in the parent module.
    instr_BEQ, instr_BNE, instr_BLT, instr_BGE, instr_BLTU, instr_BGEU,
    instr_ECALL, instr_EBREAK

  NOTE2: The following instructions are not implemented yet
    instr_FENCE, instr_FENCE_I
    CSR instructions (many as it is a cross-product of different access types and different registers)
 */

  `ifdef FV_INCLUDE_RV64
      FV_si_check_LWU: assert property((ps.si_check_LWU) |-> ##(`FV_SI_LATENCY_LWU) (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-32){1'b0}}, ps.si_dmem_ld_value[31:0]}));
      FV_si_check_LD:  assert property((ps.si_check_LD)  |-> ##(`FV_SI_LATENCY_LD)  (ps.si_rf_probe_rd_value  == {{(`FV_REG_WIDTH-64){1'b0}}, ps.si_dmem_ld_value[63:0]}));

      FV_si_check_SD:  assert property((ps.si_check_SD)  |-> ##(`FV_SI_LATENCY_SD)  (ps.si_dmem_8byte_value == ps.si_expected_dmem_8byte_value));
  `endif

  `ifdef FV_INCLUDE_RVA

     // LR/SC instructions to be added
      FV_si_check_AMOSWAPW:  assert property((ps.si_check_AMOSWAPW ) |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
					                                                                 (ps.si_dmem_8byte_value       ==  ps.si_expected_dmem_8byte_value)));
      FV_si_check_AMOADDW:   assert property((ps.si_check_AMOADDW )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
					                                                                 (ps.si_dmem_8byte_value[31:0] == (ps.si_dmem_ld_value[31:0] + ps.si_rs2_value[31:0]))));
      FV_si_check_AMOXORW:   assert property((ps.si_check_AMOXORW )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
					                                                                 (ps.si_dmem_8byte_value[31:0] == (ps.si_dmem_ld_value[31:0] ^ ps.si_rs2_value[31:0]))));
      FV_si_check_AMOANDW:   assert property((ps.si_check_AMOANDW )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
					                                                                 (ps.si_dmem_8byte_value[31:0] == (ps.si_dmem_ld_value[31:0] & ps.si_rs2_value[31:0]))));
      FV_si_check_AMOORW:    assert property((ps.si_check_AMOORW  )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
					                                                                 (ps.si_dmem_8byte_value[31:0] == (ps.si_dmem_ld_value[31:0] | ps.si_rs2_value[31:0]))));
      FV_si_check_AMOMINW:   assert property((ps.si_check_AMOMINW )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
												         (($signed(ps.si_dmem_ld_value[31:0]) <  $signed(ps.si_rs2_value[31:0])) ?
					                                                                 (ps.si_dmem_8byte_value[31:0] ==  ps.si_dmem_ld_value[31:0]) :
													 (ps.si_dmem_8byte_value[31:0] ==  ps.si_rs2_value[31:0]))));
      FV_si_check_AMOMAXW:   assert property((ps.si_check_AMOMAXW )  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
												         (($signed(ps.si_dmem_ld_value[31:0]) >  $signed(ps.si_rs2_value[31:0])) ?
					                                                                 (ps.si_dmem_8byte_value[31:0] ==  ps.si_dmem_ld_value[31:0]) :
													 (ps.si_dmem_8byte_value[31:0] ==  ps.si_rs2_value[31:0]))));
      FV_si_check_AMOMINUW:  assert property((ps.si_check_AMOMINUW)  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
												         (($unsigned(ps.si_dmem_ld_value[31:0]) <  $unsigned(ps.si_rs2_value[31:0])) ?
					                                                                 (ps.si_dmem_8byte_value[31:0] ==  ps.si_dmem_ld_value[31:0]) :
													 (ps.si_dmem_8byte_value[31:0] ==  ps.si_rs2_value[31:0]))));
      FV_si_check_AMOMAXUW:  assert property((ps.si_check_AMOMAXUW)  |-> ##(`FV_SI_LATENCY_AMOW)  ((ps.si_rf_probe_rd_value      ==  si_expected_dmem_ld_value)  &&
												         (($unsigned(ps.si_dmem_ld_value[31:0]) >  $unsigned(ps.si_rs2_value[31:0])) ?
					                                                                 (ps.si_dmem_8byte_value[31:0] ==  ps.si_dmem_ld_value[31:0]) :
													 (ps.si_dmem_8byte_value[31:0] ==  ps.si_rs2_value[31:0]))));

   `ifdef FV_INCLUDE_RV64

      FV_si_check_AMOSWAPD:  assert property((ps.si_check_AMOSWAPD ) |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
					                                                                 (ps.si_dmem_8byte_value   ==  ps.si_expected_dmem_8byte_value)));
      FV_si_check_AMOADDD:   assert property((ps.si_check_AMOADDD )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
					                                                                 (ps.si_dmem_8byte_value   == (ps.si_dmem_ld_value[63:0] + ps.si_rs2_value))));
      FV_si_check_AMOXORD:   assert property((ps.si_check_AMOXORD )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
					                                                                 (ps.si_dmem_8byte_value   == (ps.si_dmem_ld_value[63:0] ^ ps.si_rs2_value))));
      FV_si_check_AMOANDD:   assert property((ps.si_check_AMOANDD )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
					                                                                 (ps.si_dmem_8byte_value   == (ps.si_dmem_ld_value[63:0] & ps.si_rs2_value))));
      FV_si_check_AMOORD:    assert property((ps.si_check_AMOORD  )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
					                                                                 (ps.si_dmem_8byte_value   == (ps.si_dmem_ld_value[63:0] | ps.si_rs2_value))));
      FV_si_check_AMOMIND:   assert property((ps.si_check_AMOMIND )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
												         (($signed(ps.si_dmem_ld_value[63:0]) <  $signed(ps.si_rs2_value)) ?
					                                                                 (ps.si_dmem_8byte_value   ==  ps.si_dmem_ld_value[63:0]) :
													 (ps.si_dmem_8byte_value   ==  ps.si_rs2_value))));
      FV_si_check_AMOMAXD:   assert property((ps.si_check_AMOMAXD )  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
												         (($signed(ps.si_dmem_ld_value[63:0]) >  $signed(ps.si_rs2_value)) ?
					                                                                 (ps.si_dmem_8byte_value   ==  ps.si_dmem_ld_value[63:0]) :
													 (ps.si_dmem_8byte_value   ==  ps.si_rs2_value))));
      FV_si_check_AMOMINUD:  assert property((ps.si_check_AMOMINUD)  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
												         (($unsigned(ps.si_dmem_ld_value[63:0]) <  $unsigned(ps.si_rs2_value)) ?
					                                                                 (ps.si_dmem_8byte_value   ==  ps.si_dmem_ld_value[63:0]) :
													 (ps.si_dmem_8byte_value   ==  ps.si_rs2_value))));
      FV_si_check_AMOMAXUD:  assert property((ps.si_check_AMOMAXUD)  |-> ##(`FV_SI_LATENCY_AMOD)  ((ps.si_rf_probe_rd_value  ==  ps.si_dmem_ld_value[63:0])  &&
												         (($unsigned(ps.si_dmem_ld_value[63:0]) >  $unsigned(ps.si_rs2_value)) ?
					                                                                 (ps.si_dmem_8byte_value   ==  ps.si_dmem_ld_value[63:0]) :
													 (ps.si_dmem_8byte_value   ==  ps.si_rs2_value))));

   `endif //  `ifdef FV_INCLUDE_RV64

  `endif //  `ifdef FV_INCLUDE_RVA

   end

endmodule // FV_PROP_si
