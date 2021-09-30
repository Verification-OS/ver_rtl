
// =========================
// ISA-independednt common and shared modules

module FV_delay_signal #(parameter DELAY_AMOUNT=1, 
			     parameter MAX_DELAY=10,
			     parameter DATA_WIDTH=1,
			     parameter RESET_VALUE=0)
                            (input logic                   clk,
			     input logic 		   reset_,
			     input logic [DATA_WIDTH-1:0]  in,
			     output logic [DATA_WIDTH-1:0] out);

   logic [MAX_DELAY-1:0][DATA_WIDTH-1:0] shift_reg;
   logic [MAX_DELAY:0][DATA_WIDTH-1:0]	 in_delayed;

   logic [DATA_WIDTH-1:0] 		 reset_val;
   assign reset_val = RESET_VALUE;
   
   always @(posedge clk) begin
      if (!reset_)
	shift_reg <= {MAX_DELAY{reset_val}};
      else
	shift_reg <= {shift_reg[MAX_DELAY-2:0], in};
   end

   assign in_delayed = {shift_reg[MAX_DELAY-1:0], in};
   assign out = in_delayed[DELAY_AMOUNT];
   
endmodule // FV_delay_signal

// =====================
// ISA-dependent section

function logic FV_FUNC_is_orig_reg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] reg_num);

`ifdef FV_DUP_NEW_PAIRING
   FV_FUNC_is_orig_reg  = ((reg_num % 8) < 4) && (reg_num < `FV_NUM_RF_REGS);
`else
   FV_FUNC_is_orig_reg  = (reg_num < (`FV_NUM_RF_REGS/2));
`endif
   
endfunction // FV_FUNC_is_orig_reg

function logic FV_FUNC_is_dup_reg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] reg_num);

`ifdef FV_DUP_NEW_PAIRING
   FV_FUNC_is_dup_reg  = ((reg_num % 8) >= 4);
`else
   FV_FUNC_is_dup_reg  = (reg_num >= (`FV_NUM_RF_REGS/2));
`endif
   
endfunction // FV_FUNC_is_dup_reg

function logic FV_FUNC_orig_rs_limit (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   logic [`FV_RV32_REG_ADDR_WIDTH:0] reg_int;
   reg_int = {1'b0, orig_reg};

   FV_FUNC_orig_rs_limit =    
`ifdef FV_SPLIT_RF_DMEM_SPACE
 `ifdef FV_DUP_NEW_PAIRING
			       FV_FUNC_is_orig_reg(orig_reg) &&
  `ifndef FV_DUP_PAIR_R1
			       (orig_reg != 1) &&
  `endif
 `else
			       (reg_int < (`FV_NUM_RS_PAIRS)) &&
 `endif
`else
			       (reg_int < (`FV_NUM_RF_REGS))  &&
`endif
				1'b1;

endfunction // FV_FUNC_orig_rs_limit

function logic FV_FUNC_orig_rd_limit (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   logic [`FV_RV32_REG_ADDR_WIDTH:0] reg_int;
   reg_int = {1'b0, orig_reg};

   FV_FUNC_orig_rd_limit =    
`ifdef FV_SPLIT_RF_DMEM_SPACE
 `ifdef FV_DUP_NEW_PAIRING
			       FV_FUNC_is_orig_reg(orig_reg) &&
  // Note: Note? if rf_lock/unlock is in effect and working, no need to limit RD for `ifndef FV_DUP_PAIR_R1
  `ifndef FV_DUP_PAIR_R1
			       (orig_reg != 1) &&
  `endif

 `else
                               (reg_int < (`FV_NUM_RD_PAIRS)) &&
 `endif
`elsif FV_ENABLE_SI
   // destination register should not be r0 for single-instruction checks
                               (reg_int < (`FV_NUM_RF_REGS)) && (reg_int != 0) &&
`else
                               (reg_int < (`FV_NUM_RF_REGS)) &&
`endif
				1'b1;
				  
endfunction // FV_FUNC_orig_rd_limit

function logic FV_FUNC_orig_rd_limit_jal (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   logic [`FV_RV32_REG_ADDR_WIDTH:0] reg_int;
   reg_int = {1'b0, orig_reg};

   FV_FUNC_orig_rd_limit_jal =    
`ifdef FV_SPLIT_RF_DMEM_SPACE
 `ifdef FV_LIMIT_JAL_RD
                               (reg_int == `FV_LIMIT_JAL_RD) &&
 `else
  `ifdef FV_DUP_NEW_PAIRING
			       FV_FUNC_is_orig_reg(orig_reg) &&
  `else
                               (reg_int < (`FV_NUM_RD_PAIRS)) &&
  `endif
 `endif
`elsif FV_ENABLE_SI
   // destination register should not be r0 for single-instruction checks
                               (reg_int < (`FV_NUM_RF_REGS)) && (reg_int != 0) &&
`else
                               (reg_int < (`FV_NUM_RF_REGS)) &&
`endif
				1'b1;
				  
endfunction // FV_FUNC_orig_rd_limit_jal

function logic FV_FUNC_orig_frsd_limit (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   FV_FUNC_orig_frsd_limit =    
`ifdef FV_SPLIT_RF_DMEM_SPACE
			       FV_FUNC_is_orig_reg(orig_reg) &&
`endif
				1'b1;

endfunction // FV_FUNC_orig_rs_limit

function logic [`FV_RV32_REG_ADDR_WIDTH-1:0] FV_FUNC_dup_reg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

`ifdef FV_DUP_NEW_PAIRING
      FV_FUNC_dup_reg  = (orig_reg  == `FV_RV32_REG_ADDR_WIDTH'b0) ? orig_reg  : (orig_reg + 4);
`else
 `ifdef FV_RV32E
   FV_FUNC_dup_reg  = (orig_reg  == `FV_RV32_REG_ADDR_WIDTH'b0) ? orig_reg  : {2'b01, orig_reg[2:0]};
 `else
   FV_FUNC_dup_reg  = (orig_reg  == `FV_RV32_REG_ADDR_WIDTH'b0) ? orig_reg  : {1'b1, orig_reg[3:0]};
 `endif
`endif
   
endfunction // FV_FUNC_dup_reg

function logic [`FV_RV32_REG_ADDR_WIDTH-1:0] FV_FUNC_dup_freg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   FV_FUNC_dup_freg  = orig_reg + 4;
   
endfunction // FV_FUNC_dup_freg

// Note1: needs to be revised for supporting LMUL=8
function logic [`FV_RV32_REG_ADDR_WIDTH-1:0] FV_FUNC_dup_vreg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] orig_reg);

   FV_FUNC_dup_vreg  = orig_reg + 4;
   
endfunction // FV_FUNC_dup_vreg

// Note0: temp mapping for VRF until new mapping is defined
function logic [`FV_RV32_REG_ADDR_WIDTH-1:0] FV_FUNC_pairs_orig_reg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] pair_num);

`ifdef FV_DUP_NEW_PAIRING
   FV_FUNC_pairs_orig_reg  = ((pair_num / 4) * 8) + (pair_num % 4);
`else
   FV_FUNC_pairs_orig_reg  = pair_num;
`endif
   
endfunction // FV_FUNC_pairs_orig_reg

// Note: separate freg/regs2 and vreg/regs3?
function logic [`FV_RV32_REG_ADDR_WIDTH-1:0] FV_FUNC_pairs_dup_reg (logic [`FV_RV32_REG_ADDR_WIDTH-1:0] pair_num);

`ifdef FV_DUP_NEW_PAIRING
   FV_FUNC_pairs_dup_reg  = FV_FUNC_pairs_orig_reg(pair_num) + 4; // or call FV_FUNC_dup_reg?
`else
   FV_FUNC_pairs_dup_reg  = FV_FUNC_pairs_orig_reg(pair_num) + (`FV_NUM_RF_REGS/2);
`endif
   
endfunction // FV_FUNC_pairs_dup_reg

`ifdef FV_INCLUDE_RVC

// NOTE:
// no separate rsp and rdp functions as the restriction is the same because
// rdp=0 refers to x8, not x0, so no need to exclude value 0 for FV_ENABLE_SI
function logic FV_FUNC_orig_rvc_regp_limit (logic [`FV_RV32C_REGP_ADDR_WIDTH-1:0] orig_reg);

   logic [`FV_RV32C_REG_ADDR_WIDTH-1:0] reg_int;
   reg_int = {2'b0, orig_reg} + 5'd8; // rx == rx' + 8

   FV_FUNC_orig_rvc_regp_limit = 
`ifdef FV_SPLIT_RF_DMEM_SPACE
 `ifdef FV_DUP_NEW_PAIRING
			       FV_FUNC_is_orig_reg(reg_int) &&
 `else
			       (reg_int < (`FV_NUM_RF_REGS/4)) &&
 `endif
`endif
			        1'b1;

endfunction // FV_FUNC_orig_rvc_regp_limit

`endif //  `ifdef FV_INCLUDE_RVC

// =============================

function logic FV_FUNC_instr_is_rvc (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_instr_is_rvc = (instr[`FV_RV32C_INSTR_FIELD_OPCODE] != 2'b11);

endfunction // FV_FUNC_instr_is_rvc

function logic FV_FUNC_is_nop (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_is_nop = (instr == `FV_INSTR_NOP) ||
`ifdef FV_INCLUDE_RVC
			(instr == {{(`FV_INSTR_WIDTH-`FV_RV32C_INSTR_WIDTH){1'b0}}, `FV_RV32C_INSTR_CNOP}) ||
`endif
			1'b0;

endfunction // FV_FUNC_is_nop

function logic FV_FUNC_is_nop_flush (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_is_nop_flush = (instr == `FV_RV_INSTR_NOP_FLUSH);

endfunction // FV_FUNC_is_nop

function logic [`FV_OPCODE_WIDTH-1:0] FV_FUNC_get_opcode (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_get_opcode = instr[`FV_RV32_INSTR_FIELD_OPCODE];

endfunction // FV_FUNC_get_opcode

function logic [`FV_REG_ADDR_WIDTH-1:0] FV_FUNC_get_instr_rs1 (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_get_instr_rs1 = instr[`FV_RV32_INSTR_FIELD_RS1];

`ifdef FV_INCLUDE_RVC
   // need to add?
`endif

endfunction // FV_FUNC_get_instr_rs1

function logic [`FV_REG_ADDR_WIDTH-1:0] FV_FUNC_get_instr_rs2 (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_get_instr_rs2 = instr[`FV_RV32_INSTR_FIELD_RS2];

`ifdef FV_INCLUDE_RVC
   // need to add?
`endif

endfunction // FV_FUNC_get_instr_rs2

function logic [`FV_REG_ADDR_WIDTH-1:0] FV_FUNC_get_instr_rd (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_get_instr_rd = instr[`FV_RV32_INSTR_FIELD_RD];

`ifdef FV_INCLUDE_RVC
   // need to add?
`endif
   
endfunction // FV_FUNC_get_instr_rd

function logic FV_FUNC_instr_is_branch (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0]       opcode;
   logic [`FV_RV32C_OPCODE_WIDTH-1:0] opcode_rvc;
   logic [`FV_RV32C_FUNCT3_WIDTH-1:0] funct3_rvc;

   opcode     = FV_FUNC_get_opcode(instr);
   opcode_rvc = instr[`FV_RV32C_INSTR_FIELD_OPCODE];
   funct3_rvc = instr[`FV_RV32C_INSTR_FIELD_FUNCT3];
  
   FV_FUNC_instr_is_branch = FV_FUNC_instr_is_rvc(instr) ?
				 ( (opcode_rvc == `FV_RV32C_OPCODE_C1) &&
				  ((funct3_rvc == `FV_RV32C_FUNCT3_CBEQZ) ||
				   (funct3_rvc == `FV_RV32C_FUNCT3_CBNEZ))
				  ) :
				 (opcode == `FV_RV_OPCODE_BRANCH);
   
endfunction // FV_FUNC_instr_is_branch

function logic FV_FUNC_instr_is_jal (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0]       opcode;
   logic [`FV_RV32C_OPCODE_WIDTH-1:0] opcode_rvc;
   logic [`FV_RV32C_FUNCT3_WIDTH-1:0] funct3_rvc;

   opcode     = FV_FUNC_get_opcode(instr);
   opcode_rvc = instr[`FV_RV32C_INSTR_FIELD_OPCODE];
   funct3_rvc = instr[`FV_RV32C_INSTR_FIELD_FUNCT3];

   FV_FUNC_instr_is_jal = FV_FUNC_instr_is_rvc(instr) ?
			      ( (opcode_rvc == `FV_RV32C_OPCODE_C1) &&
				((funct3_rvc == `FV_RV32C_FUNCT3_CJ) ||
`ifndef FV_INCLUDE_RV64
				 (funct3_rvc == `FV_RV32C_FUNCT3_CJAL) ||
`endif
				 1'b0)
				) :
			      (opcode == `FV_RV_OPCODE_JAL);

endfunction // FV_FUNC_instr_is_jal

function logic FV_FUNC_instr_is_jalr (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0]       opcode;
   logic [`FV_RV32C_OPCODE_WIDTH-1:0] opcode_rvc;
   logic [`FV_RV32C_FUNCT4_WIDTH-1:0] funct4_rvc;

   opcode     = FV_FUNC_get_opcode(instr);
   opcode_rvc = instr[`FV_RV32C_INSTR_FIELD_OPCODE];
   funct4_rvc = instr[`FV_RV32C_INSTR_FIELD_FUNCT4];

   FV_FUNC_instr_is_jalr = FV_FUNC_instr_is_rvc(instr) ?
			       ( ((opcode_rvc == `FV_RV32C_OPCODE_C2) && 
				  (instr[`FV_RV32C_INSTR_FIELD_RS1] != 0) && 
				  (instr[`FV_RV32C_INSTR_FIELD_RS2] == 0) ) &&
				 ((funct4_rvc == `FV_RV32C_FUNCT4_CJR) ||
				  (funct4_rvc == `FV_RV32C_FUNCT4_CJALR) ||
				  1'b0)
				 ) :
			       (opcode == `FV_RV_OPCODE_JALR);

endfunction // FV_FUNC_instr_is_jalr

function logic FV_FUNC_instr_is_CF_nodup (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0] opcode;

   opcode = FV_FUNC_get_opcode(instr);
   FV_FUNC_instr_is_CF_nodup = (
				    (instr == `FV_RV_INSTR_ECALL) ||
				    (instr == `FV_RV_INSTR_EBREAK) ||
// Note: temporarily include CSRs in this group
				    (opcode == `FV_RV_OPCODE_SYSTEM) ||
`ifndef FV_DUP_BR
				    FV_FUNC_instr_is_jal(instr) ||
				    FV_FUNC_instr_is_jalr(instr) ||
				    FV_FUNC_instr_is_branch(instr) ||
`endif
				    1'b0);   

endfunction // FV_FUNC_instr_is_CF_nodup

function logic FV_FUNC_instr_is_CF_dup_taken (logic [`FV_INSTR_WIDTH-1:0] instr, logic predict_br_taken);

   FV_FUNC_instr_is_CF_dup_taken = (
`ifndef FV_DUT_DIRECT_JMPS_NO_KILL
					FV_FUNC_instr_is_jal(instr) ||
`endif
					FV_FUNC_instr_is_jalr(instr) ||
				       (FV_FUNC_instr_is_branch(instr) && predict_br_taken) ||
					1'b0);   

endfunction // FV_FUNC_instr_is_CF_dup_taken

function logic FV_FUNC_instr_is_CF_checked (logic [`FV_INSTR_WIDTH-1:0] instr);

   FV_FUNC_instr_is_CF_checked = (
				     FV_FUNC_instr_is_jal(instr) ||
				     FV_FUNC_instr_is_jalr(instr) ||
				     FV_FUNC_instr_is_branch(instr) ||
				     1'b0);   

endfunction // FV_FUNC_instr_is_CF_checked

function logic FV_FUNC_instr_causes_flush (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0] opcode;
   logic [`FV_RV32_FUNCT3_WIDTH-1:0] funct3;
   logic [`FV_RV32_REG_ADDR_WIDTH-1:0] rs1;
   
   
   opcode = FV_FUNC_get_opcode(instr);
   funct3 = instr[`FV_RV32_INSTR_FIELD_FUNCT3];
   rs1    = instr[`FV_RV32_INSTR_FIELD_RS1];
   
   FV_FUNC_instr_causes_flush = (
`ifdef FV_DUT_ATOMICS_ALWAYS_FLUSH
				     (opcode == `FV_RV_OPCODE_AMO) ||
`endif
`ifdef FV_DUT_CSR_ALWAYS_FLUSH
				     ((opcode == `FV_RV_OPCODE_SYSTEM) &&
				      (
				       (funct3 == `FV_RV32I_FUNCT3_CSRRW)  ||
				       (funct3 == `FV_RV32I_FUNCT3_CSRRS)  ||
				       (funct3 == `FV_RV32I_FUNCT3_CSRRC)  ||
				       (funct3 == `FV_RV32I_FUNCT3_CSRRWI) ||
				       (funct3 == `FV_RV32I_FUNCT3_CSRRSI) ||
				       (funct3 == `FV_RV32I_FUNCT3_CSRRCI)
				      )
				     ) ||
`endif
`ifdef FV_DUT_CSR_WRITE_ALWAYS_FLUSH
				     ((opcode == `FV_RV_OPCODE_SYSTEM) &&
				      (
				        (funct3 == `FV_RV32I_FUNCT3_CSRRW)                                              ||
				       ((funct3 == `FV_RV32I_FUNCT3_CSRRS)  && (rs1 != `FV_RV32_REG_ADDR_WIDTH'b0)) ||
				       ((funct3 == `FV_RV32I_FUNCT3_CSRRC)  && (rs1 != `FV_RV32_REG_ADDR_WIDTH'b0)) ||
				        (funct3 == `FV_RV32I_FUNCT3_CSRRWI)                                             ||
				       ((funct3 == `FV_RV32I_FUNCT3_CSRRSI) && (rs1 != `FV_RV32_REG_ADDR_WIDTH'b0)) ||
				       ((funct3 == `FV_RV32I_FUNCT3_CSRRCI) && (rs1 != `FV_RV32_REG_ADDR_WIDTH'b0))
				      )
				     ) ||
`endif
`ifdef FV_DUT_FENCE_ALWAYS_FLUSH
				     ((opcode == `FV_RV_OPCODE_MISC_MEM) && (funct3 == `FV_RV32I_FUNCT3_FENCE)) ||
`endif
`ifdef FV_DUT_FENCEI_ALWAYS_FLUSH
				     ((opcode == `FV_RV_OPCODE_MISC_MEM) && (funct3 == `FV_RV32I_FUNCT3_FENCE_I)) ||
`endif
				     1'b0);   

endfunction // FV_FUNC_instr_causes_flush

function logic FV_FUNC_instr_expects_kill (logic [`FV_INSTR_WIDTH-1:0] instr, logic predict_br_taken);

   logic [`FV_OPCODE_WIDTH-1:0] opcode;

   opcode = FV_FUNC_get_opcode(instr);
   FV_FUNC_instr_expects_kill = (
`ifndef FV_DUT_DIRECT_JMPS_NO_KILL
				    FV_FUNC_instr_is_jal(instr) ||
`endif
				    FV_FUNC_instr_is_jalr(instr) ||
`ifdef FV_DUP_BR
				    (FV_FUNC_instr_is_branch(instr) && predict_br_taken) ||
`endif
				    (instr  == `FV_RV_INSTR_ECALL) ||
				    (instr  == `FV_RV_INSTR_EBREAK) ||
				    FV_FUNC_instr_causes_flush(instr) ||
				    1'b0);   

endfunction // FV_FUNC_instr_expects_kill

function logic FV_FUNC_instr_is_dup_sync (logic [`FV_INSTR_WIDTH-1:0] instr);

   logic [`FV_OPCODE_WIDTH-1:0] opcode;

   opcode = FV_FUNC_get_opcode(instr);
   FV_FUNC_instr_is_dup_sync = (
				     (instr == `FV_RV_INSTR_NOP_SYNC) ||
				     // Note: ECALL/EBREAK, too?
				     //(instr == `FV_RV_INSTR_ECALL) ||
				     //(instr == `FV_RV_INSTR_EBREAK) ||
`ifndef FV_DUP_BR
				     FV_FUNC_instr_is_jal(instr) ||
				     FV_FUNC_instr_is_jalr(instr) ||
				     FV_FUNC_instr_is_branch(instr) ||
`endif
				    1'b0);   

endfunction // FV_FUNC_instr_is_dup_sync


function instr_size_t FV_FUNC_instr_size(logic [`FV_INSTR_WIDTH-1:0] instr);

   // size is in bytes
   casex (instr[6:0])
     7'b?????00,
     7'b?????01,
     7'b?????10: FV_FUNC_instr_size = 2; // 16 bits

     7'b????011,
     7'b???0?11,
     7'b??0??11: FV_FUNC_instr_size = 4; // 32 bits
     
     7'b?011111: FV_FUNC_instr_size = 6; // 48 bits

     7'b0111111: FV_FUNC_instr_size = 8; // 64 bits

     default:    FV_FUNC_instr_size = 0; // ? bits Note
   endcase // case (instr[6:0])
   
endfunction // FV_FUNC_instr_size

// NOTE: the following module is used in FV_CORE_EX_cf where all instr are 32-bit RISC-V so no need to special case RVC
module FV_instr_correct_next_pc(
				    input ex_queue_entry_t                      instr_entry,
`ifndef FV_ENABLE_SI
				    output logic [`FV_INSTR_ADDR_WIDTH-1:0] correct_next_pc2,
				    output logic 				instr_is_exempt,
`endif
				    output logic [`FV_INSTR_ADDR_WIDTH-1:0] correct_next_pc1
				    );

   logic [`FV_INSTR_WIDTH-1:0] 	instr;
   logic [`FV_INSTR_ADDR_WIDTH-1:0] pc;

   assign instr = instr_entry.instr;
   assign pc    = instr_entry.pc;

`ifdef FV_ENABLE_SI
   logic [`FV_REG_WIDTH-1:0] 	rs1, rs2;

   assign rs1   = instr_entry.rs1_value;
   assign rs2   = instr_entry.rs2_value;
`endif
   
   logic [`FV_RV32_OPCODE_WIDTH-1:0] opcode;
   assign opcode = instr[`FV_RV32_INSTR_FIELD_OPCODE];

   logic [`FV_RV32_FUNCT12_WIDTH-1:0] funct12;
   assign funct12 = instr[`FV_RV32_INSTR_FIELD_FUNCT12];
   
`ifdef FV_ENABLE_SI
   logic [`FV_RV32_FUNCT3_WIDTH-1:0] funct3;
   assign funct3 = instr[`FV_RV32_INSTR_FIELD_FUNCT3];

   logic 				 branch_taken;
   
   always_comb begin
      case (funct3)
	`FV_RV32I_FUNCT3_BEQ:  branch_taken = (        rs1  ==         rs2 );
	`FV_RV32I_FUNCT3_BNE:  branch_taken = (        rs1  !=         rs2 );
	`FV_RV32I_FUNCT3_BLT:  branch_taken = ($signed(rs1) <  $signed(rs2));
	`FV_RV32I_FUNCT3_BGE:  branch_taken = ($signed(rs1) >= $signed(rs2));
	`FV_RV32I_FUNCT3_BLTU: branch_taken = (        rs1  <          rs2 );
	`FV_RV32I_FUNCT3_BGEU: branch_taken = (        rs1  >=         rs2 );
	default: branch_taken = 0;
      endcase
   end   
`endif
   
   logic instr_is_jump, instr_is_branch;

   assign instr_is_jump   = ((opcode == `FV_RV_OPCODE_JAL) ||
			     (opcode == `FV_RV_OPCODE_JALR));
   assign instr_is_branch =  (opcode == `FV_RV_OPCODE_BRANCH);

   logic [`FV_INSTR_ADDR_WIDTH-1:0] direct_jump_offset, indirect_jump_offset, branch_offset,
					direct_jump_target, indirect_jump_target, branch_target, jump_target;

   // JAL
   assign direct_jump_offset   = {{(`FV_INSTR_ADDR_WIDTH-20){instr[31]}},  // 12 or 44 bits, sign extend with imm[20]
				      instr[19:12], // 8 bits
				      instr[20],    // 1 bit
				      instr[30:21], // 10 bits
				  1'b0};
   assign direct_jump_target   = pc + direct_jump_offset;
   
   assign indirect_jump_offset = ({{(`FV_INSTR_ADDR_WIDTH-11){instr[31]}},  // 21 or 53 bits, sign extern with imm[11]
  				       instr[30:20]} // 11 bits
   // single JALR is only checked in si-FV
`ifdef FV_ENABLE_SI
 				  + rs1);
`else
                                  + `FV_INSTR_ADDR_WIDTH'b0); // unused/don't-care
`endif
   assign indirect_jump_target = {indirect_jump_offset[`FV_INSTR_ADDR_WIDTH-1:1], 1'b0};

   assign jump_target = (opcode == `FV_RV_OPCODE_JAL) ? 
			  direct_jump_target : 
			indirect_jump_target;

   assign branch_offset        = {{(`FV_INSTR_ADDR_WIDTH-12){instr[31]}},   // 20 or 52 bits, sign extend with imm[12]
				      instr[7],     // 1 bit,  imm[11]
				      instr[30:25], // 6 bits, imm[10:5]
				      instr[11:8],  // 4 bits, imm[4:1]
				  1'b0};		
   assign branch_target = pc + branch_offset;

   logic [`FV_INSTR_ADDR_WIDTH-1:0] pc_incremented;
   assign pc_incremented = pc + instr_entry.instr_size;

   always_comb begin
      if (instr_is_jump == 1) 
	correct_next_pc1 = jump_target;
      else if (instr_is_branch == 1) begin
`ifdef FV_ENABLE_SI
	 if (branch_taken == 1) begin
	    correct_next_pc1 = branch_target;
	 end else begin
	    correct_next_pc1 = pc_incremented;
	 end
`else
	 correct_next_pc1 = branch_target;
`endif	 

      // == special RISC-V system instructions
      end else if ((opcode == `FV_RV_OPCODE_SYSTEM) && (funct12 == `FV_RV32I_FUNCT12_ECALL))
	correct_next_pc1 = `FV_RV_DST_ADDR_ECALL; 
      else if ((opcode == `FV_RV_OPCODE_SYSTEM) && (funct12 == `FV_RV32I_FUNCT12_EBREAK))
	correct_next_pc1 = `FV_RV_DST_ADDR_EBREAK; 
      // == 

      else
	correct_next_pc1 = pc_incremented;
`ifndef FV_ENABLE_SI
      // correct pc2 is the same as correct pc1 except for when not si-FV and we have a branch
      correct_next_pc2 = correct_next_pc1;
      if (instr_is_branch == 1) begin
	 correct_next_pc2 = pc_incremented;
      end
`endif  
   end // always_comb

// next PC of the following instuctions are not (temporarily) or cannot be checked.
`ifndef FV_ENABLE_SI
   assign instr_is_exempt = (opcode == `FV_RV_OPCODE_JALR); // JALR exempt as value of rs1 could be bypassed from pipeline unless in SI mode
`endif

endmodule // FV_instr_correct_next_pc
