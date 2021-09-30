
module FV_CORE_si(
		 input logic 							clk,
		 input logic 							reset_,
   
		 input logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] arf,
`ifdef FV_RF2_ENABLE
	         input logic [(`FV_NUM_RF2_REGS)-1:0][`FV_REG2_WIDTH-1:0] arf2,
`endif
		 input logic [`FV_DUT_NUM_MEM_REGIONS-1:0][(`DMEM_SIZE/4)-1:0][31:0] dmem,
										
		 input logic [`FV_INSTR_ADDR_WIDTH-1:0] 			pc,
										
		 input logic [`FV_INSTR_WIDTH-1:0] 				instruction,
		 input logic 							instruction_valid,
		 input logic [9:0] 						clock_counter,

		 output si_prop_signals_t                                       si_ps
	      );

   logic si_launch, 
         si_launch_d; // 1 cycle delayed version to capture dmem content 
   
   assign si_launch = (clock_counter == (`FV_SI_SRC_CAPTURE_CYCLE));
   
   // a pulse to trigger the antecedent of the SI properties
   logic si_en;
   assign si_en = (clock_counter == (`FV_SI_SRC_CAPTURE_CYCLE - `FV_SI_FE_PIPE_DELAY));
   
   reg [`FV_INSTR_WIDTH-1:0] 	  si_instr;
   reg [`FV_INSTR_ADDR_WIDTH-1:0] 	  si_pc;
   reg [`FV_REG_WIDTH-1:0] 	  si_rs1_value;
   reg [`FV_REG_WIDTH-1:0] 	  si_rs2_value;

   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rs1    = instruction[`FV_RV32_INSTR_FIELD_RS1];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rs2    = instruction[`FV_RV32_INSTR_FIELD_RS2];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] rd     = instruction[`FV_RV32_INSTR_FIELD_RD];

   // extract instruction fields
   wire [`FV_RV32_OPCODE_WIDTH-1:0]   si_opcode = si_instr[`FV_RV32_INSTR_FIELD_OPCODE];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] si_rd     = si_instr[`FV_RV32_INSTR_FIELD_RD];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] si_rs1    = si_instr[`FV_RV32_INSTR_FIELD_RS1];
   wire [`FV_RV32_REG_ADDR_WIDTH-1:0] si_rs2    = si_instr[`FV_RV32_INSTR_FIELD_RS2];
   wire [`FV_RV32_IMM5_WIDTH-1:0]     si_imm5   = si_instr[`FV_RV32_INSTR_FIELD_IMM5];
   wire [`FV_RV32_IMM7_WIDTH-1:0]     si_imm7   = si_instr[`FV_RV32_INSTR_FIELD_IMM7];
   wire [`FV_RV32_IMM12_WIDTH-1:0]    si_imm12  = si_instr[`FV_RV32_INSTR_FIELD_IMM12];
`ifdef FV_INCLUDE_RV64
   wire [`FV_RV64_SHAMT_WIDTH-1:0]    si_shamt  = si_instr[`FV_RV64_INSTR_FIELD_SHAMT];
`else
   wire [`FV_RV32_SHAMT_WIDTH-1:0]    si_shamt  = si_instr[`FV_RV32_INSTR_FIELD_SHAMT];
`endif
   wire [`FV_RV32_FUNCT3_WIDTH-1:0]   si_funct3 = si_instr[`FV_RV32_INSTR_FIELD_FUNCT3];
   wire [`FV_RV32_FUNCT7_WIDTH-1:0]   si_funct7 = si_instr[`FV_RV32_INSTR_FIELD_FUNCT7];

   wire [`FV_REG_WIDTH-1:0] 	  rf_probe_rs1_value = arf[rs1];
   wire [`FV_REG_WIDTH-1:0] 	  rf_probe_rs2_value = arf[rs2];
   wire [`FV_REG_WIDTH-1:0] 	  si_rf_probe_rd_value = arf[si_rd];

   always @(posedge clk) begin
      if(!reset_) begin
	 si_instr  <= `FV_INSTR_NOP;
      end
      else if (si_launch) begin
	 si_instr  <= instruction;
      end
      if(!reset_) begin
	 si_launch_d <= 0;
      end
      else begin
	 si_launch_d <= si_launch;
      end
   end

   always @(posedge clk) begin
      if (si_launch) begin
	 si_pc     <= pc;

	 si_rs1_value    <= (rs1 == 0) ? {(`FV_REG_WIDTH){1'b0}} : rf_probe_rs1_value; // pure regfile reads don't return 0 for r0
	 si_rs2_value    <= (rs2 == 0) ? {(`FV_REG_WIDTH){1'b0}} : rf_probe_rs2_value;
      end
   end

   // helpers
   wire [`FV_REG_WIDTH-1:0]    si_imm12_signed_ext;
   wire [`FV_REG_WIDTH-1:0]    si_imm12_unsigned_ext;
   assign si_imm12_signed_ext   = {{(`FV_REG_WIDTH-`FV_RV32_IMM12_WIDTH){si_imm12[`FV_RV32_IMM12_WIDTH-1]}}, si_imm12};
   assign si_imm12_unsigned_ext = {{(`FV_REG_WIDTH-`FV_RV32_IMM12_WIDTH){1'b0}}                                , si_imm12};

   wire   signed [(`FV_REG_WIDTH*2)-1:0] rs2_value_unsigned =       {{(`FV_REG_WIDTH){1'b0}}, si_rs2_value};
   wire   signed [(`FV_REG_WIDTH*2)-1:0] si_mul_result      =   $signed(si_rs1_value) *   $signed(si_rs2_value);
   wire   signed [(`FV_REG_WIDTH*2)-1:0] si_mulsu_result    =   $signed(si_rs1_value) *              rs2_value_unsigned;
   wire unsigned [(`FV_REG_WIDTH*2)-1:0] si_mulu_result     = $unsigned(si_rs1_value) * $unsigned(si_rs2_value);

   wire   signed [`FV_REG_WIDTH-1:0] si_div_result  =   $signed(si_rs1_value) /   $signed(si_rs2_value);
   wire unsigned [`FV_REG_WIDTH-1:0] si_divu_result = $unsigned(si_rs1_value) / $unsigned(si_rs2_value);
   wire   signed [`FV_REG_WIDTH-1:0] si_rem_result  =   $signed(si_rs1_value) %   $signed(si_rs2_value);
   wire unsigned [`FV_REG_WIDTH-1:0] si_remu_result = $unsigned(si_rs1_value) % $unsigned(si_rs2_value);

`define FV_SI_EFF_ADDRESS_WIDTH $clog2(`DMEM_SIZE)
   
   wire        [`FV_RV32_IMM12_WIDTH-1:0] ldst_offset      = (si_opcode == `FV_RV_OPCODE_LOAD) ? si_imm12 : ((si_opcode == `FV_RV_OPCODE_STORE) ? {si_imm7, si_imm5} : 12'b0);
   wire   signed [`FV_MEM_ADDR_WIDTH-1:0] addr_offset      = {{(`FV_MEM_ADDR_WIDTH-`FV_RV32_IMM12_WIDTH){ldst_offset[`FV_RV32_IMM12_WIDTH-1]}}, ldst_offset};
   wire   signed [`FV_MEM_ADDR_WIDTH-1:0] effective_addr   =   $signed(si_rs1_value) + addr_offset;
   wire unsigned [`FV_MEM_ADDR_WIDTH-1:0] ldst_addr_full   = $unsigned(effective_addr);
   wire unsigned [`FV_MEM_ADDR_WIDTH-1:0] ldst_addr        = {{(`FV_MEM_ADDR_WIDTH-`FV_SI_EFF_ADDRESS_WIDTH){1'b0}}, ldst_addr_full[`FV_SI_EFF_ADDRESS_WIDTH-1:0]};
   wire unsigned [`FV_MEM_ADDR_WIDTH-3:0] ldst_addr_next   = ldst_addr[`FV_MEM_ADDR_WIDTH-1:2] + 1;
// Note: add support for multiple memory region
   wire                                [63:0] si_dmem_8byte_value = (ldst_addr_next>=`DMEM_SIZE/4) ?
					                          {32'b0,                                        dmem[`FV_SI_DMEM_REGION][ldst_addr[`FV_MEM_ADDR_WIDTH-1:2]]} :
					                          {dmem[`FV_SI_DMEM_REGION][ldst_addr_next], dmem[`FV_SI_DMEM_REGION][ldst_addr[`FV_MEM_ADDR_WIDTH-1:2]]};
   wire                                [63:0] dmem_8byte_ld_value = si_dmem_8byte_value >> (ldst_addr[1:0] * 8);

// Note: for now, just supporting d-word LD/ST that are address aligned based on size; add support for misaligned if a core supports that

   logic [`FV_REG_WIDTH-1:0] 	      si_dmem_ld_value;
`ifdef FV_INCLUDE_RV64
   logic [63:0] 			      si_dmem_ld_value_32b_sign_extended;
`endif
   logic [63:0] 			      dmem_8byte_value_saved; // for checking stores

   wire st_is_byte = (si_funct3 == `FV_RV32I_FUNCT3_SB);
   wire st_is_half = (si_funct3 == `FV_RV32I_FUNCT3_SH);
   wire st_is_word = (si_funct3 == `FV_RV32I_FUNCT3_SW);

   wire [63:0] store_mask  = (st_is_byte ?  64'h0ff                   : 
			     (st_is_half ?  64'h0ffff                 :  
			     (st_is_word ?  64'h0ffffffff             :  
			                    64'hffffffffffffffff)))  << (ldst_addr[1:0] * 8);
   wire [63:0] store_value = (st_is_byte ? {56'h0, si_rs2_value[7:0]}  : 
		             (st_is_half ? {48'h0, si_rs2_value[15:0]} : 
			     (st_is_word ? {32'h0, si_rs2_value[31:0]} : 
			                           si_rs2_value)))  << (ldst_addr[1:0] * 8);
   wire [63:0] si_expected_dmem_8byte_value = (dmem_8byte_value_saved & ~store_mask) | store_value;
// the following is incorrect and just for testing store instructions check; Note: turn into FV_BUG?
// wire [63:0] si_expected_dmem_8byte_value = (dmem_8byte_value_saved              ) | store_value;
   
   always @(posedge clk) begin
      if (si_launch_d) begin
	 dmem_8byte_value_saved <= si_dmem_8byte_value;
	 si_dmem_ld_value       <= dmem_8byte_ld_value[`FV_REG_WIDTH-1:0];
      end
   end

`ifdef FV_INCLUDE_RV64
   assign si_dmem_ld_value_32b_sign_extended = {{32{si_dmem_ld_value[31]}}, si_dmem_ld_value[31:0]};
`endif
			      
   always @(posedge clk) begin
      // NOPs in all except for one
`ifdef FV_ENABLE_SC_DEBUG
      FV_si_NOPs: 
`else
      FV_si_con1:
`endif
	assume property((si_launch == 0) |-> (instruction[31:0] == `FV_INSTR_NOP));
   end

   assign si_ps.si_instr            = si_instr;
   assign si_ps.si_pc               = si_pc;
   assign si_ps.si_rs1_value        = si_rs1_value;
   assign si_ps.si_rs2_value        = si_rs2_value;
   assign si_ps.si_imm12_signed_ext = si_imm12_signed_ext;
   assign si_ps.si_shamt            = si_shamt;

   assign si_ps.si_mul_result       = si_mul_result;
   assign si_ps.si_mulsu_result     = si_mulsu_result;
   assign si_ps.si_mulu_result      = si_mulu_result;

   assign si_ps.si_div_result       = si_div_result;
   assign si_ps.si_divu_result      = si_divu_result;
   assign si_ps.si_rem_result       = si_rem_result;
   assign si_ps.si_remu_result      = si_remu_result;

   assign si_ps.si_rf_probe_rd_value          = si_rf_probe_rd_value;
   assign si_ps.si_dmem_ld_value              = si_dmem_ld_value;
`ifdef FV_INCLUDE_RV64
   assign si_ps.si_dmem_ld_value_32b_sign_extended = si_dmem_ld_value_32b_sign_extended;
`endif   
   assign si_ps.si_dmem_8byte_value           = si_dmem_8byte_value;
   assign si_ps.si_expected_dmem_8byte_value  = si_expected_dmem_8byte_value;

   assign si_ps.si_check_ADDI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_ADDI   == 1'b1));
   assign si_ps.si_check_SLTI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLTI   == 1'b1));
   assign si_ps.si_check_SLTIU  = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLTIU  == 1'b1));
   assign si_ps.si_check_XORI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_XORI   == 1'b1));
   assign si_ps.si_check_ORI    = (si_en && (`FV_SI_SIGNALS_PATH.instr_ORI    == 1'b1));
   assign si_ps.si_check_ANDI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_ANDI   == 1'b1));
   assign si_ps.si_check_SLLI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLLI   == 1'b1));
   assign si_ps.si_check_SRLI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRLI   == 1'b1));
   assign si_ps.si_check_SRAI   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRAI   == 1'b1));
   assign si_ps.si_check_ADD    = (si_en && (`FV_SI_SIGNALS_PATH.instr_ADD    == 1'b1));
   assign si_ps.si_check_SUB    = (si_en && (`FV_SI_SIGNALS_PATH.instr_SUB    == 1'b1));
   assign si_ps.si_check_SLL    = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLL    == 1'b1));
   assign si_ps.si_check_SLT    = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLT    == 1'b1));
   assign si_ps.si_check_SLTU   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLTU   == 1'b1));
   assign si_ps.si_check_XOR    = (si_en && (`FV_SI_SIGNALS_PATH.instr_XOR    == 1'b1));
   assign si_ps.si_check_SRL    = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRL    == 1'b1));
   assign si_ps.si_check_SRA    = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRA    == 1'b1));
   assign si_ps.si_check_OR     = (si_en && (`FV_SI_SIGNALS_PATH.instr_OR     == 1'b1));
   assign si_ps.si_check_AND    = (si_en && (`FV_SI_SIGNALS_PATH.instr_AND    == 1'b1));
   assign si_ps.si_check_MUL    = (si_en && (`FV_SI_SIGNALS_PATH.instr_MUL    == 1'b1));
   assign si_ps.si_check_MULH   = (si_en && (`FV_SI_SIGNALS_PATH.instr_MULH   == 1'b1));
   assign si_ps.si_check_MULHSU = (si_en && (`FV_SI_SIGNALS_PATH.instr_MULHSU == 1'b1));
   assign si_ps.si_check_MULHU  = (si_en && (`FV_SI_SIGNALS_PATH.instr_MULHU  == 1'b1));
   assign si_ps.si_check_DIV    = (si_en && (`FV_SI_SIGNALS_PATH.instr_DIV    == 1'b1));
   assign si_ps.si_check_DIVU   = (si_en && (`FV_SI_SIGNALS_PATH.instr_DIVU   == 1'b1));
   assign si_ps.si_check_REM    = (si_en && (`FV_SI_SIGNALS_PATH.instr_REM    == 1'b1));
   assign si_ps.si_check_REMU   = (si_en && (`FV_SI_SIGNALS_PATH.instr_REMU   == 1'b1));
   assign si_ps.si_check_LUI    = (si_en && (`FV_SI_SIGNALS_PATH.instr_LUI    == 1'b1));
   assign si_ps.si_check_AUIPC  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AUIPC  == 1'b1));
   assign si_ps.si_check_LB     = (si_en && (`FV_SI_SIGNALS_PATH.instr_LB     == 1'b1));
   assign si_ps.si_check_LH     = (si_en && (`FV_SI_SIGNALS_PATH.instr_LH     == 1'b1));
   assign si_ps.si_check_LW     = (si_en && (`FV_SI_SIGNALS_PATH.instr_LW     == 1'b1));
   assign si_ps.si_check_LBU    = (si_en && (`FV_SI_SIGNALS_PATH.instr_LBU    == 1'b1));
   assign si_ps.si_check_LHU    = (si_en && (`FV_SI_SIGNALS_PATH.instr_LHU    == 1'b1));
   assign si_ps.si_check_SB     = (si_en && (`FV_SI_SIGNALS_PATH.instr_SB     == 1'b1));
   assign si_ps.si_check_SH     = (si_en && (`FV_SI_SIGNALS_PATH.instr_SH     == 1'b1));
   assign si_ps.si_check_SW     = (si_en && (`FV_SI_SIGNALS_PATH.instr_SW     == 1'b1));
   assign si_ps.si_check_JAL    = (si_en && (`FV_SI_SIGNALS_PATH.instr_JAL    == 1'b1));
   assign si_ps.si_check_JALR   = (si_en && (`FV_SI_SIGNALS_PATH.instr_JALR   == 1'b1));

`ifdef FV_INCLUDE_RV64
   assign si_ps.si_check_LWU    = (si_en && (`FV_SI_SIGNALS_PATH.instr_LWU    == 1'b1));
   assign si_ps.si_check_LD     = (si_en && (`FV_SI_SIGNALS_PATH.instr_LD     == 1'b1));
   assign si_ps.si_check_SD     = (si_en && (`FV_SI_SIGNALS_PATH.instr_SD     == 1'b1));
   assign si_ps.si_check_ADDIW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_ADDIW  == 1'b1));
   assign si_ps.si_check_SLLIW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLLIW  == 1'b1));
   assign si_ps.si_check_SRLIW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRLIW  == 1'b1));
   assign si_ps.si_check_SRAIW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRAIW  == 1'b1));
   assign si_ps.si_check_ADDW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_ADDW   == 1'b1));
   assign si_ps.si_check_SUBW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SUBW   == 1'b1));
   assign si_ps.si_check_SLLW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SLLW   == 1'b1));
   assign si_ps.si_check_SRLW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRLW   == 1'b1));
   assign si_ps.si_check_SRAW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_SRAW   == 1'b1));

   assign si_ps.si_check_MULW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_MULW   == 1'b1));
   assign si_ps.si_check_DIVW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_DIVW   == 1'b1));
   assign si_ps.si_check_DIVUW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_DIVUW  == 1'b1));
   assign si_ps.si_check_REMW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_REMW   == 1'b1));
   assign si_ps.si_check_REMUW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_REMUW  == 1'b1));
`endif
   
`ifdef FV_INCLUDE_RVA
   assign si_ps.si_check_LRW      = (si_en && (`FV_SI_SIGNALS_PATH.instr_LRW      == 1'b1));
   assign si_ps.si_check_SCW      = (si_en && (`FV_SI_SIGNALS_PATH.instr_SCW      == 1'b1));
   assign si_ps.si_check_AMOSWAPW = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOSWAPW == 1'b1));
   assign si_ps.si_check_AMOADDW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOADDW  == 1'b1));
   assign si_ps.si_check_AMOXORW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOXORW  == 1'b1));
   assign si_ps.si_check_AMOANDW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOANDW  == 1'b1));
   assign si_ps.si_check_AMOORW   = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOORW   == 1'b1));
   assign si_ps.si_check_AMOMINW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMINW  == 1'b1));
   assign si_ps.si_check_AMOMAXW  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMAXW  == 1'b1));
   assign si_ps.si_check_AMOMINUW = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMINUW == 1'b1));
   assign si_ps.si_check_AMOMAXUW = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMAXUW == 1'b1));
 `ifdef FV_INCLUDE_RV64
   assign si_ps.si_check_LRD      = (si_en && (`FV_SI_SIGNALS_PATH.instr_LRD      == 1'b1));
   assign si_ps.si_check_SCD      = (si_en && (`FV_SI_SIGNALS_PATH.instr_SCD      == 1'b1));
   assign si_ps.si_check_AMOSWAPD = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOSWAPD == 1'b1));
   assign si_ps.si_check_AMOADDD  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOADDD  == 1'b1));
   assign si_ps.si_check_AMOXORD  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOXORD  == 1'b1));
   assign si_ps.si_check_AMOANDD  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOANDD  == 1'b1));
   assign si_ps.si_check_AMOORD   = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOORD   == 1'b1));
   assign si_ps.si_check_AMOMIND  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMIND  == 1'b1));
   assign si_ps.si_check_AMOMAXD  = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMAXD  == 1'b1));
   assign si_ps.si_check_AMOMINUD = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMINUD == 1'b1));
   assign si_ps.si_check_AMOMAXUD = (si_en && (`FV_SI_SIGNALS_PATH.instr_AMOMAXUD == 1'b1));
 `endif
`endif
   
endmodule // FV_CORE_si

