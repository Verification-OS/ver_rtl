
`define FV_RISCY_CORE_PATH riscv_wrapper.riscv_core_i

assign clk    = `FV_RISCY_CORE_PATH.clk_i;
assign reset_ = `FV_RISCY_CORE_PATH.rst_ni;

//=======================
// RF connections

logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] regs;
assign regs = `FV_RISCY_CORE_PATH.id_stage_i.registers_i.rf_reg;

//=======================
// DMEM connections

logic [7:0] mem[`DMEM_SIZE];
assign mem  = riscv_wrapper.ram_i.dp_ram_i.mem;
FV_BINDS_mem_map_byte #(.MEM_SIZE(`DMEM_SIZE)) mem_map(.mem_in(mem), .mem_out(dmem[0]));
// default enables
assign dmem_region_enables = `FV_DUT_MEM_REGION_ENABLES;

//=======================
// LD/ST connections

// effaddr is in ld/st unit (or core level) and imm is added in alu unit
assign ld_st_valid   = `FV_RISCY_CORE_PATH.data_req_o;
assign ld_st_effaddr = `FV_RISCY_CORE_PATH.data_addr_o;
assign ld_st_imm     = `FV_RISCY_CORE_PATH.id_stage_i.imm_b;

//=======================
// IF connections

logic 			   instr_req_o, instr_req_pending;
logic                      got_reset_kill;
logic                      IF_instruction1_send;
logic [`FV_INSTR_ADDR_WIDTH-1:0] IF_pc_int, IF_pc_flopped;
logic [`FV_INSTR_ADDR_WIDTH-1:0] IF_mem_fetch_addr_int, IF_mem_fetch_addr_flopped;

assign IF_instruction1_send = (IF_instruction_out_valid[1] && instr_req_pending);
			     
`ifdef FV_INCLUDE_IF_STAGE
assign instr_req_o = riscv_wrapper.instr_req;
assign IF_mem_fetch_addr_int = {riscv_wrapper.instr_addr[31:2], 2'b00};

assign riscv_wrapper.instr_rvalid = IF_instruction1_send; // only set valid if previous cycle instr was requested
assign riscv_wrapper.instr_rdata  = IF_instruction_bus_out;
assign riscv_wrapper.instr_gnt    = 1'b1; // OR instr_req_o?
`else
assign instr_req_o = `FV_RISCY_CORE_PATH.if_stage_i.instr_req_o;
assign IF_mem_fetch_addr_int = {`FV_RISCY_CORE_PATH.if_stage_i.instr_addr_o[31:2], 2'b00};

assign `FV_RISCY_CORE_PATH.if_stage_i.instr_rvalid_int = IF_instruction1_send; // only set valid if previous cycle instr was requested
assign `FV_RISCY_CORE_PATH.if_stage_i.instr_rdata_int  = IF_instruction_bus_out;
`endif // !`ifdef FV_INCLUDE_IF_STAGE

assign IF_pc_int = `FV_RISCY_CORE_PATH.if_stage_i.instr_addr_o;

// limit PC to 2-byte-aligned addresses if RVC enabled, otherwise limit to 4-byte-aligned
`ifdef FV_INCLUDE_RVC
FV_instr_add_alignement: assume property (@(posedge clk) (IF_pc[0]   == 1'b0));
`else
FV_instr_add_alignement: assume property (@(posedge clk) (IF_pc[1:0] == 2'b00));
`endif

always @(posedge clk) begin
   if (!reset_) begin
      instr_req_pending <= 0;
      got_reset_kill <= 0;
   end else begin
      instr_req_pending <= instr_req_o || ((instr_req_pending && !IF_instruction_out_valid[1]) && (!IF_kill)); // wait till bubbles go through
      if (`FV_RISCY_CORE_PATH.if_stage_i.branch_req)
	got_reset_kill <= 1;	
   end
   if (instr_req_o) begin
     IF_pc_flopped             <= IF_pc_int;
     IF_mem_fetch_addr_flopped <= IF_mem_fetch_addr_int;
   end
end
   
   assign IF_pc             = instr_req_o ? IF_pc_int             : IF_pc_flopped;
   assign IF_mem_fetch_addr = instr_req_o ? IF_mem_fetch_addr_int : IF_mem_fetch_addr_flopped;

   assign IF_stall = (!instr_req_o) && ((!(instr_req_pending && !IF_instruction_out_valid[1])) || IF_kill);

//=======================
// kill/jump/branch
   
   assign IF_kill = `FV_RISCY_CORE_PATH.id_stage_i.pc_set_o && got_reset_kill;

   // NOTE: dut_jump_taken should be aligned with commit signals
   always @(posedge clk) begin
      dut_jump_taken <= `FV_RISCY_CORE_PATH.id_stage_i.pc_set_o && `FV_RISCY_CORE_PATH.id_stage_i.jump_set;
   end

   // NOTE: dut_branch_taken should
   //  - be aligned with EX_kill
   //  - come before or in the same cycle as the commit signal of the corresponding branch instruction
   assign dut_branch_taken = `FV_RISCY_CORE_PATH.id_stage_i.pc_set_o && `FV_RISCY_CORE_PATH.id_stage_i.branch_set_q;
   
//=======================
// EX connections
   
for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
   assign IF2EX_instruction_in_valid[i] = IF_instruction_out_valid[i] && IF_instruction1_send;
end
   assign IF2EX_pc                    = IF_instruction_pc;
   assign IF2EX_stall                 = 1'b0;
   assign IF2EX_kill                  = IF_kill;

   assign EX_stall                 = 1'b0;
   assign EX_kill                  = IF_kill;

//=======================
// misc. connections

   assign commit[1]                =   `FV_RISCY_CORE_PATH.if_stage_i.instr_valid_id_o && 
	   			      (`FV_RISCY_CORE_PATH.if_stage_i.if_valid_o || 
				       `FV_RISCY_CORE_PATH.if_stage_i.clear_instr_valid_i);
   assign rf_write_en[1]           =   `FV_RISCY_CORE_PATH.id_stage_i.registers_i.we_a_i;
   assign rf_write_rd[1]           =   `FV_RISCY_CORE_PATH.id_stage_i.registers_i.waddr_a_i;

`ifdef FV_JAL_RD_OR
   assign `FV_RISCY_CORE_PATH.id_stage_i.registers_i.override_rf_wdata = fv_override_rf_wdata;
`endif

//=======================
// Note: add checks
//   1- illegal instruction check doesn't trigger
