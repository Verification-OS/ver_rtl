
`define FV_ARIANE_CORE_PATH    ariane_wrapper.ariane_core_i
`define FV_ARIANE_MEM_PATH     ariane_wrapper.ariane_axi_mem_i
`define FV_ARIANE_CACHE_PATH   ariane_wrapper.ariane_core_i.i_cache_subsystem
`define FV_ARIANE_LSU_PATH     `FV_ARIANE_CORE_PATH.ex_stage_i.lsu_i
`define FV_ARIANE_RF_PATH      `FV_ARIANE_CORE_PATH.issue_stage_i.i_issue_read_operands.i_ariane_regfile
`define FV_ARIANE_FRF_PATH     `FV_ARIANE_CORE_PATH.issue_stage_i.i_issue_read_operands.float_regfile_gen.i_ariane_fp_regfile
  
assign clk    = `FV_ARIANE_CORE_PATH.clk_i;
assign reset_ = `FV_ARIANE_CORE_PATH.rst_ni;

//=======================
// RF connections

logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] regs;
assign regs = `FV_ARIANE_RF_PATH.mem;
   
logic [(`FV_NUM_RF2_REGS)-1:0][`FV_REG2_WIDTH-1:0] regs2;
assign regs2 = `FV_ARIANE_FRF_PATH.mem; // FP regs

//=======================
// DMEM connections

`define DMEM_DEPTH (`DMEM_SIZE/(`FV_DUT_MEM_DATA_WIDTH/8))
 
// default enables
assign dmem_region_enables = `FV_DUT_MEM_REGION_ENABLES;
logic [`FV_DUT_NUM_MEM_REGIONS-1:0][`FV_MEM_ADDR_WIDTH-1:0] mem_base, mem_limit;
logic [`FV_DUT_NUM_MEM_REGIONS-1:0] mem_sel, mem_region_strong_order;
logic [`FV_MEM_ADDR_WIDTH-1:0] ld_st_effaddr_int;

// read in the DUT-specific memory regions
`include "fv_axi3_mem_regions.svh"

// set the following according to DUT/SoC specifications and set up (memory region and MMU init)      
assign mem_region_strong_order = {`FV_DUT_NUM_MEM_REGIONS{1'b0}};

genvar j;
for (j=0; j<`FV_DUT_NUM_MEM_REGIONS; j++) begin
   if ((`FV_DUT_MEM_REGION_ENABLES & ({{(`FV_DUT_NUM_MEM_REGIONS-1){1'b0}}, 1'b1} << j)) != 0 ) begin
      FV_BINDS_mem_map_byte_3d 
	#(.MEM_SIZE(`DMEM_SIZE), .MEM_DATA_WIDTH(`FV_DUT_MEM_DATA_WIDTH)) 
      mem_map(
	      .mem_in(`FV_ARIANE_MEM_PATH.axi_mem_i.genblk1[j].genblk1.dp_ram_i.mem), 
	      .mem_out(dmem[j])
	      );
   end
   
   assign mem_sel[j] = ((mem_base[j] <= ld_st_effaddr_int) && (ld_st_effaddr_int < (mem_base[j] + `DMEM_SIZE)) && dmem_region_enables[j]);
  
   FV_cover_dmem: cover property (@(posedge clk) (ld_st_valid && (ld_st_effaddr_int == mem_base[j])));

   FV_ldst_addr_aligned: assume property (@(posedge clk) (ld_st_valid && mem_sel[j] && (mem_region_strong_order[j] == 1'b1)) |-> (ld_st_effaddr_int[2:0] == 3'b0));
   
end

FV_ldst_addr_range_limits: assume property (@(posedge clk) (ld_st_valid) |-> (|mem_sel));

FV_no_misaligned_ld_st: assume property (@(posedge clk) 
					   (`FV_ARIANE_LSU_PATH.lsu_ctrl.valid == 1) |->
                                           (`FV_ARIANE_LSU_PATH.data_misaligned != 1));

//=======================
// LD/ST connections

assign ld_st_valid       = `FV_ARIANE_LSU_PATH.lsu_valid_i;
assign ld_st_effaddr_int = `FV_ARIANE_LSU_PATH.vaddr_i;
assign ld_st_effaddr     = {48'b0, ld_st_effaddr_int[15:0]};
assign ld_st_imm         = `FV_ARIANE_LSU_PATH.fu_data_i.imm;


//=======================
// IF connections

logic 			   instr_req_o, instr_req_pending;
logic                      IF_instruction1_send;
logic [`FV_INSTR_ADDR_WIDTH-1:0] IF_pc_int, IF_pc_flopped;
   
assign IF_instruction1_send = ((|IF_instruction_out_valid) && instr_req_pending);

`ifdef FV_INCLUDE_IF_STAGE
assign instr_req_o       = `FV_ARIANE_MEM_PATH.instr_req_i;
assign IF_mem_fetch_addr = `FV_ARIANE_MEM_PATH.axs_araddr;

assign `FV_ARIANE_MEM_PATH.instr_rvalid = IF_instruction1_send; // only set valid if previous cycle instr was requested
assign `FV_ARIANE_MEM_PATH.instr_rdata = IF_instruction_bus_out;

// Note: instr_gnt is unused for now
assign `FV_ARIANE_MEM_PATH.instr_gnt    = instr_req_o;

`else // !`ifdef FV_INCLUDE_IF_STAGE

logic 			   fv2if_ready;

assign fv2if_ready      = (instr_req_o && !IF_instruction1_send) ? 0 : 1;

assign instr_req_o       = `FV_ARIANE_CACHE_PATH.icache_dreq_i.req;
assign IF_mem_fetch_addr = `FV_ARIANE_CACHE_PATH.icache_dreq_i.vaddr;

assign `FV_ARIANE_CACHE_PATH.fv2if_instruction_valid = IF_instruction1_send;
assign `FV_ARIANE_CACHE_PATH.fv2if_instruction       = IF_instruction_bus_out;
assign `FV_ARIANE_CACHE_PATH.fv2if_ready             = fv2if_ready;
   
`endif // !`ifdef FV_INCLUDE_IF_STAGE

// IF_pc_int is the same w. or w.o. FV_INCLUDE_IF_STAGE
assign IF_pc_int         = IF_mem_fetch_addr;

// limit PC to 2-byte-aligned addresses if RVC enabled, otherwise limit to 4-byte-aligned
`ifdef FV_INCLUDE_RVC
FV_instr_addr_alignement:  assume property (@(posedge clk) (IF_pc[0]   == 1'b0));
FV_instr_addr_alignement1: assume property (@(posedge clk) (`FV_ARIANE_CORE_PATH.i_frontend.npc_d[0]   == 1'b0));
`else
FV_instr_addr_alignement:  assume property (@(posedge clk) (IF_pc[1:0] == 2'b00));
FV_instr_addr_alignement1: assume property (@(posedge clk) (`FV_ARIANE_CORE_PATH.i_frontend.npc_d[1:0] == 2'b00));
`endif

FV_instr_addr_limit:       assume property (@(posedge clk) (`FV_ARIANE_CACHE_PATH.icache_dreq_o.valid |-> 
							      ((`FV_ARIANE_CACHE_PATH.icache_dreq_o.vaddr >= `FV_DUT_INSTR_ADDRESS_BASE) && 
							       (`FV_ARIANE_CACHE_PATH.icache_dreq_o.vaddr <= `FV_DUT_INSTR_ADDRESS_LIMIT))
							      ));

always @(posedge clk) begin
   if (!reset_) begin
      instr_req_pending <= 0;
   end else begin
      instr_req_pending <= instr_req_o || ((instr_req_pending && !(|IF_instruction_out_valid)) && (!IF_kill)); // wait till bubbles go through
   end
   if (instr_req_o && ((!(instr_req_pending && !(|IF_instruction_out_valid))) || IF_kill))
     IF_pc_flopped <= IF_pc_int;
end
   
   assign IF_pc    = ( instr_req_o  && ((!(instr_req_pending && !(|IF_instruction_out_valid))) || IF_kill)) ? IF_pc_int : IF_pc_flopped;
   assign IF_stall = (!instr_req_o) && ((!(instr_req_pending && !(|IF_instruction_out_valid))) || IF_kill);
     
//=======================
// kill/jump/branch

   assign IF_kill = `FV_ARIANE_CORE_PATH.i_frontend.flush_i;

   logic dut_jump_taken_int, dut_jump_taken_jal, dut_jump_taken_jalr, dut_jump_taken_jal_flopped;
   
   // NOTE: dut_jump_taken should be aligned with commit signals

   // delay the JAL signal to line it up with commit and kill
   always @(posedge clk) begin
      if (!reset_)
	dut_jump_taken_jal_flopped <= 0;
      else
	dut_jump_taken_jal_flopped <= dut_jump_taken_jal;
   end

   assign dut_jump_taken_jal =     `FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.branch_valid_i &&                               // should be JAL if 
				(!(`FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.fu_data_i.operator == ariane_pkg::JALR)) &&     // not JALR, and
			        (!(ariane_pkg::op_is_branch(`FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.fu_data_i.operator))); // not branch
   assign dut_jump_taken_jalr =    `FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.branch_valid_i &&
				  (`FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.fu_data_i.operator == ariane_pkg::JALR);
      
   assign dut_jump_taken = dut_jump_taken_jal_flopped || dut_jump_taken_jalr;
   
   // NOTE: dut_branch_taken should
   //  - be aligned with EX_kill
   //  - come before or in the same cycle as the commit signal of the corresponding branch instruction
   assign dut_branch_taken = `FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.branch_valid_i && 
			     (ariane_pkg::op_is_branch(`FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.fu_data_i.operator)) &&
			     `FV_ARIANE_CORE_PATH.ex_stage_i.branch_unit_i.resolved_branch_o.is_taken;
   
//=======================
// EX connections

for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
   assign IF2EX_instruction_in_valid[i] = IF_instruction_out_valid[i] && IF_instruction1_send;
end
   assign IF2EX_pc                    = IF_pc_int;
   assign IF2EX_stall                 = 1'b0;
   assign IF2EX_kill                  = IF_kill;

   assign EX_stall                 = 1'b0;
   assign EX_kill                  = IF_kill;

//=======================
// misc. connections

   // delay commit which is from ID stage to match the delay of dut_branch_taken which is from EX stage   
   always @(posedge clk) begin
      commit[1] <= `FV_ARIANE_CORE_PATH.commit_stage_i.commit_ack_o[0];
      commit[2] <= `FV_ARIANE_CORE_PATH.commit_stage_i.commit_ack_o[1];

   end
   
   assign rf_write_en[1] = `FV_ARIANE_RF_PATH.we_i[0];
   assign rf_write_rd[1] = `FV_ARIANE_RF_PATH.waddr_i[0];
   assign rf_write_en[2] = `FV_ARIANE_RF_PATH.we_i[1];
   assign rf_write_rd[2] = `FV_ARIANE_RF_PATH.waddr_i[1];

   assign rf2_write_en[1] = `FV_ARIANE_FRF_PATH.we_i[0];
   assign rf2_write_rd[1] = `FV_ARIANE_FRF_PATH.waddr_i[0];
   assign rf2_write_en[2] = `FV_ARIANE_FRF_PATH.we_i[1];
   assign rf2_write_rd[2] = `FV_ARIANE_FRF_PATH.waddr_i[1];
   
`ifdef FV_JAL_RD_OR
   assign `FV_ARIANE_CORE_PATH.id_stage_i.registers_i.riscv_register_file_i.override_rf_wdata = fv_override_rf_wdata;
`endif

//=======================
// cover properties

   logic dcache_req_1,     dcache_req_1_delayed;
   logic dcache_req_2,     dcache_req_2_delayed;
   logic dcache_req_3,     dcache_req_3_delayed;
   logic [20:0] dcache_req_1_shiftreg;
   logic [20:0] dcache_req_2_shiftreg;
   logic [20:0] dcache_req_3_shiftreg;

   assign dcache_req_1 = (`FV_ARIANE_LSU_PATH.dcache_req_ports_o[0].data_req == 1);
   assign dcache_req_2 = (`FV_ARIANE_LSU_PATH.dcache_req_ports_o[1].data_req == 1);
   assign dcache_req_3 = (`FV_ARIANE_LSU_PATH.dcache_req_ports_o[2].data_req == 1);
   
   always @(posedge clk) begin
      if(!reset_) begin
	dcache_req_1_shiftreg     <= '0;
	dcache_req_2_shiftreg     <= '0;
	dcache_req_3_shiftreg     <= '0;
      end else begin
	dcache_req_1_shiftreg     <= (dcache_req_1_shiftreg     << 1) | {20'b0, dcache_req_1};
	dcache_req_2_shiftreg     <= (dcache_req_2_shiftreg     << 1) | {20'b0, dcache_req_2};
	dcache_req_3_shiftreg     <= (dcache_req_3_shiftreg     << 1) | {20'b0, dcache_req_3};
      end
   end
   assign dcache_req_1_delayed     = dcache_req_1_shiftreg[15];
   assign dcache_req_2_delayed     = dcache_req_2_shiftreg[15];
   assign dcache_req_3_delayed     = dcache_req_3_shiftreg[15];

   FV_cover_dcache_req_1:  cover property (@(posedge clk) (dcache_req_1));
   FV_cover_dcache_req_1_delayed:  cover property (@(posedge clk) (dcache_req_1_delayed));
   FV_cover_dcache_resp_1: cover property (@(posedge clk) (`FV_ARIANE_LSU_PATH.dcache_req_ports_i[0].data_rvalid == 1));
   FV_cover_dcache_req_2:  cover property (@(posedge clk) (dcache_req_2));
   FV_cover_dcache_req_2_delayed:  cover property (@(posedge clk) (dcache_req_2_delayed));
   FV_cover_dcache_resp_2: cover property (@(posedge clk) (`FV_ARIANE_LSU_PATH.dcache_req_ports_i[1].data_rvalid == 1));
   FV_cover_dcache_req_3:  cover property (@(posedge clk) (dcache_req_3));
   FV_cover_dcache_req_3_delayed:  cover property (@(posedge clk) (dcache_req_3_delayed));
   FV_cover_dcache_resp_3: cover property (@(posedge clk) (`FV_ARIANE_LSU_PATH.dcache_req_ports_i[2].data_rvalid == 1)); // cannot be covered as this port is for writes only (lsu's store buffer to dcache write buffer.


   FV_cover_axi_mem_rd_req:   cover property (@(posedge clk) (`FV_ARIANE_MEM_PATH.axs_arvalid == 1));
   FV_cover_axi_mem_rd_valid: cover property (@(posedge clk) (`FV_ARIANE_MEM_PATH.axs_rvalid == 1));
   FV_cover_axi_mem_wr_req:   cover property (@(posedge clk) (`FV_ARIANE_MEM_PATH.axs_awvalid == 1));
`ifdef FV_INCLUDE_IF_STAGE
   FV_Assert_axi_mem_instr_and_data_return:  assert property (@(posedge clk) (!((`FV_ARIANE_MEM_PATH.axs_rvalid == 1) && 
										  (`FV_ARIANE_MEM_PATH.instr_rvalid == 1))));
`endif
   
// === any atomics req and resp ===
`ifdef FV_INCLUDE_RVA

   FV_cover_amo_req:   cover property (@(posedge clk) (`FV_ARIANE_CACHE_PATH.i_wt_dcache.i_wt_dcache_missunit.state_q == 3'b010)); // AMO state (send req)
   FV_cover_amo_resp:  cover property (@(posedge clk) (`FV_ARIANE_CACHE_PATH.i_wt_dcache.i_wt_dcache_missunit.state_q == 3'b110)); // AMO_WAIT state (wait for resp)

// === LRD ===

   logic instr_amolrd,     instr_amolrd_delayed;
   logic instr_amolrd_dup, instr_amolrd_dup_delayed;
   logic [20:0] instr_amolrd_shiftreg,
		instr_amolrd_dup_shiftreg;
   
   assign instr_amolrd     = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_LR) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == 0);
   assign instr_amolrd_dup = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_LR) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == `FV_DUP_R0P);

   always @(posedge clk) begin
      if(!reset_) begin
	instr_amolrd_shiftreg     <= '0;
	instr_amolrd_dup_shiftreg <= '0;
      end else begin
	instr_amolrd_shiftreg     <= (instr_amolrd_shiftreg     << 1) | {20'b0, instr_amolrd};
	instr_amolrd_dup_shiftreg <= (instr_amolrd_dup_shiftreg << 1) | {20'b0, instr_amolrd_dup};
      end
   end
   assign instr_amolrd_delayed     = instr_amolrd_shiftreg[15];
   assign instr_amolrd_dup_delayed = instr_amolrd_dup_shiftreg[15];
   
   FV_cover_amo_lrd:             cover property (@(posedge clk) (instr_amolrd));
   FV_cover_amo_lrd_dup:         cover property (@(posedge clk) (instr_amolrd_dup));
   FV_cover_amo_lrd_delayed:     cover property (@(posedge clk) (instr_amolrd_delayed));
   FV_cover_amo_lrd_dup_delayed: cover property (@(posedge clk) (instr_amolrd_dup_delayed));

// === SCD ===

   logic instr_amoscd,     instr_amoscd_delayed;
   logic instr_amoscd_dup, instr_amoscd_dup_delayed;
   logic [20:0] instr_amoscd_shiftreg,
		instr_amoscd_dup_shiftreg;
   
   assign instr_amoscd     = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_SC) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == 0);
   assign instr_amoscd_dup = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_SC) &&
			     (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == `FV_DUP_R0P);

   always @(posedge clk) begin
      if(!reset_) begin
	instr_amoscd_shiftreg     <= '0;
	instr_amoscd_dup_shiftreg <= '0;
      end else begin
	instr_amoscd_shiftreg     <= (instr_amoscd_shiftreg     << 1) | {20'b0, instr_amoscd};
	instr_amoscd_dup_shiftreg <= (instr_amoscd_dup_shiftreg << 1) | {20'b0, instr_amoscd_dup};
      end
   end
   assign instr_amoscd_delayed     = instr_amoscd_shiftreg[15];
   assign instr_amoscd_dup_delayed = instr_amoscd_dup_shiftreg[15];
   
   FV_cover_amo_scd:             cover property (@(posedge clk) (instr_amoscd));
   FV_cover_amo_scd_dup:         cover property (@(posedge clk) (instr_amoscd_dup));
   FV_cover_amo_scd_delayed:     cover property (@(posedge clk) (instr_amoscd_delayed));
   FV_cover_amo_scd_dup_delayed: cover property (@(posedge clk) (instr_amoscd_dup_delayed));

// === SWAPD ===
   
   logic instr_amoswapd,     instr_amoswapd_delayed;
   logic instr_amoswapd_dup, instr_amoswapd_dup_delayed;
   logic [20:0] instr_amoswapd_shiftreg,
		instr_amoswapd_dup_shiftreg;
   
   assign instr_amoswapd     = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_AMOSWAP) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == 0);
   assign instr_amoswapd_dup = (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_OPCODE]  == `FV_RV_OPCODE_AMO) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_FUNCT3]  == `FV_RV64A_FUNCT3_D) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32A_INSTR_FIELD_FUNCT5] == `FV_RV32A_FUNCT5_AMOSWAP) &&
			       (ariane_wrapper.fv.core.instr_fetch.instr[1].gen.instr_out.instr[`FV_RV32_INSTR_FIELD_RS1]     == `FV_DUP_R0P);

   always @(posedge clk) begin
      if(!reset_) begin
	instr_amoswapd_shiftreg     <= '0;
	instr_amoswapd_dup_shiftreg <= '0;
      end else begin
	instr_amoswapd_shiftreg     <= (instr_amoswapd_shiftreg     << 1) | {20'b0, instr_amoswapd};
	instr_amoswapd_dup_shiftreg <= (instr_amoswapd_dup_shiftreg << 1) | {20'b0, instr_amoswapd_dup};
      end
   end
   assign instr_amoswapd_delayed     = instr_amoswapd_shiftreg[15];
   assign instr_amoswapd_dup_delayed = instr_amoswapd_dup_shiftreg[15];
   
   FV_cover_amo_swapd:             cover property (@(posedge clk) (instr_amoswapd));
   FV_cover_amo_swapd_dup:         cover property (@(posedge clk) (instr_amoswapd_dup));
   FV_cover_amo_swapd_delayed:     cover property (@(posedge clk) (instr_amoswapd_delayed));
   FV_cover_amo_swapd_dup_delayed: cover property (@(posedge clk) (instr_amoswapd_dup_delayed));
`endif
   

`ifdef FV_INCLUDE_RVF
   FV_cover_fpu_valid_i: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.ex_stage_i.fpu_valid_i));
   FV_cover_fpu_valid_o: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.ex_stage_i.fpu_valid_o));
`endif
   
   FV_cover_illegal_instr: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.id_stage_i.fetch_entry_valid_i && 
							     (`FV_ARIANE_CORE_PATH.id_stage_i.decoder_i.illegal_instr ||
							      `FV_ARIANE_CORE_PATH.id_stage_i.decoder_i.is_illegal_i)));

`ifdef FV_INCLUDE_RVF
 `ifdef FV_INCLUDE_RVZICSR
      
   // do we write to FRM a nonzero value and then write again?
   FV_cover_frm_dynamic: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.csr_regfile_i.frm_o != 3'b0) |=> (`FV_ARIANE_CORE_PATH.csr_regfile_i.frm_o == 3'b0));
   FV_cover_frm_fpu_valid_o: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.csr_regfile_i.frm_o != 3'b0) && (`FV_ARIANE_CORE_PATH.ex_stage_i.fpu_valid_o));
   FV_cover_frm_RF_write_en1: cover property (@(posedge clk) (`FV_ARIANE_CORE_PATH.csr_regfile_i.frm_o != 3'b0) && (rf_write_en[1] == 1));
 `endif
`endif
 
