
module FV_binds(
		    output logic 							    clk,
		    output logic 							    reset_,

		    output arf_signals_t                                                    arf_sigs,

		    output logic [`FV_DUT_NUM_MEM_REGIONS-1:0][(`DMEM_SIZE/4)-1:0][31:0] dmem,
		    output logic [`FV_DUT_NUM_MEM_REGIONS-1:0]                           dmem_region_enables,

		    output logic 							    ld_st_valid,
		    output logic [`FV_MEM_ADDR_WIDTH-1:0] 				    ld_st_effaddr,
		    output logic [`FV_REG_WIDTH-1:0] 				    ld_st_imm,

		    // instruction fetch related signals
                    input logic 							    IF_instruction_req_grant,
		    input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			    IF_instruction_out_valid,
		    input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] IF_instruction_out,
  		    input logic [`FV_IF_BUS_WIDTH-1:0] 				    IF_instruction_bus_out,
		    input logic [`FV_INSTR_ADDR_WIDTH-1:0] 				    IF_instruction_pc,

		    output logic [`FV_INSTR_ADDR_WIDTH-1:0] 			    IF_pc,
		    output logic [`FV_INSTR_ADDR_WIDTH-1:0] 			    IF_mem_fetch_addr,
		    output logic 							    IF_stall,
		    output logic 							    IF_kill,

		    // instruction execution related signals
		    output logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			    IF2EX_instruction_in_valid,
		    output logic [`FV_INSTR_ADDR_WIDTH-1:0] 			    IF2EX_pc,
		    output logic 							    IF2EX_stall,
		    output logic 							    IF2EX_kill,

		    output logic 							    EX_stall,
		    output logic 							    EX_kill,

		    output logic [`FV_MAX_COMMIT_PER_CYCLE:1] 			    commit,

		    output logic 							    dut_branch_taken,
		    output logic 							    dut_jump_taken,
		    input logic [`FV_NUM_RF_WR_PORTS:1] 				    fv_override_rf_wdata	    
		    );

   genvar i;

   logic [`FV_NUM_RF_WR_PORTS:1]                              rf_write_en;
   logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0]  rf_write_rd;
`ifdef FV_DUT_HAS_RF2
   logic [`FV_NUM_RF2_WR_PORTS:1] 				  rf2_write_en;
   logic [`FV_NUM_RF2_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf2_write_rd;
`endif
`ifdef FV_DUT_HAS_RF3
   logic [`FV_NUM_RF3_WR_PORTS:1] 				  rf3_write_en;
   logic [`FV_NUM_RF3_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf3_write_rd;
`endif

   // =======================   

`include "FV_BINDS_dut.svh"

   // =======================   

   for (i = 0; i < (`FV_NUM_RF_REGS); i++) begin
      assign arf_sigs.arf1[i] = regs[i];
   end
   for (i = 1; i <= (`FV_NUM_RF_WR_PORTS); i++) begin
      assign arf_sigs.rf1_write_en[i] = rf_write_en[i];
      assign arf_sigs.rf1_write_rd[i] = rf_write_rd[i];
   end
   
`ifdef FV_DUT_HAS_RF2
   for (i = 0; i < (`FV_NUM_RF2_REGS); i++) begin
      assign arf_sigs.arf2[i] = regs2[i];
   end
   for (i = 1; i <= (`FV_NUM_RF2_WR_PORTS); i++) begin
      assign arf_sigs.rf2_write_en[i] = rf2_write_en[i];
      assign arf_sigs.rf2_write_rd[i] = rf2_write_rd[i];
   end
`endif

`ifdef FV_DUT_HAS_RF3
   for (i = 0; i < (`FV_NUM_RF3_REGS); i++) begin
      assign arf_sigs.arf3[i] = regs3[i];
   end
   for (i = 1; i <= (`FV_NUM_RF3_WR_PORTS); i++) begin
      assign arf_sigs.rf3_write_en[i] = rf3_write_en[i];
      assign arf_sigs.rf3_write_rd[i] = rf3_write_rd[i];
   end
`endif

endmodule // FV_binds
