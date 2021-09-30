
module fv();

   logic clk;
   logic reset_;

   arf_signals_t                                                     arf_sigs;
   
   logic [`FV_DUT_NUM_MEM_REGIONS-1:0][(`DMEM_SIZE/4)-1:0][31:0] dmem; // data memory
   logic [`FV_DUT_NUM_MEM_REGIONS-1:0] 			     dmem_region_enables;
   
   logic 						    ld_st_valid;
   logic [`FV_MEM_ADDR_WIDTH-1:0] 			    ld_st_effaddr;
   logic [`FV_REG_WIDTH-1:0] 			    ld_st_imm;
   
   logic [`FV_INSTR_ADDR_WIDTH-1:0] 		    IF_pc; // PC of the instruction to be fetched from memory
   logic [`FV_INSTR_ADDR_WIDTH-1:0] 		    IF_mem_fetch_addr; // memory address of instruction fetch (could be aligned to memory interface width)
   logic 						    IF_stall; // instruction fetch stage stall
   logic 						    IF_kill;  // instruction fetch stage kill 
   // IF_kill: Cancels all instructions in the fetch unit and flushes the pipeline.  This includes all cases that lead to pipeline kill/cancel such as branch misprediction.

   logic                                                             IF_instruction_req_grant;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 		             IF_instruction_out_valid;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] IF_instruction_out;
   logic [`FV_IF_BUS_WIDTH-1:0] 				     IF_instruction_bus_out;
   logic [`FV_INSTR_ADDR_WIDTH-1:0] 			     IF_instruction_pc; // PC of the instruction that was fetched from memory (fetched PC)
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			     IF2EX_instruction_in_valid; // could be same as or modified IF_instruction_out_valid
   logic [`FV_INSTR_ADDR_WIDTH-1:0] 			     IF2EX_pc;    // PC of the instruction being issued/executed
   logic 							     IF2EX_stall; // instruction issue to execution stage stall
   logic 							     IF2EX_kill;  // instruction issue to execution stage kill 

   logic 							     EX_stall; // instruction execution stage stall
   logic 							     EX_kill;  // instruction execution stage kill 

   logic [`FV_MAX_COMMIT_PER_CYCLE:1] 			     commit;      // instr commit flag(s)

   logic 						    dut_branch_taken;
   logic 						    dut_jump_taken;
   logic [`FV_NUM_RF_WR_PORTS:1]			    fv_override_rf_wdata;

   prop_signals_t                                           ps;
   
   FV_core  core(.*);
   FV_binds binds(.*);
   FV_prop  properties(.*);
   FV_cov   coverage(.*);

endmodule // fv



