
module FV_CORE_constraints(
			       input 				  clk,
			       input 				  ld_st_valid,
			       input [`FV_MEM_ADDR_WIDTH-1:0] ld_st_effaddr,
			       input [`FV_REG_WIDTH-1:0] 	  ld_st_imm
			       );

   always @(posedge clk) begin
      // general constraint to stay within data memory size
      assume property (ld_st_valid |-> (ld_st_effaddr < `DMEM_SIZE));

      // Note0: should be stay double-word below upper end?

`ifdef FV_SPLIT_RF_DMEM_SPACE
      // splitting the effective address of original instructions from duplicate instructions

 `ifndef FV_LIMIT_LS_BASE_R0
   // Add the constraint if not using only R0 as base address.  
   // With only R0 as base, the constraint is already enforced through imm values constraint and transformation for duplicates.
   
      assume property (ld_st_valid |->
		       (((ld_st_imm[6] == 0) && (ld_st_effaddr <  (`DMEM_SIZE/2))) || 
 			((ld_st_imm[6] == 1) && (ld_st_effaddr >= (`DMEM_SIZE/2)))));
 `endif //  `ifndef FV_LIMIT_LS_BASE_R0

`endif //  `ifdef FV_SPLIT_RF_DMEM_SPACE

   end

   
endmodule // FV_CORE_constraints

