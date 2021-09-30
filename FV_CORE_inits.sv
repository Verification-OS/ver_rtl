
module FV_CORE_inits(
			 input logic 								 clk, 
			 input logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] 	 arf1,
`ifdef FV_DUT_HAS_RF2
		         input logic [(`FV_NUM_RF2_REGS)-1:0][`FV_REG2_WIDTH-1:0] 	 arf2,
`endif
`ifdef FV_DUT_HAS_RF3
		         input logic [(`FV_NUM_RF3_REGS)-1:0][`FV_REG3_WIDTH-1:0] 	 arf3,
`endif
		         input logic [`FV_DUT_NUM_MEM_REGIONS-1:0][(`DMEM_SIZE/4)-1:0][31:0] dmem,
		         input logic [`FV_DUT_NUM_MEM_REGIONS-1:0] 				 dmem_region_enables,

			 input logic 								 fv_init
			 );

   genvar i;

// ==============
// ARF inits
`ifdef FV_SPLIT_RF_DMEM_SPACE

 `ifdef FV_INCLUDE_RVA
   localparam START_I = 1;

   // init for r0 is redudant in RISC-V ISA
  `ifdef FV_ENABLE_SC_DEBUG
      FV_RF_zero_init_r0:         
  `else
        FV_init_con1_0:
  `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf1[0] == 0));
  `ifdef FV_ENABLE_SC_DEBUG
      FV_RF_zero_init_r0p:         
  `else
        FV_init_con1_0p:
  `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf1[`FV_DUP_R0P] == (`DMEM_SIZE/2)));
 `else
   localparam START_I = 0;
 `endif
	
   for (i = START_I; i < (`FV_NUM_RF_REGS/2); i++) begin
 `ifndef FV_SYMBOLIC_INITIAL_STATE
  `ifdef FV_ENABLE_SC_DEBUG
      FV_RF_zero_init:         
  `else
        FV_init_con1:
  `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf1[FV_FUNC_pairs_orig_reg(i)] == 0));
 `endif
 `ifdef FV_ENABLE_SC_DEBUG
      FV_RF_FV_consistency:   
 `else
	FV_init_con2:
 `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf1[FV_FUNC_pairs_orig_reg(i)] == arf1[FV_FUNC_pairs_dup_reg(i)]));
   end

 `ifdef FV_DUT_HAS_RF2
  `ifdef FV_RF2_ENABLE
   for (i = 0; i < (`FV_NUM_RF2_REGS/2); i++) begin
   `ifndef FV_SYMBOLIC_INITIAL_STATE
    `ifdef FV_ENABLE_SC_DEBUG
      FV_RF2_zero_init:         
    `else
        FV_init_con3:
    `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf2[FV_FUNC_pairs_orig_reg(i)] == 0));
   `endif
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF2_FV_consistency:   
   `else
	FV_init_con4:
   `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf2[FV_FUNC_pairs_orig_reg(i)] == arf2[FV_FUNC_pairs_dup_reg(i)]));
   end
  `else // !`ifdef FV_RF2_ENABLE
   // init to all 0s when not 'enabled' (not used) to avoid the SIS that slows things down
   for (i = 0; i < (`FV_NUM_RF2_REGS); i++) begin
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF2_zero_init:         
   `else
        FV_init_con5:
   `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf2[i] == 0));
   end
  `endif // !`ifdef FV_RF2_ENABLE
 `endif //  `ifdef FV_DUT_HAS_RF2
      
 `ifdef FV_DUT_HAS_RF3
  `ifdef FV_RF3_ENABLE
   for (i = 0; i < (`FV_NUM_RF3_REGS/2); i++) begin
   `ifndef FV_SYMBOLIC_INITIAL_STATE
    `ifdef FV_ENABLE_SC_DEBUG
      FV_RF3_zero_init:         
    `else
        FV_init_con6:
    `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf3[FV_FUNC_pairs_orig_reg(i)] == 0));
   `endif
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF3_FV_consistency:   
   `else
	FV_init_con7:
   `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf3[FV_FUNC_pairs_orig_reg(i)] == arf3[FV_FUNC_pairs_dup_reg(i)]));
   end
  `else // !`ifdef FV_RF3_ENABLE
   // init to all 0s when not 'enabled' (not used) to avoid the SIS that slows things down
   for (i = 0; i < (`FV_NUM_RF3_REGS); i++) begin
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF3_zero_init:         
   `else
        FV_init_con8:
   `endif
	assume property (@(posedge clk) (fv_init)  |-> (arf3[i] == 0));
   end
  `endif // !`ifdef FV_RF3_ENABLE	 
 `endif //  `ifdef FV_DUT_HAS_RF3
      
`else // !`ifdef FV_SPLIT_RF_DMEM_SPACE

 // init ARF to 0 in this case, as the search space changes.
 `ifndef FV_SYMBOLIC_INITIAL_STATE
  // ARF1 is always present
   for (i = 0; i < (`FV_NUM_RF_REGS); i++) begin
  `ifdef FV_ENABLE_SC_DEBUG
      FV_RF_zero_init:   
  `else
        FV_init_con9:
  `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf1[i] == 0));
   end

  `ifdef FV_DUT_HAS_RF2
   for (i = 0; i < (`FV_NUM_RF2_REGS); i++) begin
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF2_zero_init:         
   `else
        FV_init_con10:
   `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf2[i] == 0));
   end
  `endif

  `ifdef FV_DUT_HAS_RF3
   for (i = 0; i < (`FV_NUM_RF3_REGS); i++) begin
   `ifdef FV_ENABLE_SC_DEBUG
      FV_RF3_zero_init:         
   `else
        FV_init_con11:
   `endif
        assume property (@(posedge clk) (fv_init)  |-> (arf3[i] == 0));
   end
  `endif

 `endif //  `ifndef FV_SYMBOLIC_INITIAL_STATE

`endif // !`ifdef FV_SPLIT_RF_DMEM_SPACE

// ==============
// DMEM inits

   genvar j;
   
   for (j=0; j<`FV_DUT_NUM_MEM_REGIONS; j++) begin
      if ((`FV_DUT_MEM_REGION_ENABLES & ({{(`FV_DUT_NUM_MEM_REGIONS-1){1'b0}}, 1'b1} << j)) != 0 ) begin

`ifdef FV_SPLIT_RF_DMEM_SPACE

	 for (i = 0; i < (`DMEM_SIZE/8); i++) begin
 `ifndef FV_SYMBOLIC_INITIAL_STATE
  `ifdef FV_ENABLE_SC_DEBUG
	    FV_DMEM_zero_init:       
  `else
	    FV_init_con12:
  `endif
		assume property (@(posedge clk) (fv_init)  |-> (dmem[j][i] == 0));
 `endif
 `ifdef FV_ENABLE_SC_DEBUG
	    FV_DMEM_FV_consistency: 
 `else
	    FV_init_con13:
 `endif
		assume property (@(posedge clk) (fv_init)  |-> (dmem[j][i] == dmem[j][i+(`DMEM_SIZE/8)]));
	 end // for (i = 0; i < (`DMEM_SIZE/8); i++)
	 
`else // !`ifdef FV_SPLIT_RF_DMEM_SPACE

 `ifndef FV_SYMBOLIC_INITIAL_STATE
	 for (i = 0; i < (`DMEM_SIZE/4); i++) begin
  `ifdef FV_ENABLE_SC_DEBUG
	    FV_DMEM_zero_init: 
  `else
	    FV_init_con14:
  `endif
		assume property (@(posedge clk) (fv_init)  |-> (dmem[j][i] == 0));
	 end
 `endif //  `ifndef FV_SYMBOLIC_INITIAL_STATE

`endif // !`ifdef FV_SPLIT_RF_DMEM_SPACE

      end // if ((`FV_DUT_MEM_REGION_ENABLES & ({{(`FV_DUT_NUM_MEM_REGIONS-1){1'b0}}, 1'b1} << j)) != 0 )
   end // for (j=0; j<`FV_DUT_NUM_MEM_REGIONS; j++)
   
endmodule // FV_CORE_inits

