
module FV_CORE_EX_rf(
			 input logic 							      clk,
			 input logic 							      reset_,
   
			 input logic [`FV_NUM_RF_WR_PORTS:1] 			      rf_write_en,
			 input logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0]  rf_write_rd,
`ifdef FV_RF2_ENABLE
			 input logic [`FV_NUM_RF2_WR_PORTS:1] 			      rf2_write_en,
			 input logic [`FV_NUM_RF2_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf2_write_rd,
`endif
`ifdef FV_RF3_ENABLE
			 input logic [`FV_NUM_RF3_WR_PORTS:1] 			      rf3_write_en,
			 input logic [`FV_NUM_RF3_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf3_write_rd,
`endif

			 input logic [`FV_NUM_RF_WR_PORTS:1] 			      rf_lock, 
			 input logic [`FV_NUM_RF_WR_PORTS:1] 			      rf_unlock,
			 input logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0]  rf_lock_num,
   
			 input logic 							      dup_enable,

			 input logic 							      fv_dup_sync_ready,
			 input logic 							      dup_done

			 // outputs are taken in the FV_core module using hierarchical path
			 );
   
   localparam FV_TOTAL_COUNTER_WIDTH = ($clog2(`FV_MAX_BMC_DEPTH*`FV_NUM_RF_WR_PORTS)+1);
   localparam FV_RF_WR_COUNTER_WIDTH = ($clog2(`FV_NUM_RF_WR_PORTS)+1);
   //=========================

   logic fv_ready;
   logic [FV_TOTAL_COUNTER_WIDTH-1:0]  total_num_orig_rf_writes;
   logic [FV_TOTAL_COUNTER_WIDTH-1:0]  total_num_dup_rf_writes;
   logic [`FV_NUM_RF_WR_PORTS:1] 	   orig_rf_write, dup_rf_write;
   logic [FV_RF_WR_COUNTER_WIDTH-1:0]  num_orig_rf_writes, num_dup_rf_writes;
   

   genvar i;

   for (i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
      // Note: the following is true for RISC-V ISA; change for other ISAs
      // Instruction with destination register as 5'b0 is a NOP so ignore those
      // When destination register is 5'b0, it remains the same for both original and duplicate
      // r0', if used, has special purpose
      // when that's done, then this module can be parameterized in a way that 
      // it can be instantiated multiple times for each RF
      assign orig_rf_write[i] = (rf_write_en[i] == 1) && 
				(!FV_FUNC_is_dup_reg(rf_write_rd[i])) && 
`ifndef FV_DUP_PAIR_R1
				(rf_write_rd[i] != 5'b1) &&
`endif
				(rf_write_rd[i] != 5'b0);

      assign dup_rf_write[i]  = (rf_write_en[i] == 1) && 
				(FV_FUNC_is_dup_reg(rf_write_rd[i])) && 
`ifndef FV_DUP_PAIR_R1
				(rf_write_rd[i] != FV_FUNC_dup_reg(5'b1)) &&
`endif
				(rf_write_rd[i] != `FV_DUP_R0P);
   end
   
   always @(*) begin
      num_orig_rf_writes = 0;
      num_dup_rf_writes  = 0;
      for (int i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
	 num_orig_rf_writes = num_orig_rf_writes + {{(FV_RF_WR_COUNTER_WIDTH-1){1'b0}}, orig_rf_write[i]};
	 num_dup_rf_writes  = num_dup_rf_writes  + {{(FV_RF_WR_COUNTER_WIDTH-1){1'b0}}, dup_rf_write[i]};
      end
   end

   // individual reg tracking
   logic [`FV_NUM_RF_REGS-1:0][FV_TOTAL_COUNTER_WIDTH-1:0] rf_write_counters;
   logic [`FV_NUM_RF_REGS-1:0][FV_RF_WR_COUNTER_WIDTH-1:0] rf_writes;
   logic [`FV_NUM_RF_REGS-1:0] 				   rf_locks;

   always @(*)
     begin
	for (int i=0; i < (`FV_NUM_RF_REGS); i++) begin
	   rf_writes[i] = 0;
	   for (int j=1; j <= (`FV_NUM_RF_WR_PORTS); j++) begin
	      if (rf_write_en[j] && (rf_write_rd[j] == i))
		rf_writes[i] = rf_writes[i] + 1;
	   end
	end
     end   

   always @(posedge clk)
     begin
	if (!reset_) begin
	   total_num_orig_rf_writes <= {FV_TOTAL_COUNTER_WIDTH{1'b0}};
	   total_num_dup_rf_writes  <= {FV_TOTAL_COUNTER_WIDTH{1'b0}};
	   for (int i=0; i < (`FV_NUM_RF_REGS); i++) begin
	      rf_write_counters[i] <= {FV_TOTAL_COUNTER_WIDTH{1'b0}};
	   end
	end else begin
	   total_num_orig_rf_writes <= total_num_orig_rf_writes + {{(FV_TOTAL_COUNTER_WIDTH-FV_RF_WR_COUNTER_WIDTH){1'b0}}, num_orig_rf_writes};
	   total_num_dup_rf_writes  <= total_num_dup_rf_writes  + {{(FV_TOTAL_COUNTER_WIDTH-FV_RF_WR_COUNTER_WIDTH){1'b0}}, num_dup_rf_writes};
	   for (int i=0; i < (`FV_NUM_RF_REGS); i++) begin
	      rf_write_counters[i] <= rf_write_counters[i] + {{(FV_TOTAL_COUNTER_WIDTH-FV_RF_WR_COUNTER_WIDTH){1'b0}}, (rf_writes[i])};
	   end
	end
     end

   assign fv_ready = ((total_num_orig_rf_writes == total_num_dup_rf_writes) || dup_done) && dup_enable;

   always @(posedge clk)
     begin
	if (!reset_) begin
	   for (int i=0; i < (`FV_NUM_RF_REGS); i++) begin
	      rf_locks[i] <= 0;
	   end
	end else begin
	   for (int i=0; i < (`FV_NUM_RF_REGS); i++) begin
	      for (int j=1; j<=`FV_NUM_RF_WR_PORTS; j++) begin
		 if (rf_lock[j] && (rf_lock_num[j] == i))
		   rf_locks[i] <= 1;
		 if (rf_unlock[j] && (rf_lock_num[j] == i))
		   rf_locks[i] <= 0;
	      end
	   end
	end
     end // always @ (posedge clk)

`ifdef FV_ENABLE_SC_DEBUG
 `ifdef FV_NO_DUP_SYNC_READY
   // DUP_sync_ready and reg compare on sync cannot work because of variable latency from sync_ready (commit) to RF write; e.g., riscy core
 `else
   FV_SC_DUP_CF_rf_unlocked_on_sync: assert property (@(posedge clk) fv_dup_sync_ready |-> ((|rf_locks) == 0));
 `endif
`endif
   
   logic                               fv_dup_ready;
   logic [(`FV_NUM_RF_REGS/2)-1:0] fv_dup_ready_pairs;
   
   always @(*)
   begin
      for (int i=0; i < (`FV_NUM_RF_REGS/2); i++) begin
	 if ((        (!rf_locks[FV_FUNC_pairs_orig_reg(i)]) &&       (!rf_locks[FV_FUNC_pairs_dup_reg(i)]) && 
	      (rf_write_counters[FV_FUNC_pairs_orig_reg(i)] == rf_write_counters[FV_FUNC_pairs_dup_reg(i)])) ||
	     dup_done)
	    fv_dup_ready_pairs[i] = 1;
	 else
	    fv_dup_ready_pairs[i] = 0;
      end
   end
  
   //=========================
   //=========================

   assign fv_dup_ready = fv_ready;

`ifdef FV_RF2_ENABLE
   localparam FV_TOTAL2_COUNTER_WIDTH = ($clog2(`FV_MAX_BMC_DEPTH*`FV_NUM_RF2_WR_PORTS)+1);
   localparam FV_RF2_WR_COUNTER_WIDTH = ($clog2(`FV_NUM_RF2_WR_PORTS)+1);

   logic fv_ready_2;
   logic [FV_TOTAL2_COUNTER_WIDTH-1:0]  total_num_orig_rf2_writes;
   logic [FV_TOTAL2_COUNTER_WIDTH-1:0]  total_num_dup_rf2_writes;
   logic [`FV_NUM_RF2_WR_PORTS:1] 	    orig_rf2_write, dup_rf2_write;
   logic [FV_RF2_WR_COUNTER_WIDTH-1:0]  num_orig_rf2_writes, num_dup_rf2_writes;
   
   for (i=1; i<=`FV_NUM_RF2_WR_PORTS; i++) begin
      assign orig_rf2_write[i] = (rf2_write_en[i] == 1) && (!FV_FUNC_is_dup_reg(rf2_write_rd[i]));
      assign dup_rf2_write[i]  = (rf2_write_en[i] == 1) &&  (FV_FUNC_is_dup_reg(rf2_write_rd[i]));
   end
   
   always @(*) begin
      num_orig_rf2_writes = 0;
      num_dup_rf2_writes  = 0;
      for (int i=1; i<=`FV_NUM_RF2_WR_PORTS; i++) begin
	 num_orig_rf2_writes = num_orig_rf2_writes + {{(FV_RF2_WR_COUNTER_WIDTH-1){1'b0}}, orig_rf2_write[i]};
	 num_dup_rf2_writes  = num_dup_rf2_writes  + {{(FV_RF2_WR_COUNTER_WIDTH-1){1'b0}}, dup_rf2_write[i]};
      end
   end

   // individual reg tracking
   logic [`FV_NUM_RF2_REGS-1:0][FV_TOTAL2_COUNTER_WIDTH-1:0] rf2_write_counters;
   logic [`FV_NUM_RF2_REGS-1:0][FV_RF2_WR_COUNTER_WIDTH-1:0] rf2_writes;

   always @(*)
     begin
	for (int i=0; i < (`FV_NUM_RF2_REGS); i++) begin
	   rf2_writes[i] = 0;
	   for (int j=1; j <= (`FV_NUM_RF2_WR_PORTS); j++) begin
	      if (rf2_write_en[j] && (rf2_write_rd[j] == i))
		rf2_writes[i] = rf2_writes[i] + 1;
	   end
	end
     end   

   always @(posedge clk)
     begin
	if (!reset_) begin
	   total_num_orig_rf2_writes <= {FV_TOTAL2_COUNTER_WIDTH{1'b0}};
	   total_num_dup_rf2_writes  <= {FV_TOTAL2_COUNTER_WIDTH{1'b0}};
	   for (int i=0; i < (`FV_NUM_RF2_REGS); i++) begin
	      rf2_write_counters[i] <= {FV_TOTAL2_COUNTER_WIDTH{1'b0}};
	   end
	end else begin
	   total_num_orig_rf2_writes <= total_num_orig_rf2_writes + {{(FV_TOTAL2_COUNTER_WIDTH-FV_RF2_WR_COUNTER_WIDTH){1'b0}}, num_orig_rf2_writes};
	   total_num_dup_rf2_writes  <= total_num_dup_rf2_writes  + {{(FV_TOTAL2_COUNTER_WIDTH-FV_RF2_WR_COUNTER_WIDTH){1'b0}}, num_dup_rf2_writes};
	   for (int i=0; i < (`FV_NUM_RF2_REGS); i++) begin
	      rf2_write_counters[i] <= rf2_write_counters[i] + {{(FV_TOTAL2_COUNTER_WIDTH-FV_RF2_WR_COUNTER_WIDTH){1'b0}}, (rf2_writes[i])};
	   end
	end
     end

   assign fv_ready_2 = ((total_num_orig_rf2_writes == total_num_dup_rf2_writes) || dup_done) && dup_enable;
   
   logic                                fv_dup_ready_2;
   logic [(`FV_NUM_RF2_REGS/2)-1:0] fv_dup_ready_pairs_2;
   
   always @(*)
   begin
      for (int i=0; i < (`FV_NUM_RF2_REGS/2); i++) begin
	 if (((rf2_write_counters[FV_FUNC_pairs_orig_reg(i)] == rf2_write_counters[FV_FUNC_pairs_dup_reg(i)])) ||
	     dup_done)
	    fv_dup_ready_pairs_2[i] = 1;
	 else
	    fv_dup_ready_pairs_2[i] = 0;
      end
   end
  
   assign fv_dup_ready_2 = fv_ready_2;

`endif //  `ifdef FV_RF2_ENABLE

`ifdef FV_RF3_ENABLE
   localparam FV_TOTAL3_COUNTER_WIDTH = ($clog2(`FV_MAX_BMC_DEPTH*`FV_NUM_RF3_WR_PORTS)+1);
   localparam FV_RF3_WR_COUNTER_WIDTH = ($clog2(`FV_NUM_RF3_WR_PORTS)+1);

   logic fv_ready_3;
   logic [FV_TOTAL3_COUNTER_WIDTH-1:0]  total_num_orig_rf3_writes;
   logic [FV_TOTAL3_COUNTER_WIDTH-1:0]  total_num_dup_rf3_writes;
   logic [`FV_NUM_RF3_WR_PORTS:1] 	    orig_rf3_write, dup_rf3_write;
   logic [FV_RF3_WR_COUNTER_WIDTH-1:0]  num_orig_rf3_writes, num_dup_rf3_writes;
   
   for (i=1; i<=`FV_NUM_RF3_WR_PORTS; i++) begin
      assign orig_rf3_write[i] = (rf3_write_en[i] == 1) && (!FV_FUNC_is_dup_reg(rf3_write_rd[i]));
      assign dup_rf3_write[i]  = (rf3_write_en[i] == 1) &&  (FV_FUNC_is_dup_reg(rf3_write_rd[i]));
   end
   
   always @(*) begin
      num_orig_rf3_writes = 0;
      num_dup_rf3_writes  = 0;
      for (int i=1; i<=`FV_NUM_RF3_WR_PORTS; i++) begin
	 num_orig_rf3_writes = num_orig_rf3_writes + {{(FV_RF3_WR_COUNTER_WIDTH-1){1'b0}}, orig_rf3_write[i]};
	 num_dup_rf3_writes  = num_dup_rf3_writes  + {{(FV_RF3_WR_COUNTER_WIDTH-1){1'b0}}, dup_rf3_write[i]};
      end
   end

   // individual reg tracking
   logic [`FV_NUM_RF3_REGS-1:0][FV_TOTAL3_COUNTER_WIDTH-1:0] rf3_write_counters;
   logic [`FV_NUM_RF3_REGS-1:0][FV_RF3_WR_COUNTER_WIDTH-1:0] rf3_writes;

   always @(*)
     begin
	for (int i=0; i < (`FV_NUM_RF3_REGS); i++) begin
	   rf3_writes[i] = 0;
	   for (int j=1; j <= (`FV_NUM_RF3_WR_PORTS); j++) begin
	      if (rf3_write_en[j] && (rf3_write_rd[j] == i))
		rf3_writes[i] = rf3_writes[i] + 1;
	   end
	end
     end   

   always @(posedge clk)
     begin
	if (!reset_) begin
	   total_num_orig_rf3_writes <= {FV_TOTAL3_COUNTER_WIDTH{1'b0}};
	   total_num_dup_rf3_writes  <= {FV_TOTAL3_COUNTER_WIDTH{1'b0}};
	   for (int i=0; i < (`FV_NUM_RF3_REGS); i++) begin
	      rf3_write_counters[i] <= {FV_TOTAL3_COUNTER_WIDTH{1'b0}};
	   end
	end else begin
	   total_num_orig_rf3_writes <= total_num_orig_rf3_writes + {{(FV_TOTAL3_COUNTER_WIDTH-FV_RF3_WR_COUNTER_WIDTH){1'b0}}, num_orig_rf3_writes};
	   total_num_dup_rf3_writes  <= total_num_dup_rf3_writes  + {{(FV_TOTAL3_COUNTER_WIDTH-FV_RF3_WR_COUNTER_WIDTH){1'b0}}, num_dup_rf3_writes};
	   for (int i=0; i < (`FV_NUM_RF3_REGS); i++) begin
	      rf3_write_counters[i] <= rf3_write_counters[i] + {{(FV_TOTAL3_COUNTER_WIDTH-FV_RF3_WR_COUNTER_WIDTH){1'b0}}, (rf3_writes[i])};
	   end
	end
     end

   assign fv_ready_3 = ((total_num_orig_rf3_writes == total_num_dup_rf3_writes) || dup_done) && dup_enable;
   
   logic                                fv_dup_ready_3;
   logic [(`FV_NUM_RF3_REGS/2)-1:0] fv_dup_ready_pairs_3;
   
   always @(*)
   begin
      for (int i=0; i < (`FV_NUM_RF3_REGS/2); i++) begin
	 if (((rf3_write_counters[FV_FUNC_pairs_orig_reg(i)] == rf3_write_counters[FV_FUNC_pairs_dup_reg(i)])) ||
	     dup_done)
	    fv_dup_ready_pairs_3[i] = 1;
	 else
	    fv_dup_ready_pairs_3[i] = 0;
      end
   end
  
   assign fv_dup_ready_3 = fv_ready_3;

`endif //  `ifdef FV_RF3_ENABLE

   // =======================

   // Note: update
`ifdef FV_DUT_RF_SAME_REG_WRITE_NOT_ALLOWED
   // should not write to the same register from the two ports at the same time
   FV_DUT_Property_RF_writes:   assert property (@(posedge clk) (rf_write_en[1] && rf_write_en[2]) |-> (rf_write_rd[1] != rf_write_rd[2]));  
`endif
      
endmodule // FV_CORE_EX_rf
