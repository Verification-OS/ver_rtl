
module FV_CORE_ex( // inputs
		       input logic 							    clk,
		       input logic 							    reset_,

		       input logic 							    dup_enable,
		       input logic 							    cmt_enable,
		       input logic 							    cf_enable,
		       input logic 							    si_enable,

		       input arf_signals_t                                                  arf_sigs,

		       // instruction execution related signals
		       input 								    if_queue_entry_t IF2EX_instr_in[`FV_IF_MAX_INSTR_PER_CYCLE:1],
		       input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			    IF2EX_instr_in_valid,
		       input logic [`FV_INSTR_ADDR_WIDTH-1:0] 			    IF2EX_pc,
		       input logic 							    IF2EX_stall,
		       input logic 							    IF2EX_kill,

		       input logic 							    EX_stall,
		       input logic 							    EX_kill,
		       output logic 							    EX2IF_killed_instr_found,
		       output 								    ex_queue_entry_t EX2IF_killed_instr,
		       
		       input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 			    commit,

		       input logic 							    dut_branch_taken,
		       input logic 							    dut_jump_taken, 
		       output logic [`FV_NUM_RF_WR_PORTS:1] 			    fv_override_rf_wdata,
										  
		       // outputs for FV_prop
		       output logic [9:0] 						    fv_num_committed_instr
		       );

   genvar i;
   
`ifdef FV_ENABLE_DUP
   logic  dup_sync_point;
   always @(*) begin
      dup_sync_point = 0;
      for (int i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin
	 dup_sync_point = dup_sync_point || (commit[i] &&
					       FV_FUNC_instr_is_dup_sync(queue_next_commit_entry[i].instr));

      end
   end

   logic  dup_done; // a sequence of original instructions followed by its duplicate has finished

   always @(posedge clk) begin
      if (!reset_)
	dup_done            <= 0;
      // if not, then never done
 `ifdef FV_DUP_DO_ONE_SET
      else if (dup_sync_point)
	dup_done            <= 1;
 `endif
   end

   logic fv_dup_sync_ready, fv_dup_sync_ready_predelay;
   assign fv_dup_sync_ready_predelay = dup_enable && cf_enable && (dup_sync_point || dup_done);
   
   FV_delay_signal #(.DELAY_AMOUNT(`FV_COMMIT_TO_RF_WR_DELAY), .MAX_DELAY(`FV_COMMIT_TO_RF_WR_DELAY_MAX), .RESET_VALUE(1)) 
      delay_sync_ready(.clk(clk), .reset_(reset_),
		       .in(fv_dup_sync_ready_predelay), .out(fv_dup_sync_ready));
     
`else // !`ifdef FV_ENABLE_DUP
   assign dup_done       = 0;
   assign fv_dup_sync_ready = 0;
`endif //  `ifdef FV_ENABLE_DUP

   // internal connections
   logic [`FV_NUM_RF_WR_PORTS:1] rf_lock;
   logic [`FV_NUM_RF_WR_PORTS:1] rf_unlock;
   logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf_lock_num;

   ex_queue_entry_t queue_head[`FV_MAX_COMMIT_PER_CYCLE:1];
   ex_queue_entry_t queue_next_commit_entry[`FV_MAX_COMMIT_PER_CYCLE:1];
   
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] have_at_least_2_committed_instrs;
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] have_at_least_1_uncommitted_instrs;
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] check_committed_instr;
   logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_committed_next_pc;
   
   // =========================
   // RF write tracking for DUP
   FV_CORE_EX_rf rf_tracker(.*,
`ifdef FV_RF2_ENABLE
				.rf2_write_en(arf_sigs.rf2_write_en),
				.rf2_write_rd(arf_sigs.rf2_write_rd),
`endif
`ifdef FV_RF3_ENABLE
				.rf3_write_en(arf_sigs.rf3_write_en),
				.rf3_write_rd(arf_sigs.rf3_write_rd),
`endif
				.rf_write_en(arf_sigs.rf1_write_en),
				.rf_write_rd(arf_sigs.rf1_write_rd)
				);

   //=========================
   // executing instructions queue
   logic  ex_queue_enable;
   assign ex_queue_enable = dup_enable || cf_enable;
   
   FV_CORE_EX_queue instr_queue(
`ifdef FV_ENABLE_SI
				    .arf(arf_sigs.arf1),
`endif				    
				    .*
				    );
   
   //=========================
   // CF logic
   FV_CORE_EX_cf cf_tracker(.*,
				.arf(arf_sigs.arf1),
				.rf_write_en(arf_sigs.rf1_write_en),
				.rf_write_rd(arf_sigs.rf1_write_rd)
				);


   //=========================
   // CMT logic

   logic [9:0] fv_num_committed_instr_inc;
   
   always @(*) begin
      fv_num_committed_instr_inc = 0;
      for (int i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin
	 if (commit[i] ==1)
	   fv_num_committed_instr_inc = fv_num_committed_instr_inc + {10'b1};
      end
   end

   always @(posedge clk)
     begin
	if (!reset_) begin
	   fv_num_committed_instr <= 10'b0;
	end else begin
	   fv_num_committed_instr <= fv_num_committed_instr + fv_num_committed_instr_inc;
	end
     end

   // ===============
   // assertions

// ==============================
// ==============================
     
`ifdef FV_DUP_NO_RND_MIX
   logic 	dup_flush_point; 
   assign dup_flush_point     = commit[1] && FV_FUNC_is_nop_flush(next_commit_instr1);
   FV_dup_flush_cover1: cover property (@(posedge clk) (dup_flush_point) && (next_commit_pointer > 2));
   FV_dup_flush_cover2: cover property (@(posedge clk) (dup_flush_point) && (next_commit_pointer > 5));
   FV_dup_flush_cover3: cover property (@(posedge clk) (dup_flush_point) && (next_commit_pointer > 10));

   FV_dup_sync_cover1: cover property (@(posedge clk) (dup_sync_point) && (next_commit_pointer > 2));
   FV_dup_sync_cover2: cover property (@(posedge clk) (dup_sync_point) && (next_commit_pointer > 5));
   FV_dup_sync_cover3: cover property (@(posedge clk) (dup_sync_point) && (next_commit_pointer > 10));

   logic 	pipe_end_in_dup_mode;
   
   always @(posedge clk) begin
      if (!reset_) begin
	 pipe_end_in_dup_mode <= 0;
      end else if (dup_flush_point) begin
	 pipe_end_in_dup_mode <= 1;
      end else if (dup_sync_point) begin
	 pipe_end_in_dup_mode <= 0;
      end
   end

`endif //  `ifdef FV_DUP_NO_RND_MIX
   
endmodule // FV_CORE_ex

