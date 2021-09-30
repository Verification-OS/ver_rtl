
module FV_CORE_EX_cf( // inputs
			  input logic 								      clk,
			  input logic 								      reset_,

			  input logic 								      cf_enable,
			  input logic 								      ex_queue_enable,
			  input logic 								      si_enable,

			  input logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] 	      arf,

			  // inputs from DUT
			  input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				      commit,
			  input logic [`FV_NUM_RF_WR_PORTS:1] 				      rf_write_en,
			  input logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] 	      rf_write_rd,
			  input logic 								      dut_branch_taken,
			  // dut_branch_taken is used for finding the instruction corresponding to the kill signal, and 
			  // it should come before or in the same cycle as the commit signal of the corresponding branch instruction
			  input logic 								      dut_jump_taken,
			  // dut_jump_taken is used for checking committing jump instructions generate a kill

			  // internal inputs			  
			  input 								      ex_queue_entry_t queue_head[`FV_MAX_COMMIT_PER_CYCLE:1],
			  input 								      ex_queue_entry_t queue_next_commit_entry[`FV_MAX_COMMIT_PER_CYCLE:1],
			  input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				      have_at_least_2_committed_instrs,
			  input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				      have_at_least_1_uncommitted_instrs,
			  // internal outputs
			  output logic [`FV_MAX_COMMIT_PER_CYCLE:1] 			      check_committed_instr, // for updating EX_queue head_pointer

			  output logic [`FV_NUM_RF_WR_PORTS:1] 				      rf_lock, 
			  output logic [`FV_NUM_RF_WR_PORTS:1] 				      rf_unlock,
			  output logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] 	      rf_lock_num,
		       
			  output logic [`FV_NUM_RF_WR_PORTS:1] 				      fv_override_rf_wdata
			  );

   localparam COMMITS_PER_CYCLE=`FV_MAX_COMMIT_PER_CYCLE;
   genvar i;
   
   // ======================
   // general next PC checks

   logic [`FV_MAX_COMMIT_PER_CYCLE:1] cf_check;
   
   for (i=1; i<=`FV_MAX_COMMIT_PER_CYCLE;i++) begin
      assign check_committed_instr[i] = have_at_least_2_committed_instrs[i]; // because we use the saved PC of the second instr to check the next PC of the first
      assign cf_check[i]           = cf_enable && check_committed_instr[i];
   end

`ifndef FV_ENABLE_SI
   logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_correct_next_pc2;
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				instr_is_exempt;
`endif
   logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_correct_next_pc1;

   for (i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin : CF_check
      FV_instr_correct_next_pc calc_next_pc(.instr_entry(queue_head[i]),
`ifndef FV_ENABLE_SI
					     .correct_next_pc2(instr_correct_next_pc2[i]),
					     .instr_is_exempt(instr_is_exempt[i]),
`endif
					     .correct_next_pc1(instr_correct_next_pc1[i])
					     );
   end

   // ===============
   // IMPORTANT NOTE: 
   // ===============
   // The big assumption here is that there will be only one branch unit present and 
   // therefore only one CF_checked instruction is committed in each cycle.
   
   logic [`FV_INSTR_WIDTH-1:0] next_CF_commit_instr;

   ex_queue_entry_t                queue_next_CF_commit_entry;
   logic 			   have_at_least_1_uncommitted_CF_instr;
   integer 			   next_CF_commit_index;

   logic [`FV_MAX_COMMIT_PER_CYCLE+1:1] commit_extended;   // adding an extra MSB tied to zero for easy coding
   assign commit_extended[`FV_MAX_COMMIT_PER_CYCLE+1] = 0; // tie to 0; obviously not additional commit
   
   always @(*) begin
       // its OK if the following two are not really a CF_checked instr
      queue_next_CF_commit_entry           = queue_next_commit_entry[1];
      have_at_least_1_uncommitted_CF_instr = have_at_least_1_uncommitted_instrs[1];
      next_CF_commit_index                 = 1;
      
      // counting backwards to find the first CF_checked instr
      for (int i=`FV_MAX_COMMIT_PER_CYCLE; i>=1; i--) begin

	 commit_extended[i] = commit[i]; // simple replication to the extended vector

	 if (FV_FUNC_instr_is_CF_checked(queue_next_commit_entry[i].instr)) begin
	    queue_next_CF_commit_entry           = queue_next_commit_entry[i];
	    have_at_least_1_uncommitted_CF_instr = have_at_least_1_uncommitted_instrs[i];
	    next_CF_commit_index                 = i;
	 end

      end
   end
   
   assign next_CF_commit_instr  = queue_next_CF_commit_entry.instr;

   logic  next_CF_commit_is_jal, next_CF_commit_is_jalr;
   assign next_CF_commit_is_jal  = have_at_least_1_uncommitted_CF_instr && FV_FUNC_instr_is_jal(next_CF_commit_instr);
   assign next_CF_commit_is_jalr = have_at_least_1_uncommitted_CF_instr && FV_FUNC_instr_is_jalr(next_CF_commit_instr);

   logic check_jmp_taken;
   assign check_jmp_taken        = ex_queue_enable && (|commit) && (next_CF_commit_is_jal || next_CF_commit_is_jalr);

`ifdef FV_DUP_BR
   logic  next_CF_commit_is_branch;
   assign next_CF_commit_is_branch = have_at_least_1_uncommitted_CF_instr && FV_FUNC_instr_is_branch(next_CF_commit_instr);

   // =========
   // CF queue
   
   typedef struct {
      logic [`FV_INSTR_WIDTH-1:0]      instr;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] pc;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] next_pc;
      logic 				   next_pc_valid;
      logic [`FV_REG_WIDTH-1:0] 	   rd_value;
      logic 				   br_taken;
      logic 				   is_dup;
      instr_size_t                         instr_size; // could be different than what it is in the EX queue, e.g., could be decompressed before storing here
   } CF_orig_queue_entry_t;

   CF_orig_queue_entry_t CF_orig_queue[`FV_CF_INSTR_QUEUE_DEPTH-1:0];
   CF_orig_queue_entry_t CF_orig_queue_head, CF_orig_queue_tail_d, CF_orig_queue_tailm1;

   logic [`FV_CF_INSTR_QUEUE_POINTER_WIDTH-1:0] CF_orig_head_pointer,     // where committed and processed instructions are deleted
						    CF_orig_tail_pointer,     // where new instructions are inserted
						    CF_orig_tail_pointer_d;   // delayed version of CF_orig_tail_pointer
   
   logic CF_orig_queue_push, CF_orig_queue_pop;

   assign CF_orig_queue_head   = CF_orig_queue[CF_orig_head_pointer];
   assign CF_orig_queue_tail_d = CF_orig_queue[CF_orig_tail_pointer_d];
   assign CF_orig_queue_tailm1 = CF_orig_queue[CF_orig_tail_pointer-1];

   typedef struct {
      logic [`FV_INSTR_WIDTH-1:0]      instr;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] pc;
      logic 				   br_taken;
      instr_size_t                         instr_size; // could be different than what it is in the EX queue, e.g., could be decompressed before storing here
   } CF_dup_entry_t;

   CF_dup_entry_t CF_dup_committed;
   logic CF_dup_committed_valid;
   logic CF_dup_committed_save, CF_dup_committed_clear;
   
   wire no_CF_orig_instr               = (CF_orig_tail_pointer ==  CF_orig_head_pointer);
   wire have_only_1_CF_orig_instr      = (CF_orig_tail_pointer == (CF_orig_head_pointer+1));
   wire have_at_least_2_CF_orig_instrs = !no_CF_orig_instr && !have_only_1_CF_orig_instr;
   
   logic [`FV_INSTR_WIDTH-1:0] CF_orig_head_instr, CF_orig_tail_d_instr, CF_dup_instr;
   assign CF_orig_head_instr   = CF_orig_queue_head.instr;
   assign CF_orig_tail_d_instr = CF_orig_queue_tail_d.instr;
   assign CF_dup_instr         = CF_dup_committed.instr;
   
   assign CF_orig_queue_push     = cf_enable && (|commit) && (next_CF_commit_is_branch || next_CF_commit_is_jal || next_CF_commit_is_jalr) && (!(queue_next_CF_commit_entry.is_dup));
   assign CF_dup_committed_save  = cf_enable && (|commit) && (next_CF_commit_is_branch || next_CF_commit_is_jal || next_CF_commit_is_jalr) && (  queue_next_CF_commit_entry.is_dup);
   assign CF_dup_committed_clear = cf_enable && (|commit) && CF_dup_committed_valid; // save has higher priority than clear (for back-to-back)  Note0: commit[2]?
   assign CF_orig_queue_pop      = CF_dup_committed_clear; // we are done with all checks at this point
   
   // CF_orig_queue tail pointer update
   always @(posedge clk)
     begin
        if (!reset_) begin
           CF_orig_tail_pointer <= {`FV_CF_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
        end else if (CF_orig_queue_push) begin
  	   // Note: complete for 2 commits? no, because the assumption is only one CF_instr commit per cycle
           CF_orig_queue[CF_orig_tail_pointer].instr    <= next_CF_commit_instr;
           CF_orig_queue[CF_orig_tail_pointer].pc       <= queue_next_CF_commit_entry.pc;
           CF_orig_queue[CF_orig_tail_pointer].br_taken <= queue_next_CF_commit_entry.predict_br_taken;
           CF_orig_queue[CF_orig_tail_pointer].is_dup   <= queue_next_CF_commit_entry.is_dup; // Note: any use for this?
           CF_orig_queue[CF_orig_tail_pointer].instr_size <= queue_next_CF_commit_entry.instr_size;
	   
           CF_orig_tail_pointer <= CF_orig_tail_pointer + 1;
	   // Note0: done? if the next instr is also getting committed this cycle, set next_pc and next_pc_valid, too
	   if (commit_extended[next_CF_commit_index + 1]) begin
	      CF_orig_queue[CF_orig_tail_pointer].next_pc       <= queue_next_commit_entry[next_CF_commit_index + 1].pc;
	      CF_orig_queue[CF_orig_tail_pointer].next_pc_valid <= 1'b1;
	   end else begin
              // wait for next commit to update it
              CF_orig_queue[CF_orig_tail_pointer].next_pc_valid <= 1'b0;
	   end
	end // if (CF_orig_queue_push)
	
	// capture the PC of the next committed instruction
	// use the saved PC of the next commit instr to check the next PC of the current instr
	if ((|commit) && (!no_CF_orig_instr) && CF_orig_queue_tailm1.next_pc_valid == 1'b0) begin
	   CF_orig_queue[CF_orig_tail_pointer-1].next_pc       <= queue_next_commit_entry[1].pc;
	   CF_orig_queue[CF_orig_tail_pointer-1].next_pc_valid <= 1'b1;
	end
     end // always @ (posedge clk)

   // CF_orig_queue head pointer update
   always @(posedge clk)
     begin
        if (!reset_) begin
           CF_orig_head_pointer <= {`FV_CF_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
        end else if (CF_orig_queue_pop) begin
	   CF_orig_head_pointer <= CF_orig_head_pointer + 1;
	end
     end
   
   logic CF_orig_queue_push_d, CF_dup_committed_save_d;

   FV_delay_signal #(.DELAY_AMOUNT(`FV_COMMIT_TO_RF_WR_DELAY+1), .MAX_DELAY(`FV_COMMIT_TO_RF_WR_DELAY_MAX), .RESET_VALUE(0)) 
      delay_CF_orig_queue_push(.clk(clk), .reset_(reset_),
		       .in(CF_orig_queue_push), .out(CF_orig_queue_push_d));
   FV_delay_signal #(.DELAY_AMOUNT(`FV_COMMIT_TO_RF_WR_DELAY+1), .MAX_DELAY(`FV_COMMIT_TO_RF_WR_DELAY_MAX), .RESET_VALUE(0)) 
      delay_CF_dup_committed_save(.clk(clk), .reset_(reset_),
		       .in(CF_dup_committed_save), .out(CF_dup_committed_save_d));
   FV_delay_signal #(.DELAY_AMOUNT(`FV_COMMIT_TO_RF_WR_DELAY+1), .MAX_DELAY(`FV_COMMIT_TO_RF_WR_DELAY_MAX), .RESET_VALUE(0), .DATA_WIDTH(`FV_CF_INSTR_QUEUE_POINTER_WIDTH)) 
      delay_CF_orig_tail_pointer(.clk(clk), .reset_(reset_),
		       .in(CF_orig_tail_pointer), .out(CF_orig_tail_pointer_d));
   

   always @(posedge clk)
     begin
	if (CF_orig_queue_push_d) // rd value shows up in ARF a FV_COMMIT_TO_RF_WR_DELAY+1 cycle after intrs is committed
          CF_orig_queue[CF_orig_tail_pointer_d].rd_value <= arf[FV_FUNC_get_instr_rd(CF_orig_tail_d_instr)];
      end   

   // CF_dup instrcution saving
   always @(posedge clk)
     begin
        if (!reset_) begin
	   CF_dup_committed_valid <= 0;
        end else if (CF_dup_committed_save) begin
  	   // Note: compplete for 2 commits
           CF_dup_committed.instr    <= next_CF_commit_instr;
           CF_dup_committed.pc       <= queue_next_CF_commit_entry.pc;
           CF_dup_committed.br_taken <= dut_branch_taken || queue_next_CF_commit_entry.received_kill; // receiving kill this cycle (with commit) or previously
           // wait for next commit to update it
           CF_dup_committed.instr_size <= queue_next_CF_commit_entry.instr_size;
	   CF_dup_committed_valid <= 1;
	end else if (CF_dup_committed_clear)
	   CF_dup_committed_valid <= 0;
     end // always @ (posedge clk)

   logic [`FV_INSTR_ADDR_WIDTH-1:0] JAL_pc_plus_4, JAL_saved_pc;
   logic 				check_JAL_saved_pc;

   always @(*)
   begin
    if (CF_orig_queue_push_d) begin
       JAL_pc_plus_4      =    (CF_orig_queue_tail_d.pc) + CF_orig_queue_tail_d.instr_size;
       JAL_saved_pc       = arf[FV_FUNC_get_instr_rd(CF_orig_tail_d_instr)];
       check_JAL_saved_pc =    (FV_FUNC_instr_is_jal(CF_orig_tail_d_instr) || 
			        FV_FUNC_instr_is_jalr(CF_orig_tail_d_instr)) && 
			       (FV_FUNC_get_instr_rd(CF_orig_tail_d_instr) != 0); // RISC-V specific
    end else if (CF_dup_committed_save_d) begin
       JAL_pc_plus_4      =    (CF_dup_committed.pc) + CF_dup_committed.instr_size;
       JAL_saved_pc       = arf[FV_FUNC_get_instr_rd(CF_dup_instr)];
       check_JAL_saved_pc =    (FV_FUNC_instr_is_jal(CF_dup_instr) ||
			        FV_FUNC_instr_is_jalr(CF_dup_instr)) && 
			       (FV_FUNC_get_instr_rd(CF_dup_instr) != 0); // RISC-V specific
    end else begin
       JAL_pc_plus_4      = '0;
       JAL_saved_pc       = '0;
       check_JAL_saved_pc = 0;
    end
   end

   logic check_br_dup_taken;
   logic check_BR_dest_pc, check_JAL_dest_pc, check_JALR_dest_pc;

   assign check_br_dup_taken       = CF_dup_committed_valid && FV_FUNC_instr_is_branch(CF_dup_instr);
   assign check_BR_dest_pc         = CF_dup_committed_clear && FV_FUNC_instr_is_branch(CF_dup_instr);
   assign check_JAL_dest_pc        = CF_dup_committed_clear && FV_FUNC_instr_is_jal(CF_dup_instr);
   assign check_JALR_dest_pc       = CF_dup_committed_clear && FV_FUNC_instr_is_jalr(CF_dup_instr);
   
   logic CF_orig_taken, CF_dup_taken;
   logic [`FV_INSTR_ADDR_WIDTH-1:0] CF_orig_dest_pc, CF_dup_dest_pc,
					CF_orig_dest_pc_offset, CF_dup_dest_pc_offset;
   assign CF_orig_taken       = CF_orig_queue_head.br_taken;
   assign CF_dup_taken        = CF_dup_committed.br_taken;
   assign CF_orig_dest_pc     = CF_orig_queue_head.next_pc;
   assign CF_dup_dest_pc      = queue_next_CF_commit_entry.pc;

   // subtract the br/jm original instruction size from off set for non-taken case
   assign CF_orig_dest_pc_offset = $signed(CF_orig_dest_pc - CF_orig_queue_head.pc) - 
				   ((FV_FUNC_instr_is_branch(CF_orig_head_instr) && (!CF_orig_taken)) ? CF_orig_queue_head.instr_size : 0);
   
   assign CF_dup_dest_pc_offset  = $signed(CF_dup_dest_pc  - CF_dup_committed.pc) -
				   ((FV_FUNC_instr_is_branch(CF_dup_instr) && (!CF_dup_taken)) ? CF_dup_committed.instr_size : 0);

 `ifdef FV_ENABLE_SC_DEBUG
   // next_pc_valid should be 1 by this time
   FV_SC_DUP_CF_CF_orig_pc_valid_on_dup_clear: assert property (@(posedge clk) CF_dup_committed_clear |-> (CF_orig_queue_head.next_pc_valid == 1));

   FV_SC_DUP_CF_cover_CF_orig_queue_push:    cover property (@(posedge clk) (CF_orig_queue_push_d == 1));
   FV_SC_DUP_CF_cover_CF_dup_committed_save: cover property (@(posedge clk) (CF_dup_committed_save_d == 1));
   
   FV_SC_DUP_CF_br_dup_no_orig_commit: assert property (@(posedge clk) (CF_dup_committed_valid == 1) |-> (no_CF_orig_instr != 1));
 `endif //  `ifdef FV_ENABLE_SC_DEBUG
   
 `ifndef FV_JAL_RD_OR
   // the following checks JAL and JALR
   FV_CF_JAL_check_saved_PC:   assert property (@(posedge clk) (check_JAL_saved_pc == 1) |-> (JAL_pc_plus_4 == JAL_saved_pc));
 `endif
`endif //  `ifdef FV_DUP_BR


`ifdef FV_DUP_BR

   // Note1: commit and RF write_en's do not always line up
   logic CF_instr_committed_rf_wr, CF_instr_committed_rf_wr_predelay;

   assign CF_instr_committed_rf_wr_predelay = (CF_orig_queue_push || CF_dup_committed_save);

   FV_delay_signal #(.DELAY_AMOUNT(`FV_COMMIT_TO_RF_WR_DELAY), .MAX_DELAY(`FV_COMMIT_TO_RF_WR_DELAY_MAX), .RESET_VALUE(0)) 
      delay_CF_instr_committed_rf_wr(.clk(clk), .reset_(reset_),
		       .in(CF_instr_committed_rf_wr_predelay), .out(CF_instr_committed_rf_wr));

 `ifdef FV_JAL_RD_OR
   // Note: rewrite to multi-instr/commit using parameters
   // Note1: separate into 2 overrides depending on matching rd1/2?
   assign fv_override_rf_wdata = CF_instr_committed_rf_wr && (|rf_write_en);

     for (i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
      assign rf_lock[i] = 0;
      assign rf_unlock[i] = 0;
   end
 `else
   assign fv_override_rf_wdata = 0;
   for (i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
// Note: code is for RISC-V RF
      assign rf_lock[i] = CF_instr_committed_rf_wr && rf_write_en[i] &&
			  (rf_write_rd[i] != (`FV_NUM_RD_PAIRS));
      assign rf_unlock[i] = (!rf_lock[i]) && rf_write_en[i];
   end
 `endif // !`ifdef FV_JAL_RD_OR

   for (i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
      assign rf_lock_num[i] = rf_write_rd[i];
   end
`else // !`ifdef FV_DUP_BR
   assign fv_override_rf_wdata = 0;
   for (i=1; i<=`FV_NUM_RF_WR_PORTS; i++) begin
      assign rf_lock[i] = 0;
      assign rf_unlock[i] = 0;
      assign rf_lock_num[i] = '0;
   end
`endif // !`ifdef FV_DUP_BR

endmodule // FV_CORE_EX_cf
