
module FV_prop(
		   input logic 							  clk,
		   input logic 							  reset_,
   

		   input logic 							  EX_kill,
		   input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 		  commit,
		   input logic 							  dut_branch_taken,
		   input logic 							  dut_jump_taken,
		   input prop_signals_t                                           ps
		   );

   genvar 		 i;

`ifdef FV_ENABLE_DUP
   // per-pair dup_ready for more checks along the cycles
   for (i = 0; i < (`FV_NUM_RF_REGS/2); i++) begin : FV_DUP_halves_arf1
      if (i == 0)
  `ifdef FV_DUP_PAIR_R0
        prop: assert property (@(posedge clk) (ps.fv_dup_ready_1) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
  `else
     ;
  `endif
      else if (i == 1)
  `ifdef FV_DUP_PAIR_R1
        prop: assert property (@(posedge clk) (ps.fv_dup_ready_1) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
  `else
     ;
  `endif
      else
        prop: assert property (@(posedge clk) (ps.fv_dup_ready_1) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
	  end

   for (i = 0; i < (`FV_NUM_RF_REGS/2); i++) begin : FV_DUP_pairs_arf1
      if (i == 0)
  `ifdef FV_DUP_PAIR_R0
        prop: assert property (@(posedge clk) (ps.fv_dup_ready_pairs_1[i]) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
  `else
     ;
  `endif
      else if (i == 1)
  `ifdef FV_DUP_PAIR_R1
        prop: assert property (@(posedge clk) (ps.fv_dup_ready_pairs_1[i]) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
  `else
     ;
  `endif
      else
	prop: assert property (@(posedge clk) (ps.fv_dup_ready_pairs_1[i]) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
	  end

  `ifndef FV_NO_DUP_SYNC_READY
   for (i = 0; i < (`FV_NUM_RD_PAIRS);  i++) begin : FV_DUP_sync_arf1
      if (i == 0)
   `ifdef FV_DUP_PAIR_R0
        prop: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
   `else
      ;
   `endif
      else if (i == 1)
   `ifdef FV_DUP_PAIR_R1
        prop: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
   `else
      ;
   `endif
      else
	prop: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.arf1[FV_FUNC_pairs_orig_reg(i)] == ps.arf1[FV_FUNC_pairs_dup_reg(i)]));
	  end
   FV_DUP_sync_ready: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.fv_dup_ready_1));
  `endif //  `ifndef FV_NO_DUP_SYNC_READY
   
  `ifdef FV_RF2_ENABLE
   for (i = 0; i < (`FV_NUM_RF2_REGS/2); i++) begin : FV_DUP_halves_arf2
      prop: assert property (@(posedge clk) (ps.fv_dup_ready_2)          |-> (ps.arf2[FV_FUNC_pairs_orig_reg(i)] == ps.arf2[FV_FUNC_pairs_dup_reg(i)]));
   end

   for (i = 0; i < (`FV_NUM_RF2_REGS/2); i++) begin : FV_DUP_pairs_arf2
      prop: assert property (@(posedge clk) (ps.fv_dup_ready_pairs_2[i]) |-> (ps.arf2[FV_FUNC_pairs_orig_reg(i)] == ps.arf2[FV_FUNC_pairs_dup_reg(i)]));
   end

  `ifndef FV_NO_DUP_SYNC_READY
   for (i = 0; i < (`FV_NUM_RF2_PAIRS);  i++) begin : FV_DUP_sync_arf2
      prop: assert property (@(posedge clk) (ps.fv_dup_sync_ready)     |-> (ps.arf2[FV_FUNC_pairs_orig_reg(i)] == ps.arf2[FV_FUNC_pairs_dup_reg(i)]));
      end
   FV_DUP_sync_ready: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.fv_dup_ready_2));

  `endif //  `ifndef FV_NO_DUP_SYNC_READY
 `endif //  `ifdef FV_RF2_ENABLE
   
  `ifdef FV_RF3_ENABLE
   for (i = 0; i < (`FV_NUM_RF3_REGS/2); i++) begin : FV_DUP_halves_arf3
      prop: assert property (@(posedge clk) (ps.fv_dup_ready_3)          |-> (ps.arf3[FV_FUNC_pairs_orig_reg(i)] == ps.arf3[FV_FUNC_pairs_dup_reg(i)]));
   end

   for (i = 0; i < (`FV_NUM_RF3_REGS/2); i++) begin : FV_DUP_pairs_arf3
      prop: assert property (@(posedge clk) (ps.fv_dup_ready_pairs_3[i]) |-> (ps.arf3[FV_FUNC_pairs_orig_reg(i)] == ps.arf3[FV_FUNC_pairs_dup_reg(i)]));
   end

  `ifndef FV_NO_DUP_SYNC_READY
   for (i = 0; i < (`FV_NUM_RF3_PAIRS);  i++) begin : FV_DUP_sync_arf3
      prop: assert property (@(posedge clk) (ps.fv_dup_sync_ready)     |-> (ps.arf3[FV_FUNC_pairs_orig_reg(i)] == ps.arf3[FV_FUNC_pairs_dup_reg(i)]));
      end
   FV_DUP_sync_ready: assert property (@(posedge clk) (ps.fv_dup_sync_ready) |-> (ps.fv_dup_ready_3));

  `endif //  `ifndef FV_NO_DUP_SYNC_READY
 `endif //  `ifdef FV_RF3_ENABLE
   
`endif //  `ifdef FV_ENABLE_DUP
   

`ifdef FV_ENABLE_CF
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] instr_next_pc_is_correct;
   for (i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin : FV_CF

 `ifdef FV_ENABLE_SI
      assign instr_next_pc_is_correct[i] = (ps.instr_correct_next_pc1[i] == ps.instr_committed_next_pc[i]);
 `else
      assign instr_next_pc_is_correct[i] = (ps.instr_correct_next_pc1[i] == ps.instr_committed_next_pc[i]) || (ps.instr_correct_next_pc2[i] == ps.instr_committed_next_pc[i]) || ps.instr_is_exempt[i];
 `endif  

      prop: assert property (@(posedge clk) (ps.cf_check[i] == 1) |-> (instr_next_pc_is_correct[i] == 1));

   end

 `ifdef FV_DUP_BR
   // the following is pairwise (orig/dup) check
   FV_DUP_CF_check_br_dup_taken: assert property (@(posedge clk) (ps.check_br_dup_taken) |-> (ps.CF_orig_taken == ps.CF_dup_taken));
   FV_DUP_CF_check_dest_PC:      assert property (@(posedge clk) (ps.check_BR_dest_pc || ps.check_JAL_dest_pc) |-> (ps.CF_orig_dest_pc_offset == ps.CF_dup_dest_pc_offset));
   FV_DUP_CF_check_JALR_dest_PC: assert property (@(posedge clk) (ps.check_JALR_dest_pc) |-> (ps.CF_orig_dest_pc == ps.CF_dup_dest_pc));
 `endif

`endif //  `ifdef FV_ENABLE_CF
 
`ifdef FV_ENABLE_EX_QUEUE
   // the following is individual instr check, not pairwise
   FV_EXQ_check_kill_found: assert property (@(posedge clk) (EX_kill == 1) |-> (ps.killed_instr_found == 1));
   FV_EXQ_check_jmp_taken: assert property (@(posedge clk) (ps.check_jmp_taken) |-> (dut_jump_taken == 1));
   
   // DUT hook-up checks that could catch DUT bugs, too
   for (i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin : FV_EXQ_check_commit
      not_empty:              assert property (@(posedge clk) (commit[i]) |-> (!ps.ex_queue_is_empty[i]));
      some_uncommitted:       assert property (@(posedge clk) (commit[i]) |-> (!ps.no_uncommitted_instr[i]));
      expected_kill_received: assert property (@(posedge clk) (ps.check_committed_instr[i]) |-> (!ps.expected_kill[i] || ps.received_kill[i])); // if expected_kill==1 then kill_received==1
   end

   FV_EXQ_check_queue_not_full: assert property (@(posedge clk) (!ps.ex_queue_is_full));
    
`endif //  `ifdef FV_ENABLE_EX_QUEUE
   

`ifdef FV_ENABLE_CMT

   FV_CMT: assert property (@(posedge clk) (ps.fv_clock_counter_ns <= ((ps.fv_num_committed_instr * `FV_CMT_CHECK_MAX_LATENCY) + `FV_CMT_CHECK_WARMUP_COUNT)));

`endif //  `ifdef FV_ENABLE_CMT

`ifdef FV_ENABLE_SI
   FV_PROP_si si(.clk(clk), 
		     .ps(ps.si_ps)
		     );
`endif

endmodule // FV_prop

