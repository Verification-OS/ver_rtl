
module FV_CORE_IF_gen ( // inputs from DUT
			    input logic 			  clk, 

			    // inputs from BMC
			    input logic [`FV_INSTR_WIDTH-1:0] instr_in, // assumption: input instructions are always valid (ready)
			    input logic 			  fv_if_attempt_dup, // try inserting a duplicate instruction this clock
			    input logic 			  fv_if_attempt_dup_sync, // try randomly sending NOP_SYNC
			    input logic 			  fv_if_insert_bubble, // insert a random bubble
			    input logic 			  fv_if_predict_br_taken, // predicts whether branch is taken or not taken (1 if taken)

			    // internal inputs
			    input 				  if_queue_entry_t instr_queue_head,
			    input logic 			  dup_enable,
			    input logic 			  enable,
			    input logic 			  is_empty,
			    input logic 			  in_passthru_mode,
			    input logic 			  in_dup_mode,
			    input logic 			  IF_kill, 
			    input logic 			  no_output_when_kill, 
								  
			    // outputs
			    output 				  if_queue_entry_t instr_out,
			    output logic 			  instr_out_valid,

			    output logic 			  queue_push,
			    output logic 			  queue_pop,
			    output logic 			  goto_passthru_mode
			  );

   FV_CORE_IF_instr_constraint instr_constraint(.clk(clk),
						    .instruction(instr_in));


   wire 		    instr_in_is_nop;
   wire 		    send_dup_sync, send_dup_flush, send_nop;
   wire 		    instr_in_is_CF_nodup;
   wire 		    instr_send_CF_nodup;
   wire 		    instr_in_causes_flush;
   wire 		    instr_send_causes_flush;
   wire 		    instr_queue_head_causes_flush;
 		    
   assign instr_in_is_nop               = FV_FUNC_is_nop(instr_in);
   assign instr_in_is_CF_nodup          = FV_FUNC_instr_is_CF_nodup(instr_in);
   assign instr_in_causes_flush         = FV_FUNC_instr_causes_flush(instr_in);
   assign instr_send_causes_flush       = instr_in_causes_flush && queue_push;
   assign instr_queue_head_causes_flush = FV_FUNC_instr_causes_flush(instr_queue_head.instr);
   
`ifdef FV_DUP_BR
   wire  instr_in_is_CF_dup_taken,  
	 instr_queue_head_is_CF_dup_taken;
   wire  instr_send_CF_dup_taken;

   assign instr_in_is_CF_dup_taken         = FV_FUNC_instr_is_CF_dup_taken(instr_in, fv_if_predict_br_taken);
   assign instr_queue_head_is_CF_dup_taken = FV_FUNC_instr_is_CF_dup_taken(instr_queue_head.instr, instr_queue_head.predict_br_taken);
   
   assign instr_send_CF_dup_taken = instr_in_is_CF_dup_taken && queue_push;
   
   assign goto_passthru_mode = queue_pop ? (instr_queue_head_is_CF_dup_taken ||
					    instr_queue_head_causes_flush) : 
			                   (instr_send_CF_nodup || 
					    instr_send_CF_dup_taken ||
					    instr_send_causes_flush);

`else // !`ifdef FV_DUP_BR
   assign goto_passthru_mode = queue_pop ? instr_queue_head_causes_flush: 
					   instr_send_causes_flush; // Do we need to add instr_send_CF_nodup? No, because in no DUP_BR, conditional branches are among CF_no_dup and may not be taken so what came after that branch should be DUP'd (no passthru)
`endif //  `ifdef FV_DUP_BR
   
   wire instr_push = (!instr_in_is_nop) && (!instr_in_is_CF_nodup);

   logic can_send_instr;
   assign can_send_instr = enable;

   assign queue_push = can_send_instr && dup_enable &&
		       ((!fv_if_attempt_dup) || is_empty) && 
		       (!(fv_if_attempt_dup_sync && is_empty)) &&
`ifdef FV_DUP_NO_RND_MIX
		       (!in_dup_mode) &&
`endif
		       (instr_push) &&
		       (!in_passthru_mode) &&
		       1'b1;

   // NOTE: No pushing and popping at the same time (fv_if_attempt_dup is the guard) 
   assign queue_pop  = can_send_instr && dup_enable &&
		       ( fv_if_attempt_dup && (!is_empty)) &&
`ifdef FV_DUP_NO_RND_MIX
		       ( in_dup_mode) &&
`endif		       
		       (!in_passthru_mode) &&
		       1'b1;

   
   // when queue is empty and attempt_dup is 1, randomly send dup_sync (if fv_if_attempt_dup_sync==1)
   // Note: OK to send_dup_sync while in_passthru_mode, right?
   assign send_dup_sync    = can_send_instr && dup_enable &&
			       (!in_passthru_mode) &&
`ifdef FV_DUP_NO_RND_MIX
			       in_dup_mode && is_empty;
`else
			       fv_if_attempt_dup_sync && is_empty;
`endif

`ifdef FV_DUP_NO_RND_MIX

   assign send_dup_flush = can_send_instr && dup_enable && (!in_dup_mode) &&
			     (!in_passthru_mode) &&
			     fv_if_attempt_dup && (!is_empty);
   
			     
`else // !`ifdef FV_DUP_NO_RND_MIX
   
   assign send_dup_flush = 0;
   
`endif // !`ifdef FV_DUP_NO_RND_MIX

   assign send_nop         = can_send_instr && dup_enable &&
			     (!in_passthru_mode) &&
			     (!is_empty) &&
			     (
`ifdef FV_DUP_NO_RND_MIX
			      // send_nop creates NOP during queue_pop when (!fv_if_attempt_dup)
			      (in_dup_mode && (!fv_if_attempt_dup)) ||
`endif
`ifdef FV_IF_INSTR_BUS_USED
			      // Note: same for when `FV_IF_MAX_INSTR_PER_CYCLE > 1
			      // cannot send bubbles in middle of a bus, so send NOP if cannot sent the CF_nodup
                              ((!queue_pop) && instr_in_is_CF_nodup) ||
`endif
			      1'b0);
   
   assign instr_send_CF_nodup = can_send_instr && dup_enable &&
                                is_empty && instr_in_is_CF_nodup && (!fv_if_attempt_dup_sync);
   
   assign instr_out_valid =  dup_enable ?
			    (can_send_instr &&
			     (queue_push         || // original instruction (non-NOP)
			      queue_pop          || // duplicate instruction
			      instr_send_CF_nodup ||
			      send_dup_sync    ||
			      send_dup_flush   ||
			      send_nop           ||
			      in_passthru_mode   ||
			      instr_in_is_nop) ? 1'b1 : 
`ifdef FV_NO_BUBBLE
                          (can_send_instr && (!no_output_when_kill))) : // always send at least a NOP unless FV_NO_OUTPUT_WHEN_KILL 
`else
                             1'b0) :
`endif
`ifdef FV_NO_OUTPUT_WHEN_KILL
			    can_send_instr && (!IF_kill);
`else
                            can_send_instr;
`endif

   logic [`FV_INSTR_WIDTH-1:0] instr_out_raw, instr_out_dup;
   
   assign instr_out_raw = dup_enable ?
			  ((queue_push        || 
			   in_passthru_mode   ||
			   instr_send_CF_nodup)       ? instr_in :
 		          queue_pop                   ? instr_queue_head.instr :
			  send_dup_sync             ? `FV_INSTR_NOP_SYNC :
			  send_dup_flush            ? `FV_INSTR_NOP_FLUSH :
			  send_nop                    ? `FV_INSTR_NOP :
			  `FV_INSTR_NOP) :
			  instr_in; // passthru input if dup_enable==0

   FV_CORE_IF_dup dup_instr(.clk(clk),
                                .instr_in(instr_out_raw),
				.instr_out(instr_out_dup));
   assign instr_send_dup = queue_pop;

   assign instr_out.instr         = instr_send_dup  ? instr_out_dup : instr_out_raw;
   // use output of above statement for the following as dup instr size may be different than orig
   assign instr_out.instr_size    = instr_out_valid ? FV_FUNC_instr_size(instr_out.instr) : 0;
   assign instr_out.is_dup        = instr_send_dup;
   assign instr_out.is_dup_sync  = instr_out_valid && send_dup_sync;  // validate here so don't have to worry about it elsewhere
   assign instr_out.is_dup_flush = instr_out_valid && send_dup_flush;
`ifdef FV_DUP_BR
   assign instr_out.predict_br_taken = instr_send_dup ? instr_queue_head.predict_br_taken : fv_if_predict_br_taken;
`else
   assign instr_out.predict_br_taken = 0;
`endif   

`ifdef FV_ENABLE_SC_DEBUG
   // ==========
   // assertions

   // Note: add assertions (not to be violated) on the following
   // queue_push, queue_pop, and send_orig_dup_pair are mutually exclusive
   FV_SC_DUP_instr_Q_send_1hot: assert property (@(posedge clk) $onehot0({queue_push,
									     queue_pop,
									     instr_send_CF_nodup,
// having instr_in_is_nop in this mix is just to test that the assert works (fails when instr_in_is_nop is included)
//								             instr_in_is_nop,
									     send_dup_sync,
									     send_dup_flush,
									     send_nop
									     }));
   
 `ifdef FV_DUP_BR
   FV_SC_DUP_CF_in_passthru_no_dup: assert property (@(posedge clk) (in_passthru_mode) |-> ((queue_push || 
												    queue_pop  ||
												    send_dup_sync ||
												    send_dup_flush) == 0));
 `endif

   // ================
   // cover properties
   
 `ifdef FV_DUP_NO_RND_MIX
   FV_SC_cover_in_dup_mode_and_send_nop: cover property (@(posedge clk) (in_dup_mode && send_nop));

   FV_SC_cover_in_dup_mode_and_passthru: cover property (@(posedge clk) (in_dup_mode && in_passthru_mode));
    
  `ifndef FV_ENABLE_CMT
   FV_SC_cover_in_dup_mode_and_bubble:   cover property (@(posedge clk) (in_dup_mode && fv_if_insert_bubble));
  `endif

 `endif //  `ifdef FV_DUP_NO_RND_MIX
`endif //  `ifdef FV_ENABLE_SC_DEBUG

endmodule // FV_CORE_IF_gen


