
module FV_CORE_if( // inputs
		       input logic 							       clk, 
		       input logic 							       reset_,
		       input logic 							       dup_enable,
				   
		       input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] instruction_in,
								
		       input logic 							       IF_stall,
		       input logic 							       IF_kill,
		       input logic [`FV_INSTR_ADDR_WIDTH-1:0] 			       IF_pc,
		       input logic [`FV_INSTR_ADDR_WIDTH-1:0] 			       IF_mem_fetch_addr,
		       input logic 							       EX2IF_killed_instr_found,
		       input ex_queue_entry_t                                                  EX2IF_killed_instr,

		       input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			       fv_if_attempt_dup,
		       input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			       fv_if_attempt_dup_sync,
		       input logic 							       fv_if_insert_bubble,
		       input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			       fv_if_predict_br_taken,
								
		       // outputs
                       output logic                                                            IF_instr_req_grant, // to be used if FV_FLOP_INSTR_OUTPUTS and need to stall instr. request
		       output logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			       IF_instr_out_valid,
		       output if_queue_entry_t                                                 IF_instr_out[`FV_IF_MAX_INSTR_PER_CYCLE:1],
		       output logic [`FV_IF_BUS_WIDTH-1:0] 				       IF_instr_bus_out,
		       output logic [`FV_INSTR_ADDR_WIDTH-1:0] 			       IF_instr_pc
		       );

   // outputs from queue
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] instr_out_valid;
   if_queue_entry_t instr_out[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   if_queue_entry_t instr_queue_head[`FV_IF_MAX_INSTR_PER_CYCLE:1];

   // *_next optionally get flopped into *_flopped before getting connecting to *_int
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] instruction_out_valid_next, 
					    instruction_out_valid_int;
   if_queue_entry_t instruction_out_next[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   if_queue_entry_t instruction_out_int[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] IF_pc_next, 
					                                  IF_pc_int;

   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] goto_passthru_mode, in_passthru_mode;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] enable, is_empty, queue_push, queue_pop;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] in_dup_mode;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] dup_stop; // when =1, no more instructions are sent out (valid1/2=0)

   logic fv_if_insert_bubble_int;
`ifdef FV_RND_BUBBLE
   assign fv_if_insert_bubble_int = fv_if_insert_bubble;
`else
   assign fv_if_insert_bubble_int = 0;
`endif

   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_attempt_dup_sync_int;
`ifdef FV_DUP_NO_RND_MIX
   assign fv_if_attempt_dup_sync_int = '0;
`else
   assign fv_if_attempt_dup_sync_int = fv_if_attempt_dup_sync;
`endif
   
   logic no_output_when_kill; // when set, FV module should not send an instruction on the output
`ifdef FV_NO_OUTPUT_WHEN_KILL
   assign no_output_when_kill = IF_kill;
`else
   assign no_output_when_kill = 0;
`endif

   // index zero is used for possible partial instruction left over from the previous cycle
   genvar i;
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : instr
      FV_CORE_IF_gen gen( // inputs
			      .clk(clk),
				  
			      .instr_in(instruction_in[i]),
			      .fv_if_attempt_dup(fv_if_attempt_dup[i]),
			      .fv_if_attempt_dup_sync(fv_if_attempt_dup_sync_int[i]),
			      .fv_if_insert_bubble(fv_if_insert_bubble_int),
			      .fv_if_predict_br_taken(fv_if_predict_br_taken[i]),

			      .instr_queue_head(instr_queue_head[i]),
			      .dup_enable(dup_enable),
			      .enable(enable[i]),
			      .is_empty(is_empty[i]),
			      .in_passthru_mode(in_passthru_mode[i]),
			      .in_dup_mode(in_dup_mode[i]),
			      .no_output_when_kill(no_output_when_kill),
			      .IF_kill(IF_kill),

			      // outputs
			      .instr_out(instr_out[i]),
			      .instr_out_valid(instr_out_valid[i]),

			      .queue_push(queue_push[i]),
			      .queue_pop(queue_pop[i]),
			      .goto_passthru_mode(goto_passthru_mode[i])
			      );
   end // block: instr_gen
   
   FV_CORE_IF_queue instr_queue( // inputs
				     .clk(clk),
				     .reset_(reset_),
				     .stall(IF_stall),
				     .kill(IF_kill),
				     
				     .killed_instr_found(EX2IF_killed_instr_found),
				     .killed_instr(EX2IF_killed_instr),

				     .no_output_when_kill(no_output_when_kill),
				     .instr_out(instr_out),
				     .queue_push(queue_push),
				     .queue_pop(queue_pop),
				     
				     // internal outputs
				     .instr_queue_head(instr_queue_head),
				     .is_empty(is_empty)
				     );

   logic passthru_mode;
   logic goto_passthru_mode_end;

   assign goto_passthru_mode_end = ((!IF_stall && !no_output_when_kill) && goto_passthru_mode[`FV_IF_MAX_INSTR_PER_CYCLE]) || 
				   in_passthru_mode[`FV_IF_MAX_INSTR_PER_CYCLE];
   always @(posedge clk)
     begin
        if (!reset_) begin
	   passthru_mode <= 0;
	end else if (!IF_stall) begin
	   passthru_mode <= goto_passthru_mode_end;
	end
     end

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : passthru
      if (i == 1)
	assign in_passthru_mode[1] = passthru_mode && !IF_kill;
      else
	assign in_passthru_mode[i] =  ((!IF_stall && !no_output_when_kill) && goto_passthru_mode[i-1]) ? 1'b1 : // set
				      in_passthru_mode[i-1];                                                   // hold
	
   end

`ifdef FV_DUP_NO_RND_MIX

   logic in_dup_mode_flopped;
   logic dup_stop_flopped;
   
   logic  send_dup_flush_end, send_dup_sync_end;
   // no need to AND with dup_enable as we are in ifdef only enabled for DUP
   assign send_dup_flush_end = instr_out[`FV_IF_MAX_INSTR_PER_CYCLE].is_dup_flush;
   assign send_dup_sync_end  = instr_out[`FV_IF_MAX_INSTR_PER_CYCLE].is_dup_sync;

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : dup_mode_dup_stop
      if (i == 1) begin
	assign in_dup_mode[1] = in_dup_mode_flopped;
	 assign dup_stop[1]  = dup_stop_flopped;
      end else begin
	assign in_dup_mode[i] =  (instr_out[i-1].is_dup_flush) ? 1'b1 : // set
				 (instr_out[i-1].is_dup_sync)  ? 1'b0 : // reset
				 in_dup_mode[i-1]);                      // hold
	assign dup_stop[i]   =  (instr_out[i-1].is_dup_sync)  ? 1'b1 : // set
				 dup_stop[i-1]);                        // hold
      end
   end
   
   always @(posedge clk)
     begin
	if (!reset_) begin
	   in_dup_mode_flopped <= 0;
	   dup_stop_flopped   <= 0;
	end else if (send_dup_flush_end && !IF_stall) begin
	   in_dup_mode_flopped <= 1;
	end else if (send_dup_sync_end && !IF_stall) begin
	   in_dup_mode_flopped <= 0;
 `ifdef FV_DUP_DO_ONE_SET
	   dup_stop_flopped   <= 1;	   
 `endif
	end	   
     end // always @ (posedge clk)
   
`else // !`ifdef FV_DUP_NO_RND_MIX
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : dup_mode
      assign in_dup_mode[i] = 0; // no used
      assign dup_stop[i] = 0;
   end
`endif // !`ifdef FV_DUP_NO_RND_MIX

   logic  general_enable;
   assign general_enable = reset_ && (!fv_if_insert_bubble_int) && !no_output_when_kill;

   // *_nxt get flopped into * and then optionally get flopped into *_flopped before getting connected to *_int
   logic            partial_instr_valid_nxt,
		    partial_instr_valid, 
		    partial_instr_valid_int;
   if_queue_entry_t partial_instr_nxt, 
                    partial_instr, 
                    partial_instr_int;
   instr_size_t     partial_instr_size, 
                    partial_instr_bytes_remaining_nxt, 
                    partial_instr_bytes_remaining, 
                    partial_instr_bytes_remaining_int;
   integer          partial_instr_num;
   
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:0][`FV_INSTR_ADDR_WIDTH-1:0] instr_width_sum, // values based on input PCs and generated instructions
					                               instr_width_sum_int; // values after optional flopping of outputs
   logic [`FV_INSTR_ADDR_WIDTH-1:0] 			       IF_fetch_offset;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			       instr_gets_output, // instr gets to the output but may be partial 
								       instr_fits_output; // instr fits to the output so no partial
   
   assign partial_instr_size = (partial_instr_valid && (!IF_kill)) ? partial_instr.instr_size : 0;

`ifdef FV_IF_INSTR_BUS_USED
   assign IF_fetch_offset = IF_pc - IF_mem_fetch_addr;
`else
   assign IF_fetch_offset = 0; // can have full set regardless of new fetch PC
`endif
   assign instr_width_sum[0] = ((partial_instr_valid && (!IF_kill)) ? $unsigned(partial_instr_bytes_remaining) : 0) + IF_fetch_offset; // Note: these two terms cannot be non-zero both at the same time, right? add property assert

   always @(posedge clk) begin
      if (!reset_) begin
	 partial_instr_valid           <= 0;
	 partial_instr_bytes_remaining <= 0;
      end else begin
	 if (instr_out_valid[1] && (!IF_stall)) begin
	    partial_instr_valid           <= partial_instr_valid_nxt;
	    partial_instr_bytes_remaining <= partial_instr_bytes_remaining_nxt;
	 end else if (IF_kill) begin
	    partial_instr_valid           <= 0;
	    partial_instr_bytes_remaining <= 0;
	 end
      end
      if ((instr_out_valid[1] && (!IF_stall)) || IF_kill) begin
	 partial_instr <= partial_instr_nxt;
      end
   end   

   always @(*) begin
      partial_instr_valid_nxt = 0;
      partial_instr_num = 0;      
      partial_instr_bytes_remaining_nxt = 0;
      for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	 instr_width_sum[i]   =  instr_width_sum[i-1] + instr_out[i].instr_size;
	 instr_gets_output[i] = (instr_width_sum[i-1] < (`FV_IF_BUS_WIDTH/8)); // FV_IF_BUS_WIDTH is in terms of bits; convert to bytes
	 instr_fits_output[i] = (instr_width_sum[i]  <= (`FV_IF_BUS_WIDTH/8)); // FV_IF_BUS_WIDTH is in terms of bits; convert to bytes
	 enable[i]            = general_enable && instr_gets_output[i] && (!dup_stop[i]);
	 if ((partial_instr_valid_nxt == 0) && instr_out_valid[i] && (instr_gets_output[i] && (!instr_fits_output[i]))) begin
	    partial_instr_valid_nxt = 1;
	    partial_instr_num       = i;
	    partial_instr_bytes_remaining_nxt = instr_width_sum[i] - (`FV_IF_BUS_WIDTH/8);
	 end
      end
   end

   assign partial_instr_nxt = instr_out[partial_instr_num];

   // ==========
   // outputs

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign instruction_out_valid_next[i] = instr_out_valid[i] && instr_gets_output[i];
      // IF_gen should pass through instr_in if dup_enable==0 and set other fields to 0 except for size that is based in instr_in
      assign instruction_out_next[i]       = instr_out[i];

      if (i==1)
	assign IF_pc_next[i] = IF_pc + ((partial_instr_valid && (!IF_kill)) ? partial_instr_bytes_remaining : 0);
      else
	assign IF_pc_next[i] = IF_pc_next[i-1] + instr_out[i-1].instr_size;
   end
 
`ifdef FV_FLOP_INSTR_OUTPUTS
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] instruction_out_valid_flopped;
   if_queue_entry_t                      instruction_out_flopped[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] IF_pc_flopped;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:0][`FV_INSTR_ADDR_WIDTH-1:0] instr_width_sum_flopped;

   logic            partial_instr_valid_flopped;
   if_queue_entry_t partial_instr_flopped;
   instr_size_t     partial_instr_bytes_remaining_flopped;
   
   if_queue_entry_t                      instruction_out_reset;

   assign instruction_out_reset.instr            = `FV_INSTR_NOP;
   assign instruction_out_reset.instr_size       = 4; // Note: change to a define?
   assign instruction_out_reset.is_dup           = 0;
   assign instruction_out_reset.is_dup_sync     = 0;
   assign instruction_out_reset.is_dup_flush    = 0;
   assign instruction_out_reset.predict_br_taken = 0;
   
   always @(posedge clk) 
     begin
	for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	   if (!reset_) begin
	      instruction_out_valid_flopped[i] <= 1'b0;
	      instruction_out_flopped[i]       <= instruction_out_reset;
	      
	   end else begin
	      if (!IF_stall) begin
		 instruction_out_valid_flopped[i] <= instruction_out_valid_next[i];
		 instruction_out_flopped[i]       <= instruction_out_next[i];
	      end
	   end // else: !if(!reset_)
	   if (!IF_stall) begin
	      IF_pc_flopped[i] <= IF_pc_next[i];
	   end
	end
	for (int i=0; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	   if (!reset_) begin
	      instr_width_sum_flopped[i] <= 0;
	   end else begin
	      if (!IF_stall) begin
		 instr_width_sum_flopped[i] <= instr_width_sum[i];
	      end
	   end
	end
	if (!reset_)
	  partial_instr_valid_flopped <= 0;
	else
	  if (!IF_stall) begin
	     partial_instr_valid_flopped <= (partial_instr_valid && (!IF_kill));
	  end

	if (!IF_stall) begin
	   partial_instr_flopped                 <= partial_instr;
	   partial_instr_bytes_remaining_flopped <= partial_instr_bytes_remaining;
	end
     end

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign instruction_out_valid_int[i] = instruction_out_valid_flopped[i] && (!no_output_when_kill);
      assign instruction_out_int[i]       = instruction_out_flopped[i];
      assign IF_pc_int[i]                 = IF_pc_flopped[i];
   end
   for (i=0; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign instr_width_sum_int[i]       = instr_width_sum_flopped[i];
   end

   assign partial_instr_valid_int           = partial_instr_valid_flopped && (!no_output_when_kill);
   assign partial_instr_int                 = partial_instr_flopped;
   assign partial_instr_bytes_remaining_int = partial_instr_bytes_remaining_flopped;
   
`else // !`ifdef FV_FLOP_INSTR_OUTPUTS
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign instruction_out_valid_int[i] = instruction_out_valid_next[i]; // already has "&& (!no_output_when_kill)" through general_enable 
      assign instruction_out_int[i]       = instruction_out_next[i];
      assign IF_pc_int[i]                 = IF_pc_next[i];
   end
   for (i=0; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign instr_width_sum_int[i]       = instr_width_sum[i];
   end

   assign partial_instr_valid_int           = (partial_instr_valid && (!IF_kill));
   assign partial_instr_int                 = partial_instr;
   assign partial_instr_bytes_remaining_int = partial_instr_bytes_remaining;

`endif // !`ifdef FV_FLOP_INSTR_OUTPUTS

   assign IF_instr_req_grant = instruction_out_valid_next[1]; // if there is a bubble, this can be used to stall the request
   
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_IF_BUS_WIDTH-1:0] IF_instr_bus_out_shift;

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign IF_instr_out_valid[i]     = instruction_out_valid_int[i];
      assign IF_instr_out[i]           = instruction_out_int[i];
      assign IF_instr_bus_out_shift[i] = instruction_out_int[i].instr << (instr_width_sum_int[i-1] * 8);
   end

   always @(*) begin
      IF_instr_bus_out = partial_instr_valid_int ? (partial_instr_int.instr >> ((partial_instr_int.instr_size - partial_instr_bytes_remaining_int)*8)) : 0;
      for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	 IF_instr_bus_out = IF_instr_bus_out | IF_instr_bus_out_shift[i];
      end
   end
   assign IF_instr_pc                   = IF_pc_int[1];

   // ==========
   // assertions
   
   // =======================
   // assumptions/constraints

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
`ifdef FV_ENABLE_SC_DEBUG
      FV_reset_instr_in:
`else
      FV_if_con1:
`endif
        assume property (@(posedge clk) ((!reset_) |-> (instruction_in[i]        == `FV_INSTR_NOP)));
   end

`ifdef FV_ENABLE_SC_DEBUG
   FV_reset_fv_if_attempt_dup:       
`else
   FV_if_con2:
`endif
     assume property (@(posedge clk) ((!reset_) |-> (fv_if_attempt_dup      == 0)));

`ifdef FV_ENABLE_SC_DEBUG
   FV_reset_fv_if_insert_bubble:      
`else
   FV_if_con3:
`endif
     assume property (@(posedge clk) ((!reset_) |-> (fv_if_insert_bubble     == 0)));

`ifdef FV_ENABLE_SC_DEBUG
   FV_reset_fv_if_attempt_dup_sync:  
`else
   FV_if_con4:
`endif
     assume property (@(posedge clk) ((!reset_) |-> (fv_if_attempt_dup_sync == 0)));

`ifdef FV_DUP_BR
 `ifdef FV_ENABLE_SC_DEBUG
   FV_reset_fv_if_predict_br_taken:   
 `else
   FV_if_con5:
 `endif
     assume property (@(posedge clk) ((!reset_) |-> (fv_if_predict_br_taken  == 0)));
`endif

`ifdef FV_HOLD_OUTPUT_UNDER_STALL
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
 `ifdef FV_ENABLE_SC_DEBUG
      FV_hold_instr_in:               
 `else
      FV_if_con6:
 `endif
	assume property (@(posedge clk) (IF_stall     |=> (instruction_in[i]        == $past(instruction_in[i]))));
   end

 `ifdef FV_ENABLE_SC_DEBUG
   FV_hold_fv_if_attempt_dup:       
 `else
   FV_if_con7:
 `endif
     assume property (@(posedge clk) (IF_stall     |=> (fv_if_attempt_dup      == $past(fv_if_attempt_dup))));

 `ifdef FV_ENABLE_SC_DEBUG
   FV_hold_fv_if_insert_bubble:      
 `else
   FV_if_con8:
 `endif
     assume property (@(posedge clk) (IF_stall     |=> (fv_if_insert_bubble     == $past(fv_if_insert_bubble))));

 `ifdef FV_ENABLE_SC_DEBUG
   FV_hold_fv_if_attempt_dup_sync:  
 `else
   FV_if_con9:
 `endif
     assume property (@(posedge clk) (IF_stall     |=> (fv_if_attempt_dup_sync == $past(fv_if_attempt_dup_sync))));

 `ifdef FV_DUP_BR
  `ifdef FV_ENABLE_SC_DEBUG
   FV_hold_fv_if_predict_br_taken:   
  `else
   FV_if_con10:
  `endif
     assume property (@(posedge clk) (IF_stall     |=> (fv_if_predict_br_taken  == $past(fv_if_predict_br_taken))));
 `endif
`endif
    
endmodule // FV_CORE_if

