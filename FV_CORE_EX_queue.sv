
module FV_CORE_EX_queue( // inputs
			     input logic 								 clk,
			     input logic 								 reset_,

			     input logic 								 ex_queue_enable,
`ifdef FV_ENABLE_SI
			     input logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] 		 arf,
`endif   
			     // instruction execution related signals
			     input if_queue_entry_t                                                      IF2EX_instr_in[`FV_IF_MAX_INSTR_PER_CYCLE:1],
			     input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 				 IF2EX_instr_in_valid,
			     input logic [`FV_INSTR_ADDR_WIDTH-1:0] 				 IF2EX_pc,
			     input logic 								 IF2EX_stall,
			     input logic 								 IF2EX_kill,

			     input logic 								 EX_kill,
			     output logic 								 EX2IF_killed_instr_found,
		             output ex_queue_entry_t                                                     EX2IF_killed_instr,

			     input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				 commit,
			     input logic 								 dut_branch_taken,
			     input logic 								 dut_jump_taken,

			     // outputs
			     output 									 ex_queue_entry_t queue_head[`FV_MAX_COMMIT_PER_CYCLE:1],
			     output 									 ex_queue_entry_t queue_next_commit_entry[`FV_MAX_COMMIT_PER_CYCLE:1],
			     output logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				 have_at_least_2_committed_instrs,
			     output logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				 have_at_least_1_uncommitted_instrs,
			     output logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_committed_next_pc,

			     input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				 check_committed_instr // for updating EX_queue head_pointer
			     );

   genvar i;

   ex_queue_entry_t instr_queue[`FV_EX_INSTR_QUEUE_DEPTH-1:0];

   logic [`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] head_pointer_flopped,        // where committed and processed instructions are deleted
						    next_commit_pointer_flopped, // where the next to-be-committed instruction is
						    tail_pointer_flopped;        // where new instructions are inserted

   logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] head_pointer,
					                                            next_commit_pointer;

   logic [`FV_MAX_COMMIT_PER_CYCLE:0][`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] head_pointer_inc,            // increment amount each clk
					                                            next_commit_pointer_inc;     // increment amount each clk
					 
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] 					    is_empty,
										    no_uncommitted_instr;
   
   logic 				  is_full;
   logic 				  queue_push, queue_pop, update_next_commit_pointer;

   // NOTE: assumption is that instruction commit is in-order and commit[i] give the number of commits/clk
   // NOTE2: all these assume no queue overflow and pointer wrap-around (Q large enough)
   for (i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin
      assign head_pointer[i]            = head_pointer_flopped        + i - 1;
      assign next_commit_pointer[i]     = next_commit_pointer_flopped + i - 1;
      assign queue_head[i]              = instr_queue[head_pointer[i]];
      assign queue_next_commit_entry[i] = instr_queue[next_commit_pointer[i]];
      if (i==1) begin
	 assign is_empty[i]             = (head_pointer_flopped        == tail_pointer_flopped);
	 assign no_uncommitted_instr[i] = (next_commit_pointer_flopped == tail_pointer_flopped);
      end else begin
	 assign is_empty[i]             = is_empty[i-1]             || (head_pointer[i]        == tail_pointer_flopped);
	 assign no_uncommitted_instr[i] = no_uncommitted_instr[i-1] || (next_commit_pointer[i] == tail_pointer_flopped);
      end

      assign have_at_least_2_committed_instrs[i]   = (next_commit_pointer_flopped >= (head_pointer[i] + 2));
      assign have_at_least_1_uncommitted_instrs[i] = (next_commit_pointer[i]      <   tail_pointer_flopped);
      assign instr_committed_next_pc[i]            = instr_queue[head_pointer[i] + 1].pc;
   end

// ===========================   
// Note: add asserts
   
   // should never have instr_valid1 and is_full (increase CF queue depth)
   assign is_full = ((tail_pointer_flopped + 1) == head_pointer_flopped);

   // =============
   // finding the killed instruction (assuming 1 kill each cycle)

   logic found_flag;
   logic [`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] found_pointer;

   logic 					    found;
   ex_queue_entry_t                                 queue_search;

   logic [`FV_EX_INSTR_QUEUE_DEPTH-1:0] 	    valid_mask, uncommitted_mask, search_mask, received_kill_mask, expects_kill_mask, is_branch_mask;
   
   always @(*)
     begin
	for (int i=0; i<`FV_EX_INSTR_QUEUE_DEPTH; i++) begin
	   if ((head_pointer_flopped<=i) && (i<tail_pointer_flopped))
	     valid_mask[i] = 1;
	   else
	     valid_mask[i] = 0;
	   
	   if ((next_commit_pointer_flopped<=i) && (i<tail_pointer_flopped))
	     uncommitted_mask[i] = 1;
	   else
	     uncommitted_mask[i] = 0;

	   queue_search = instr_queue[i];
	   
	   expects_kill_mask[i]  = queue_search.expects_kill;
	   received_kill_mask[i] = queue_search.received_kill;
	   is_branch_mask[i]     = queue_search.is_branch;
	end // for (int i=0; i<`FV_EX_INSTR_QUEUE_DEPTH; i++)
	
	search_mask = valid_mask & 
`ifdef FV_DUP_BR
		      expects_kill_mask &
`else
		      (dut_branch_taken ? (uncommitted_mask & is_branch_mask) : expects_kill_mask) & 
`endif
		      (~received_kill_mask);

	found = 0;
	found_pointer = 0;
	for (int i=0; i<`FV_EX_INSTR_QUEUE_DEPTH; i++)
	  if (search_mask[i] == 1)
	    if (found == 0) begin
	       found = 1;
	       found_pointer = i;
	    end
     end // always @ (*)

   assign found_flag = found; // found first uncommitted CF instr.
   assign EX2IF_killed_instr_found = found_flag;
   assign EX2IF_killed_instr       = instr_queue[found_pointer];
   
   // in some DUTs, some instructions (e.g., ECALL) generates two kills in the course of its execution
   // so the second time around, the following won't hold and we cannot have this in general unless we create an exception
   // e.g., okay if last committed is ECALL
   // for now, exclude enable FV_EXCLUDE_ECALL_EBREAK define for these DUTs

`ifdef FV_DUP_BR
   assign queue_push                 = ex_queue_enable && (!IF2EX_stall) && (| IF2EX_instr_in_valid) && (!(IF2EX_kill && found_flag)); // kill only if expects_kill
`else
   assign queue_push                 = ex_queue_enable && (!IF2EX_stall) && (| IF2EX_instr_in_valid) && (!IF2EX_kill);
`endif
   
   assign update_next_commit_pointer = ex_queue_enable && (| commit);

   assign queue_pop                  = ex_queue_enable && (| check_committed_instr);

   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] push_pointer;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:0][`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] tail_pointer_inc;
   logic [`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] tail_pointer_next;

   assign tail_pointer_inc[0] = 0; 
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign tail_pointer_inc[i] = IF2EX_instr_in_valid[i] + tail_pointer_inc[i-1];
      assign push_pointer[i]     = tail_pointer_flopped    + tail_pointer_inc[i-1];
   end
   
   assign tail_pointer_next = (IF2EX_kill && found_flag) ?
			      (found_pointer + 1) :
			      queue_push ? (tail_pointer_flopped + tail_pointer_inc[`FV_IF_MAX_INSTR_PER_CYCLE]) : tail_pointer_flopped;
   
   // queue tail_pointer_flopped update
   always @(posedge clk)
     begin
        if (!reset_)
          tail_pointer_flopped <= {`FV_EX_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
	else
	  tail_pointer_flopped <= tail_pointer_next;
     end // always @ (posedge clk)

   // =============
   // extract the RF values for si-FV
`ifdef FV_ENABLE_SI
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_REG_WIDTH-1:0] rs1_value, rs2_value;

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign rs1_value[i] = arf[FV_FUNC_get_instr_rs1(IF2EX_instr_in[i].instr)];
      assign rs2_value[i] = arf[FV_FUNC_get_instr_rs2(IF2EX_instr_in[i].instr)];
   end
`endif

   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] IF2EX_pc_int;
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      if (i == 1)
	assign IF2EX_pc_int[1] = IF2EX_pc;
      else
	assign IF2EX_pc_int[i] = IF2EX_pc_int[i-1] + IF2EX_instr_in[i-1].instr_size;
   end
   
   // queue push
   // simultaneous push and kill taken into account (Note0, double-check)
   always @(posedge clk)
     begin
	if (queue_push) begin
	   for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	      if (IF2EX_instr_in_valid[i]) begin
                 instr_queue[push_pointer[i]].instr            <= IF2EX_instr_in[i].instr;
                 instr_queue[push_pointer[i]].pc               <= IF2EX_pc_int[i];
                 instr_queue[push_pointer[i]].instr_size       <= IF2EX_instr_in[i].instr_size; // could be different than what it is in the EX queue, e.g., could be decompressed before storing here
`ifdef FV_ENABLE_SI
                 instr_queue[push_pointer[i]].rs1_value        <= rs1_value[i];
                 instr_queue[push_pointer[i]].rs2_value        <= rs2_value[i];
`endif
		 instr_queue[push_pointer[i]].received_kill    <= 1'b0;
		 instr_queue[push_pointer[i]].expects_kill     <= FV_FUNC_instr_expects_kill(IF2EX_instr_in[i].instr, IF2EX_instr_in[i].predict_br_taken);
		 instr_queue[push_pointer[i]].is_branch        <= FV_FUNC_instr_is_branch(IF2EX_instr_in[i].instr);
`ifdef FV_DUP_BR
                 instr_queue[push_pointer[i]].predict_br_taken <= IF2EX_instr_in[i].predict_br_taken;
                 instr_queue[push_pointer[i]].is_dup           <= IF2EX_instr_in[i].is_dup;
`endif
	      end // if (IF2EX_instr_in_valid[i])
	   end // for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++)
	end // if (queue_push)

	if (EX_kill && found_flag) begin
	   instr_queue[found_pointer].received_kill <= instr_queue[found_pointer].is_branch ? dut_branch_taken : 1; // received the kill so clear it (no longer expects kill)
	end
     end // always @ (posedge clk)
 
   // queue next_commit pointer update
   always @(*) begin

      next_commit_pointer_inc[0] = 0;
      for (int i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin
	 if (commit[i] == 1)
	   next_commit_pointer_inc[i] = next_commit_pointer_inc[i-1] + {{(`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1){1'b0}}, 1'b1};
	 else
	   next_commit_pointer_inc[i] = next_commit_pointer_inc[i-1];
      end
   end

   always @(posedge clk)
     begin
        if (!reset_)
          next_commit_pointer_flopped <= {`FV_EX_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
        else if (update_next_commit_pointer)
          next_commit_pointer_flopped <= next_commit_pointer_flopped + next_commit_pointer_inc[`FV_MAX_COMMIT_PER_CYCLE];
     end // always @ (posedge clk)

   logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1:0] pop_pointer;
   logic [`FV_MAX_COMMIT_PER_CYCLE:1] 					    expected_kill, received_kill;
   
   // queue head pointer update
   always @(*) begin

      head_pointer_inc[0] = 0;
      for (int i=1; i<=`FV_MAX_COMMIT_PER_CYCLE; i++) begin
	 if (check_committed_instr[i] ==1)
	   head_pointer_inc[i] = head_pointer_inc[i-1] + {{(`FV_EX_INSTR_QUEUE_POINTER_WIDTH-1){1'b0}}, 1'b1};
	 else
	   head_pointer_inc[i] = head_pointer_inc[i-1];

	 pop_pointer[i]   = head_pointer_flopped + head_pointer_inc[i-1];
	 expected_kill[i] = instr_queue[pop_pointer[i]].expects_kill;
	 received_kill[i] = instr_queue[pop_pointer[i]].received_kill;
     
      end
   end      
   
   always @(posedge clk)
     begin
        if (!reset_)
          head_pointer_flopped <= {`FV_EX_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
        else if (queue_pop)
          head_pointer_flopped <= head_pointer_flopped + head_pointer_inc[`FV_MAX_COMMIT_PER_CYCLE];
     end // always @ (posedge clk)
   
endmodule // FV_CORE_EX_queue

