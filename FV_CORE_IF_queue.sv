
module FV_CORE_IF_queue( // inputs from DUT
			     input logic 				     clk, 
			     input logic 				     reset_,
					 
			     input logic 				     stall,
			     input logic 				     kill,
									
			     // internal inputs
			     input logic 				     killed_instr_found,
		             input ex_queue_entry_t                          killed_instr,

			     input logic 				     no_output_when_kill,
			     input if_queue_entry_t                          instr_out[`FV_IF_MAX_INSTR_PER_CYCLE:1],
			     input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1]  queue_push,
			     input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1]  queue_pop,

			     // internal outputs
			     output if_queue_entry_t                         instr_queue_head[`FV_IF_MAX_INSTR_PER_CYCLE:1],
			     output logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] is_empty
			  );

   if_queue_entry_t instr_queue[`FV_IF_INSTR_QUEUE_DEPTH-1:0];

   logic [`FV_IF_MAX_INSTR_PER_CYCLE+1:1][`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1:0] head_pointer, tail_pointer, tail_pointer_inc, push_pointer;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1:0] new_head_pointer;
   logic [`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1:0] head_pointer_flopped;
   logic [`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1:0] tail_pointer_flopped;

   logic kill_int; // only kills if we didn't expect the kill (from taken branches and jumps); used in BR_DUP mode
`ifdef FV_DUP_BR
   // dup branches get mixed like other orig/dup instruction and when predicted taken, the following instructions don't get pushed into the queue so no need to kill
   assign kill_int = kill && (!killed_instr_found);
`else
   assign kill_int = kill && (killed_instr_found && FV_FUNC_instr_is_CF_nodup(killed_instr.instr)); // default kill if no branch duplication
`endif

   logic  is_full, going_empty;
   assign going_empty = kill_int && (!no_output_when_kill);

   genvar i;
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE+1; i++) begin : per_instr_pointers
      if (i == 1) begin
	 assign head_pointer[1]     = head_pointer_flopped;
	 assign tail_pointer[1]     = tail_pointer_flopped;
	 assign tail_pointer_inc[1] = 0;
	 assign push_pointer[1]     = kill_int ? {`FV_IF_INSTR_QUEUE_POINTER_WIDTH{1'b0}} : tail_pointer_flopped;
      end else begin
	 assign head_pointer[i]     = head_pointer[i-1]     + {{(`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1){1'b0}}, queue_pop[i-1]};
	 assign tail_pointer[i]     = tail_pointer[i-1]     + {{(`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1){1'b0}}, queue_push[i-1]};
	 assign tail_pointer_inc[i] = tail_pointer_inc[i-1] + {{(`FV_IF_INSTR_QUEUE_POINTER_WIDTH-1){1'b0}}, queue_push[i-1]};
	 assign push_pointer[i]     = kill_int ? tail_pointer_inc[i] : tail_pointer[i];
      end
   end

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : empty
      assign is_empty[i] = (tail_pointer[i] == head_pointer[i]) || going_empty;
   end  

   assign is_full =   ((tail_pointer_flopped + 1) == head_pointer_flopped); // Note0 update for N instructions
   // Note: implement wrap-around logic and wait till have space?
`ifdef FV_ENABLE_SC_DEBUG
   FV_check_if_queue_not_full: assert property (@(posedge clk) (!is_full));
`endif
   
   // ================
   // queue head/tail pointers update

   always @(posedge clk)
     begin
        if (!reset_ || kill_int) begin
           head_pointer_flopped <= {`FV_IF_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
           tail_pointer_flopped <= (!stall) ? tail_pointer_inc[`FV_IF_MAX_INSTR_PER_CYCLE+1] : {`FV_IF_INSTR_QUEUE_POINTER_WIDTH{1'b0}};
        end else if (!stall) begin
           head_pointer_flopped <= head_pointer[`FV_IF_MAX_INSTR_PER_CYCLE+1];
           tail_pointer_flopped <= tail_pointer[`FV_IF_MAX_INSTR_PER_CYCLE+1];
	end
     end  
   
   always @(posedge clk)
     begin
	for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : queue_update
	   if ((!stall) && queue_push[i])
	     instr_queue[push_pointer[i]] <= instr_out[i];
	end
     end

   if_queue_entry_t new_queue_entries[`FV_IF_MAX_INSTR_PER_CYCLE-1:0];

   logic [$clog2(`FV_IF_MAX_INSTR_PER_CYCLE):0] new_pointer;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][$clog2(`FV_IF_MAX_INSTR_PER_CYCLE):0] new_head_pointer_inc;

   always @(*)
     begin
	new_pointer = 0;
	for (int i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
	   if (queue_push[i]) begin
	      new_queue_entries[new_pointer] = instr_out[i];
	      new_pointer = new_pointer + 1;
	   end
	end
     end
   
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      if (i==1) 
	assign new_head_pointer_inc[1] = 0;
      else
	assign new_head_pointer_inc[i] = ((head_pointer[i] <= tail_pointer_flopped)) ? 0 : (new_head_pointer_inc[i-1] + queue_pop[i-1]);
   end

   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign new_head_pointer[i] = new_head_pointer_inc[i];
      if (i == 1) begin
	 assign instr_queue_head[1] = instr_queue[head_pointer[1]];
      end else begin
	 assign instr_queue_head[i] = (head_pointer[i] < tail_pointer_flopped) ? instr_queue[head_pointer[i]] : 
				   new_queue_entries[new_head_pointer[i]];
      end
   end
      
endmodule // FV_CORE_IF_queue


