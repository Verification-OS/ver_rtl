
module FV_core(
		   input logic 								    clk,
		   input logic 								    reset_,

		   input arf_signals_t                                                      arf_sigs,

		   input logic [`FV_DUT_NUM_MEM_REGIONS-1:0][(`DMEM_SIZE/4)-1:0][31:0]  dmem,
		   input logic [`FV_DUT_NUM_MEM_REGIONS-1:0] 			    dmem_region_enables, // not used yet, remove?
   
		   input logic 								    ld_st_valid,
		   input logic [`FV_MEM_ADDR_WIDTH-1:0] 				    ld_st_effaddr,
		   input logic [`FV_REG_WIDTH-1:0] 					    ld_st_imm,
   
		   // instruction fetch related signals
                   output logic 							    IF_instruction_req_grant,
		   output logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			    IF_instruction_out_valid,
		   output logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] IF_instruction_out,
  		   output logic [`FV_IF_BUS_WIDTH-1:0] 				    IF_instruction_bus_out,
		   // the following PC corresponds to the PC of the first valid address fetched, not the possibly padded wide interface
		   output logic [`FV_INSTR_ADDR_WIDTH-1:0] 				    IF_instruction_pc,

		   input logic [`FV_INSTR_ADDR_WIDTH-1:0] 				    IF_pc,
		   input logic [`FV_INSTR_ADDR_WIDTH-1:0] 				    IF_mem_fetch_addr,
		   input logic 								    IF_stall,
		   input logic 								    IF_kill,

		    // instruction execution related signals
		   input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			    IF2EX_instruction_in_valid,
		   input logic [`FV_INSTR_ADDR_WIDTH-1:0] 				    IF2EX_pc,
		   input logic 								    IF2EX_stall,
		   input logic 								    IF2EX_kill,

		   input logic 								    EX_stall,
		   input logic 								    EX_kill,
		   
		   input logic [`FV_MAX_COMMIT_PER_CYCLE:1] 			    commit,

		   input logic 								    dut_branch_taken,
		   input logic 								    dut_jump_taken,
		   output logic [`FV_NUM_RF_WR_PORTS:1] 				    fv_override_rf_wdata,

		   output prop_signals_t                                                    ps
		   );
   
   logic  enable;
   assign enable = 1;
   
   wire 		    dup_enable;
   wire 		    cmt_enable;
   wire 		    cf_enable;
   wire 		    si_enable;
`ifdef FV_ENABLE_DUP
   assign 		    dup_enable = enable;
`else
   assign 		    dup_enable = 1'b0;
`endif
`ifdef FV_ENABLE_CMT
   assign 		    cmt_enable = enable;
`else
   assign 		    cmt_enable = 1'b0;
`endif
`ifdef FV_ENABLE_CF
   assign 		    cf_enable = enable;
`else
   assign 		    cf_enable = 1'b0;
`endif
`ifdef FV_ENABLE_SI
   assign 		    si_enable = enable;
`else
   assign 		    si_enable = 1'b0;
`endif

   struct packed {
      logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] instr_in;
   } i_drivers;
   assign i_drivers = {$bits(i_drivers){enable}};

   wire [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] instruction_in;
   assign instruction_in = i_drivers.instr_in;
   
   struct packed {
      logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_attempt_dup;
      logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_attempt_dup_sync;
      logic fv_if_insert_bubble;
      logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_predict_br_taken;
   } o_drivers;
   assign o_drivers = {$bits(o_drivers){enable}};
   
   wire [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_attempt_dup = o_drivers.fv_if_attempt_dup;
`ifdef FV_RND_BUBBLE
   wire fv_if_insert_bubble = o_drivers.fv_if_insert_bubble;
`else
   assign fv_if_insert_bubble = 0;
`endif
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_attempt_dup_sync;
`ifdef FV_NO_DUP_SYNC_READY
   assign fv_if_attempt_dup_sync = {(`FV_IF_MAX_INSTR_PER_CYCLE){1'b0}};
`else
   assign fv_if_attempt_dup_sync = o_drivers.fv_if_attempt_dup_sync;
`endif
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] fv_if_predict_br_taken;
`ifdef FV_DUP_BR
   assign fv_if_predict_br_taken = o_drivers.fv_if_predict_br_taken;
`else
   assign fv_if_predict_br_taken = {(`FV_IF_MAX_INSTR_PER_CYCLE){1'b0}};
`endif   
   // ================
   // property signals

`define FV_PATH_CORE       `FV_DUT_PATH.fv.core
`define FV_PATH_IF         `FV_PATH_CORE.instr_fetch
`define FV_PATH_EX         `FV_PATH_CORE.ex_tracker
`define FV_PATH_EX_INSTR_Q `FV_PATH_CORE.ex_tracker.instr_queue
`define FV_PATH_EX_RF      `FV_PATH_CORE.ex_tracker.rf_tracker
`define FV_PATH_EX_CF      `FV_PATH_CORE.ex_tracker.cf_tracker
   
   logic [9:0] 						    fv_num_committed_instr;
   logic [9:0] 						    fv_clock_counter_ns;
   // internally from EX to IF
   logic                  EX2IF_killed_instr_found;
   ex_queue_entry_t       EX2IF_killed_instr;
   genvar i;
   
   // =============
   // DUP
   for (i = 0; i < `FV_NUM_RF_REGS; i++) begin
      assign ps.arf1[i] = arf_sigs.arf1[i];
   end
   assign ps.fv_dup_ready_1        = `FV_PATH_EX_RF.fv_dup_ready;
   assign ps.fv_dup_ready_pairs_1  = `FV_PATH_EX_RF.fv_dup_ready_pairs;
   assign ps.fv_dup_sync_ready     = `FV_PATH_EX.fv_dup_sync_ready;

`ifdef FV_RF2_ENABLE
   for (i = 0; i < `FV_NUM_RF2_REGS; i++) begin
      assign ps.arf2[i] = arf_sigs.arf2[i];
   end

   assign ps.fv_dup_ready_2        = `FV_PATH_EX_RF.fv_dup_ready_2;
   assign ps.fv_dup_ready_pairs_2  = `FV_PATH_EX_RF.fv_dup_ready_pairs_2;
`endif

`ifdef FV_RF3_ENABLE
   for (i = 0; i < `FV_NUM_RF3_REGS; i++) begin
      assign ps.arf3[i] = arf_sigs.arf3[i];
   end

   assign ps.fv_dup_ready_3        = `FV_PATH_EX_RF.fv_dup_ready_3;
   assign ps.fv_dup_ready_pairs_3  = `FV_PATH_EX_RF.fv_dup_ready_pairs_3;
`endif

   // =============
   // CMT
   assign ps.fv_num_committed_instr = fv_num_committed_instr; 
   assign ps.fv_clock_counter_ns    = fv_clock_counter_ns;
   
   // =============
   // CF
   assign ps.cf_check             = `FV_PATH_EX_CF.cf_check;
   assign ps.instr_correct_next_pc1  = `FV_PATH_EX_CF.instr_correct_next_pc1;
`ifndef FV_ENABLE_SI
   assign ps.instr_correct_next_pc2  = `FV_PATH_EX_CF.instr_correct_next_pc2;
   assign ps.instr_is_exempt         = `FV_PATH_EX_CF.instr_is_exempt;
`endif
   assign ps.instr_committed_next_pc = `FV_PATH_EX.instr_committed_next_pc;
   assign ps.check_jmp_taken         = `FV_PATH_EX_CF.check_jmp_taken;

   assign ps.killed_instr_found      = EX2IF_killed_instr_found;
   
`ifdef FV_DUP_BR
   assign ps.check_br_dup_taken      = `FV_PATH_EX_CF.check_br_dup_taken;
   assign ps.check_BR_dest_pc        = `FV_PATH_EX_CF.check_BR_dest_pc; 
   assign ps.check_JAL_dest_pc       = `FV_PATH_EX_CF.check_JAL_dest_pc; 
   assign ps.check_JALR_dest_pc      = `FV_PATH_EX_CF.check_JALR_dest_pc;
   assign ps.CF_orig_taken           = `FV_PATH_EX_CF.CF_orig_taken; 
   assign ps.CF_dup_taken            = `FV_PATH_EX_CF.CF_dup_taken;
   assign ps.CF_orig_dest_pc         = `FV_PATH_EX_CF.CF_orig_dest_pc; 
   assign ps.CF_dup_dest_pc          = `FV_PATH_EX_CF.CF_dup_dest_pc;
   assign ps.CF_orig_dest_pc_offset  = `FV_PATH_EX_CF.CF_orig_dest_pc_offset; 
   assign ps.CF_dup_dest_pc_offset   = `FV_PATH_EX_CF.CF_dup_dest_pc_offset;
`endif //  `ifdef FV_DUP_BR

   assign ps.ex_queue_is_empty       = `FV_PATH_EX_INSTR_Q.is_empty;
   assign ps.no_uncommitted_instr    = `FV_PATH_EX_INSTR_Q.no_uncommitted_instr;
   assign ps.ex_queue_is_full        = `FV_PATH_EX_INSTR_Q.is_full;
   assign ps.check_committed_instr   = `FV_PATH_EX_INSTR_Q.check_committed_instr;
   assign ps.expected_kill           = `FV_PATH_EX_INSTR_Q.expected_kill;
   assign ps.received_kill           = `FV_PATH_EX_INSTR_Q.received_kill;
				       
   // ==============

// Note1: move this to a FV header file
`ifdef FV_ENABLE_CMT
 `define FV_MAX_CLOCK_COUNTER (`FV_CMT_CHECK_CLK_COUNT+2)
`else
 `define FV_MAX_CLOCK_COUNTER (`FV_SI_SRC_CAPTURE_CYCLE+2)
`endif  

   // a saturating in addition to the non-saturating clock counter
   logic [9:0] clock_counter;
   logic       fv_init;

   always @(posedge clk)
     begin
	if (!reset_) begin
	   clock_counter        <= 10'b0;  
	   fv_clock_counter_ns <= 10'b0;  
	end else begin
	   if (clock_counter < `FV_MAX_CLOCK_COUNTER)
	     clock_counter  <= clock_counter + 1;
	   fv_clock_counter_ns <= fv_clock_counter_ns + 1;
	end
     end

   assign fv_init = (clock_counter == 0);

   logic                                    IF_instr_req_grant;
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] IF_instr_out_valid;
   if_queue_entry_t                         IF_instr_out[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   logic [`FV_IF_BUS_WIDTH-1:0] 	    IF_instr_bus_out;
   logic [`FV_INSTR_ADDR_WIDTH-1:0]     IF_instr_pc;
   
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] IF2EX_instr_in_valid;
   if_queue_entry_t                         IF2EX_instr_in[`FV_IF_MAX_INSTR_PER_CYCLE:1];
   
`ifdef FV_INCLUDE_RVC
   logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] illegal_rvc, is_compressed;
`endif
   
   assign IF_instruction_req_grant = IF_instr_req_grant;
   
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
      assign IF_instruction_out_valid[i] = IF_instr_out_valid[i];
      assign IF_instruction_out[i]       = IF_instr_out[i].instr;

      // in case needed, valid goes out and comes back in.  
      // instr follows the same but so far comes back in as is
      assign IF2EX_instr_in_valid[i]            = IF2EX_instruction_in_valid[i];
      // straight internal connection for the following
`ifdef FV_INCLUDE_RVC
      FV_CORE_decomp_rvc decomp_rvc(.instr_i(IF_instr_out[i].instr),
				        .instr_o(IF2EX_instr_in[i].instr),
					.illegal_instr_o(illegal_rvc[i]),
					.is_compressed_o(is_compressed[i])
					);
      assign IF2EX_instr_in[i].instr_size       = is_compressed[i] ? 2 : IF_instr_out[i].instr_size; // store the original size to next PC can be calculated based on that
`else
      assign IF2EX_instr_in[i].instr            = IF_instr_out[i].instr;
      assign IF2EX_instr_in[i].instr_size       = IF_instr_out[i].instr_size;
`endif
      assign IF2EX_instr_in[i].predict_br_taken = IF_instr_out[i].predict_br_taken;
      assign IF2EX_instr_in[i].is_dup           = IF_instr_out[i].is_dup;
      // the following two are not used in CORE_ex but just in case ...
      assign IF2EX_instr_in[i].is_dup_flush    = IF_instr_out[i].is_dup_flush;
      assign IF2EX_instr_in[i].is_dup_sync     = IF_instr_out[i].is_dup_sync;
   end // for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++)
   // other PCs can be drived using this as base (for instr 1, and instr_sizes)
   assign IF_instruction_bus_out = IF_instr_bus_out;
   assign IF_instruction_pc      = IF_instr_pc;

   // ======================
   // submodule instantiations
   
   FV_CORE_inits initializations(.*,
`ifdef FV_DUT_HAS_RF2
				     .arf2(arf_sigs.arf2),
`endif
`ifdef FV_DUT_HAS_RF3
				     .arf3(arf_sigs.arf3),
`endif
				     .arf1(arf_sigs.arf1)
				     );

   FV_CORE_if instr_fetch(.*);

   FV_CORE_constraints constraints(.*);

   FV_CORE_ex ex_tracker(.*);
   
`ifdef FV_ENABLE_SI
   si_prop_signals_t si_ps;
   logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] arf;
   assign arf = arf_sigs.arf1;

   FV_CORE_si si_core(.*,
			 .instruction(IF_instruction_out[1]),
			 .instruction_valid(IF2EX_instruction_in_valid[1]),
			 .pc(IF2EX_pc),
			 .clock_counter(fv_clock_counter_ns),
			 .si_ps(si_ps)
			 );

   assign ps.si_ps = si_ps;
`endif
   
   //=========================
   //=========================

`ifndef FV_ILLEGAL_INSTR_ALLOWED
   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin : FV_no_illegal_instr
      prop: assume property (@(posedge clk) (IF_instruction_out[i] != 32'b0));
   end
`endif

endmodule // FV_core



