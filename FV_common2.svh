
`pragma protect begin
`protect

`ifndef _FV_COMMON2_VH
`define _FV_COMMON2_VH

`ifdef FV_INCLUDE_RISCV

// NOTE: MISC_MEM operations are not included by default
//       add `define FV_RV_MISC_MEM to include them

`endif //  `ifdef FV_INCLUDE_RISCV

package fv_pkg;

`ifdef FV_ENCRYPTED
 `include "FV_isa.svhp"
`else
 `include "FV_isa.svh"
`endif

`define FV_INSTR_SIZE_WIDTH $clog2(`FV_INSTR_WIDTH)

`define FV_SI_SIGNALS_PATH core.instr_fetch.instr[1].gen.instr_constraint.encoder
   
`endif //  `ifndef _FV_COMMON2_VH

   // instruction size in bytes
   // NOTES:
   //   - 0=no instruction, 1=8 bits, 2=16 bits, etc.
   //   - max is MSB=1, all other bits 0
   typedef logic [$clog2(`FV_INSTR_WIDTH):0] instr_size_t; 

   typedef struct {
      logic [`FV_INSTR_WIDTH-1:0] instr;
      instr_size_t                    instr_size;
      logic 			      is_dup;        // 1 = is a duplicate
      logic 			      is_dup_sync;  // 1 = is a sync token; after all duplicates are sent
      logic 			      is_dup_flush; // 1 = is a flush token; after all originals are sent (if FV_DUP_NO_RND_MIX is defined)
      logic 			      predict_br_taken;
   } if_queue_entry_t;
   
   typedef struct {
      logic [`FV_INSTR_WIDTH-1:0]      instr;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] pc;
      instr_size_t                         instr_size; // could be different than what it is in the EX queue, e.g., could be decompressed before storing here
`ifdef FV_ENABLE_SI
      logic [`FV_REG_WIDTH-1:0] 	   rs1_value; // used for si-FV
      logic [`FV_REG_WIDTH-1:0] 	   rs2_value; // used for si-FV
`endif
      logic 				   received_kill;
      logic 				   expects_kill; // we expect to receive a kill for this instruction; cleared after kill is received
      logic 				   is_branch; // decode ahead of time
`ifdef FV_DUP_BR
      logic 				   predict_br_taken;
      logic 				   is_dup;
`endif
   } ex_queue_entry_t;
   
   typedef struct {
      // DUP
      logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0] arf1;
      logic 	                          fv_dup_ready_1;
      logic [(`FV_NUM_RF_REGS/2)-1:0] fv_dup_ready_pairs_1;
      logic 				  fv_dup_sync_ready;

`ifdef FV_RF2_ENABLE
      logic [(`FV_NUM_RF2_REGS)-1:0][`FV_REG2_WIDTH-1:0] arf2;
      logic 	                           fv_dup_ready_2;
      logic [(`FV_NUM_RF2_REGS/2)-1:0] fv_dup_ready_pairs_2;
`endif

`ifdef FV_RF3_ENABLE
      logic [(`FV_NUM_RF3_REGS)-1:0][`FV_REG3_WIDTH-1:0] arf3;
      logic 	                           fv_dup_ready_3;
      logic [(`FV_NUM_RF3_REGS/2)-1:0] fv_dup_ready_pairs_3;
`endif

      // CMT
      logic [9:0] 			  fv_num_committed_instr;
      logic [9:0] 			  fv_clock_counter_ns;

      // CF
      logic [`FV_MAX_COMMIT_PER_CYCLE:1] cf_check;
      logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_correct_next_pc1;
`ifndef FV_ENABLE_SI
      logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_correct_next_pc2;
      logic [`FV_MAX_COMMIT_PER_CYCLE:1] 				   instr_is_exempt;
`endif
      logic [`FV_MAX_COMMIT_PER_CYCLE:1][`FV_INSTR_ADDR_WIDTH-1:0] instr_committed_next_pc;

      logic killed_instr_found;
      logic check_jmp_taken;

 `ifdef FV_DUP_BR
      logic check_br_dup_taken;
      logic check_BR_dest_pc;
      logic check_JAL_dest_pc;
      logic check_JALR_dest_pc;
      logic CF_orig_taken;
      logic CF_dup_taken;
      logic [`FV_INSTR_ADDR_WIDTH-1:0] CF_orig_dest_pc, 
                                           CF_dup_dest_pc,
                                           CF_orig_dest_pc_offset, 
                                           CF_dup_dest_pc_offset;
 `endif //  `ifdef FV_DUP_BR
      
      logic [`FV_MAX_COMMIT_PER_CYCLE:1] ex_queue_is_empty,
      no_uncommitted_instr;

      logic [`FV_MAX_COMMIT_PER_CYCLE:1] check_committed_instr,
                                             expected_kill, 
                                             received_kill;
   
      logic 				     ex_queue_is_full;

`ifdef FV_ENABLE_SI
      si_prop_signals_t                      si_ps;
`endif

   } prop_signals_t;

   // architectural register file(s) connections from DUT to FV module
   typedef struct {
      logic [(`FV_NUM_RF_REGS)-1:0][`FV_REG_WIDTH-1:0]       arf1;  
      logic [`FV_NUM_RF_WR_PORTS:1] 		             rf1_write_en; // arch RF write-back enable(s)
      logic [`FV_NUM_RF_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0]  rf1_write_rd; // arch RF write-back reg num(s)
`ifdef FV_DUT_HAS_RF2
      logic [(`FV_NUM_RF2_REGS)-1:0][`FV_REG2_WIDTH-1:0]     arf2;
      logic [`FV_NUM_RF2_WR_PORTS:1] 			     rf2_write_en; // arch RF2 write-back enable(s)
      logic [`FV_NUM_RF2_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf2_write_rd; // arch RF2 write-back reg num(s)
`endif
`ifdef FV_DUT_HAS_RF3
      logic [(`FV_NUM_RF3_REGS)-1:0][`FV_REG3_WIDTH-1:0]     arf3;
      logic [`FV_NUM_RF3_WR_PORTS:1] 			     rf3_write_en; // arch RF3 write-back enable(s)
      logic [`FV_NUM_RF3_WR_PORTS:1][`FV_REG_ADDR_WIDTH-1:0] rf3_write_rd; // arch RF3 write-back reg num(s)
`endif
   } arf_signals_t;
   
endpackage // fv_pkg
   
import fv_pkg::*;

`endprotect
`pragma protect end
