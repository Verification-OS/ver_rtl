
`define FV_RIDECORE_CORE_PATH top.pipe

assign clk    =  `FV_RIDECORE_CORE_PATH.clk;
assign reset_ = !`FV_RIDECORE_CORE_PATH.reset;

//=======================
// RF connections

logic [`FV_REG_WIDTH-1:0] regs[0:31];
assign regs = `FV_RIDECORE_CORE_PATH.aregfile.regfile.mem;

//=======================
// DMEM connections

logic [31:0] mem[0:(`DMEM_SIZE/4)-1];
assign mem = top.datamemory.mem;
FV_BINDS_mem_map_dword #(.MEM_SIZE(`DMEM_SIZE)) mem_map(.mem_in(mem), .mem_out(dmem[0]));   
// default enables
assign dmem_region_enables = `FV_DUT_MEM_REGION_ENABLES;

//=======================
// LD/ST connections

assign ld_st_valid   = `FV_RIDECORE_CORE_PATH.seiryu.issue;
assign ld_st_effaddr = `FV_RIDECORE_CORE_PATH.seiryu.effaddr;
assign ld_st_imm     = `FV_RIDECORE_CORE_PATH.seiryu.imm;

//=======================
// IF connections

`ifdef FV_INCLUDE_IF_STAGE
`else
assign instr_req_o = 1'b1;
assign IF_pc       = `FV_RIDECORE_CORE_PATH.pc;
assign IF_mem_fetch_addr = IF_pc; // Note until CF is implemented
 
assign `FV_RIDECORE_CORE_PATH.fv_vld_out1         = IF_instruction_out_valid[1];
assign `FV_RIDECORE_CORE_PATH.fv2ifu_instruction1 = IF_instruction_out[1];

 `ifdef FV_SUPER_SCALAR_2
assign `FV_RIDECORE_CORE_PATH.fv_vld_out2         =  IF_instruction_out_valid[2];
assign `FV_RIDECORE_CORE_PATH.fv2ifu_instruction2 =  IF_instruction_out[2];
assign `FV_RIDECORE_CORE_PATH.invalid2_pipe        = !IF_instruction_out_valid[2];
 `else
assign `FV_RIDECORE_CORE_PATH.invalid2_pipe        = 1'b1;
 `endif

`endif // !`ifdef FV_INCLUDE_IF_STAGE

assign IF_stall = `FV_RIDECORE_CORE_PATH.stall_IF;

//=======================
// kill/jump/branch
   
assign IF_kill          = `FV_RIDECORE_CORE_PATH.kill_IF;

logic  exunit_branch_is_jump;
assign exunit_branch_is_jump = (`FV_RIDECORE_CORE_PATH.kirin.opcode == `FV_RV_OPCODE_JALR) ||
			       (`FV_RIDECORE_CORE_PATH.kirin.opcode == `FV_RV_OPCODE_JAL);

assign dut_jump_taken   = `FV_RIDECORE_CORE_PATH.kill_IF &&   exunit_branch_is_jump;
assign dut_branch_taken = `FV_RIDECORE_CORE_PATH.kill_IF && (!exunit_branch_is_jump);

//=======================
// EX connections
   
assign IF2EX_instruction_in_valid[1] = IF_instruction_out_valid[1];
`ifdef FV_SUPER_SCALAR_2
assign IF2EX_instruction_in_valid[2] = IF_instruction_out_valid[2];
`endif
assign IF2EX_pc                    = IF_instruction_pc;
assign IF2EX_stall                 = 1'b0;
assign IF2EX_kill                  = IF_kill;

assign EX_stall                 = 1'b0;
assign EX_kill                  = IF_kill;

//=======================
// misc. connections

assign commit[1] = (!`FV_RIDECORE_CORE_PATH.prmiss) && (`FV_RIDECORE_CORE_PATH.comnum>0);
assign commit[2] = (!`FV_RIDECORE_CORE_PATH.prmiss) && (`FV_RIDECORE_CORE_PATH.comnum>1);

assign rf_write_en[1] = `FV_RIDECORE_CORE_PATH.arfwe1;
assign rf_write_en[2] = `FV_RIDECORE_CORE_PATH.arfwe2;
assign rf_write_rd[1] = `FV_RIDECORE_CORE_PATH.dstarf1;
assign rf_write_rd[2] = `FV_RIDECORE_CORE_PATH.dstarf2;


 
