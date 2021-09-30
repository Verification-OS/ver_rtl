
// NOTE: User is free to add more cover properties in the included FV_cov_dut.svh.

module FV_cov(
		  input logic 								  clk,
		  input logic 								  reset_,

		  // instructions that are generated and sent out to DUT by FV module
		  input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1] 			  IF_instruction_out_valid,
		  input logic [`FV_IF_MAX_INSTR_PER_CYCLE:1][`FV_INSTR_WIDTH-1:0] IF_instruction_out // individual instructions that are packed into IF_instruction_bus_out
		  );

   genvar i;

//   for (i=1; i<=`FV_IF_MAX_INSTR_PER_CYCLE; i++) begin
   for (i=1; i<=1; i++) begin
      FV_COV_instructions instr_cov(.clk(clk), 
					.instr_valid(IF_instruction_out_valid[i]), 
					.instr(IF_instruction_out[i])
					);
   end
   
`include "FV_cov_dut.svh"
   
endmodule // FV_cov
