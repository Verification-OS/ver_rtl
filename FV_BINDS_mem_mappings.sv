
// This file contains a set of memory mapping functions (in form of modules).
// Custom mappings can be added as needed.

module FV_BINDS_mem_map_byte
  #(parameter MEM_SIZE=`DMEM_SIZE)
   (
    input logic [7:0] 			  mem_in[MEM_SIZE],
    output logic [(MEM_SIZE/4)-1:0][31:0] mem_out
    );

   genvar j;
   generate
      for (j = 0; j < MEM_SIZE; j+=4) begin
	 localparam integer k = j/4;
	 assign mem_out[k] = {mem_in[j+3], mem_in[j+2], mem_in[j+1], mem_in[j]};
      end
   endgenerate
   
endmodule // FV_BINDS_mem_map_byte

module FV_BINDS_mem_map_dword
  #(parameter MEM_SIZE=`DMEM_SIZE)
   (
    input logic [31:0] 			  mem_in[0:(MEM_SIZE/4)-1],
    output logic [(MEM_SIZE/4)-1:0][31:0] mem_out
    );

   genvar j;
   generate
      for (j = 0; j < (MEM_SIZE/4); j++) begin
	 assign mem_out[j] = mem_in[j];
      end
   endgenerate
   
endmodule // FV_BINDS_mem_map_dword

module FV_BINDS_mem_map_byte_bank
  #(parameter MEM_SIZE=`DMEM_SIZE)
   (
    input logic [7:0] 			  mem0_in [(MEM_SIZE/4)-1:0],
    input logic [7:0] 			  mem1_in [(MEM_SIZE/4)-1:0],
    input logic [7:0] 			  mem2_in [(MEM_SIZE/4)-1:0],
    input logic [7:0] 			  mem3_in [(MEM_SIZE/4)-1:0],

    output logic [(MEM_SIZE/4)-1:0][31:0] mem_out
    );

   genvar j;
   generate
      for (j = 0; j < (MEM_SIZE/4); j++) begin
	 assign mem_out[j] = {mem3_in[j], mem2_in[j], mem1_in[j], mem0_in[j]};
      end
   endgenerate
   
endmodule // FV_BINDS_mem_map_byte_bank

module FV_BINDS_mem_map_byte_3d
  #(parameter MEM_SIZE=`DMEM_SIZE,                       // MEM_SIZE is in bytes
    parameter MEM_DATA_WIDTH=`FV_DUT_MEM_DATA_WIDTH, // MEM_DATA_WIDTH is in bits
    parameter MEM_DEPTH=(MEM_SIZE/(MEM_DATA_WIDTH/8)))
   (
    input logic [MEM_DATA_WIDTH/8-1:0] [7:0] mem_in [MEM_DEPTH],
    output logic [(MEM_SIZE/4)-1:0][31:0]    mem_out
    );

   genvar n;
   generate
      for (n = 0; n < (MEM_SIZE/4); n++) begin
	 localparam integer k =  n / (MEM_DATA_WIDTH/32); // dmem is dword wide, so /32 to get mem's addr
	 localparam integer m = (n % (MEM_DATA_WIDTH/32))*4; // offset within the mem width
	 assign mem_out[n] = {mem_in[k][m+3], mem_in[k][m+2], mem_in[k][m+1], mem_in[k][m]}; // concat 4 bytes
      end
   endgenerate
   
endmodule // FV_BINDS_mem_map_byte_3d


