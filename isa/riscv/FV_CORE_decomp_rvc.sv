
module FV_CORE_decomp_rvc
(
    input  logic [31:0] instr_i,
    output logic [31:0] instr_o,
    output logic        illegal_instr_o,
    output logic        is_compressed_o
);

   assign instr_o = instr_i;
   assign illegal_instr_o = 0;
   assign is_compressed_o = 0;

endmodule // FV_CORE_decomp_rvc
