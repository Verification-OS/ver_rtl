
`ifndef _FV_VH
`define _FV_VH

`define FV_MAX_BMC_DEPTH 256

`ifdef FV_ENCRYPTED
 `include "FV_common1.svhp"
`else
 `include "FV_common1.svh"
`endif

// DUT arch params, both:
//  - ISA-dependent, such as the ISA choice itself, and  
//  - ISA-independent, e.g., two-way super-scalar

`include "fv_dut.svh"

`ifdef FV_ENCRYPTED
 `include "FV_common2.svhp"
`else
 `include "FV_common2.svh"
`endif

`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS
 `include "FV_trim_indiv_instr.svh"
`endif
`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS_2
 `include "FV_trim_indiv_instr2.svh"
`endif
`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS_3
 `include "FV_trim_indiv_instr3.svh"
`endif
`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS_4
 `include "FV_trim_indiv_instr4.svh"
`endif
`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS_5
 `include "FV_trim_indiv_instr5.svh"
`endif
`ifdef FV_TRIM_INDIVIDUAL_INSTRUCTIONS_CVA6
 `include "FV_trim_indiv_instr_cva6.svh"
`endif

`endif //  `ifndef _FV_VH

