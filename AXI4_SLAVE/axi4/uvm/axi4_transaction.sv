`include "uvm_macros.svh"
 import uvm_pkg::*;

class axi_txn #(
    parameter int ADDR_WIDTH = 32 ,
    parameter int DATA_WIDTH = 32 
) extends uvm_sequence_item;
`uvm_object_param_utils(axi_txn #(ADDR_WIDTH, DATA_WIDTH))

rand logic                      is_write;

rand logic [ADDR_WIDTH-1:0]     addr    ;
rand logic [7:0]                len     ;
rand logic [2:0]                size    ;
rand logic [1:0]                burst   ;

rand logic [DATA_WIDTH-1:0]     wdata[] ;
rand logic [(DATA_WIDTH/8)-1:0] wstrb   ;

logic [DATA_WIDTH-1:0]          rdata[] ;
logic [1:0]                     resp    ;

function new(input string name = "transaction");
    super.new(name);
endfunction

constraint legal_burst {burst inside {2'b00, 2'b01, 2'b10};}
constraint legal_wstrb {is_write -> wstrb != '0;}
constraint addr_align  {addr % (1 << size) == 0;}   // Address must be aligned to the size of each beat (2^size)
constraint max_bytes   {(len + 1) * (1 << size) <= 256;}
constraint wrap_len_limit {
    burst == 2'b10 -> len inside {[0:15]};  // cannot exceed 16 beats per burst
    burst != 2'b10 -> len inside {[0:255]};
}
constraint wrap_addr_boundary {
    burst == 2'b10 -> addr % ((len + 1) * (1 << size)) == 0;
}
constraint wdata_len_consistency {
    is_write  -> (wdata.size() == len + 1);
    !is_write -> (rdata.size() == len + 1);
}

endclass

