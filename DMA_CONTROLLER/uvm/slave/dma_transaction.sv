class dma_txn #(
    parameter int ADDR_WIDTH = 32 ,
    parameter int DATA_WIDTH = 32
) extends uvm_sequence_item;
`uvm_object_param_utils(dma_txn#(ADDR_WIDTH, DATA_WIDTH))

rand logic                      is_write;

rand logic [ADDR_WIDTH-1:0]     addr;
rand logic [DATA_WIDTH-1:0]     wdata;
rand logic [(DATA_WIDTH/8)-1:0] wstrb;

logic [1:0]                     resp;
logic [DATA_WIDTH-1:0]          rdata;

logic [DATA_WIDTH-1:0]          out_reg;

function new(input string name = "dma_txn");
    super.new(name);
endfunction

localparam SRC_ADDR   = 32'h00;
localparam DST_ADDR   = 32'h04;
localparam LEN_ADDR   = 32'h08;
localparam CTRL_ADDR  = 32'h0C;
localparam STAT_ADDR  = 32'h10;
localparam BURST_ADDR = 32'h14;

constraint legal_addr {
  addr inside { SRC_ADDR, DST_ADDR, LEN_ADDR, CTRL_ADDR, BURST_ADDR };
}
constraint legal_wstrb  {is_write -> wstrb != '0;};
constraint burst_addr {(addr == BURST_ADDR) -> }
endclass