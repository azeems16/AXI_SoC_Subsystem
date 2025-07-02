class cdc_harness_coverage;

logic wr_clk, rd_clk;
logic wr_en, wr_full;
logic rd_en, rd_empty;

covergroup wr_cg @ (posedge wr_clk);
    option.per_instance = 1;
    coverpoint wr_en   {bins off      = {0}; bins on   = {1}; }
    coverpoint wr_full {bins not_full = {0}; bins full = {1}; }
    wr_enXfull: cross wr_en, wr_full;
endgroup

covergroup rd_cg @ (posedge rd_clk);
    option.per_instance = 1;
    coverpoint rd_en    {bins off       = {0}; bins on    = {1}; }
    coverpoint rd_empty {bins not_empty = {0}; bins empty = {1}; }
    rd_enXfull: cross rd_en, rd_empty;

// Additionally add transitional states   
endgroup

function new(input logic clk1, input logic clk2);
    this.wr_clk = clk1;
    this.rd_clk = clk2;
    wr_cg = new();
    rd_cg = new();
endfunction

function void drive_sample_wr(
    input logic wr_en,
    input logic wr_full
);
    this.wr_en    = wr_en;
    this.wr_full  = wr_full;

    wr_cg.sample();
endfunction
  
function void drive_sample_rd(
    input logic rd_en,
    input logic rd_empty
);
    this.rd_en    = rd_en;
    this.rd_empty = rd_empty;

    rd_cg.sample();
endfunction

endclass