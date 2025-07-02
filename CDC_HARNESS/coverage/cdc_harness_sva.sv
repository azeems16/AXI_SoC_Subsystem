module cdc_fifo_sva #(
  parameter DATA_WIDTH = 4,
  parameter DEPTH = 16
)(
  input logic wr_clk,
  input logic wr_en,
  input logic wr_full,

  input logic rd_clk,
  input logic rd_en,
  input logic rd_empty,

  input logic wr_rst_n_async,
  input logic rd_rst_n_async
);

  // -------------------------------------------------
  // Write Domain Assertions
  // -------------------------------------------------

  property no_write_when_full;
    @(posedge wr_clk) disable iff (!wr_rst_n_async)
      wr_en |-> !wr_full;
  endproperty
  assert property (no_write_when_full)
    else $error("Write attempted when FIFO was full.");

  // -------------------------------------------------
  // Read Domain Assertions
  // -------------------------------------------------

  property no_read_when_empty;
    @(posedge rd_clk) disable iff (!rd_rst_n_async)
      rd_en |-> !rd_empty;
  endproperty
  assert property (no_read_when_empty)
    else $error("Read attempted when FIFO was empty.");
endmodule