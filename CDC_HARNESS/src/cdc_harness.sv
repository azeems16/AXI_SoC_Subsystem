module cdc_harness #(
  parameter DATA_WIDTH = 8,
  parameter ADDR_WIDTH = 4
) (
  input  logic                  wr_clk,
  input  logic                  wr_rst_n_async,
  input  logic [DATA_WIDTH-1:0] wr_data,
  input  logic                  wr_en,
  output logic                  wr_full,

  input  logic                  rd_clk,
  input  logic                  rd_rst_n_async,
  output logic [DATA_WIDTH-1:0] rd_data,
  input  logic                  rd_en,
  output logic                  rd_empty
);

logic wr_rst_n_sync;
logic rd_rst_n_sync;

cdc_reset_sync reset_synchronizer_write (
  .dst_clk     (wr_clk) ,
  .rst_n_async (wr_rst_n_async) ,
  .rst_n_sync  (wr_rst_n_sync)
);

cdc_reset_sync reset_synchronizer_read (
  .dst_clk     (rd_clk) ,
  .rst_n_async (rd_rst_n_async) ,
  .rst_n_sync  (rd_rst_n_sync)
);

cdc_async_fifo async_fifo (
  // Write domain ports
  .wr_clk   (wr_clk) ,
  .wr_rst_n (wr_rst_n_sync) ,
  .wr_data  (wr_data) ,
  .wr_en    (wr_en) ,
  .wr_full  (wr_full) ,
  
  .rd_clk   (rd_clk) ,
  .rd_rst_n (rd_rst_n_sync) ,
  .rd_data  (rd_data) ,
  .rd_en    (rd_en) ,
  .rd_empty (rd_empty)
);


endmodule