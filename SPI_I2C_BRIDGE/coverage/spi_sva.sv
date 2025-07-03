module spi_sva (
  input  logic        sclk      , // SPI clock (from master)
  input  logic        cs_n      , // Active-low chip select
  input  logic        mosi      , // Master Out, Slave In
  input  logic        wr_clk    , // Write clock (system domain)
  input  logic        wr_rst_n  , // Write domain reset
  input  logic        wr_full   , // Write full from FIFO
  input  logic [7:0]  rx_data   , // Output data byte (valid when wr_en asserted)
  input  logic        wr_en       // Write enable for FIFO
);

property off_if_not_selected;
    @ (posedge wr_clk) disable iff (!wr_rst_n)
    cs_n |-> !wr_en;
endproperty

property off_when_full;
    @ (posedge wr_clk) disable iff (!wr_rst_n)
    wr_full |-> !wr_en;
endproperty

property valid_write_conditions;
  @(posedge wr_clk) disable iff (!wr_rst_n)
  wr_en |-> (!cs_n && !wr_full);
endproperty

assert property (valid_write_conditions)
  else $warning("ASSERTION FAILED: wr_en asserted when either cs_n was high or FIFO was full");

assert property (off_if_not_selected)
  else $warning("ASSERTION FAILED: wr_en asserted while chip not selected");

assert property (off_when_full)
  else $warning("ASSERTION FAILED: wr_en asserted when full");

endmodule