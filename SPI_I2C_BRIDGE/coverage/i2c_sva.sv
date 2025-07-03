module i2c_sva (
  input logic        rd_clk,
  input logic        scl,
  input logic        sda,
  input logic        rd_rst_n,
  input logic [7:0]  rd_data,
  input logic        rd_empty,
  input logic        rd_en
);

property no_read_when_empty;
    @(posedge rd_clk) disable iff (!rd_rst_n)
    rd_empty |-> !rd_en;
endproperty

property no_toggle_unless_reading;
    @(posedge rd_clk) disable iff (!rd_rst_n)
    !rd_en |-> $stable(scl) && $stable(sda);
endproperty

assert property (no_read_when_empty)
  else $fatal("ASSERTION FAILED: rd_en asserted while rd_empty is high");

assert property (no_toggle_unless_reading)
  else $fatal("ASSERTION FAILED: scl/sda changed when rd_en was low");

endmodule
