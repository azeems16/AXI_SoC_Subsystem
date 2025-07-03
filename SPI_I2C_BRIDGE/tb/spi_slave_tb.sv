`include "spi_sva.sv"
module spi_slave_tb;

logic sclk      ;
logic cs_n      ;
logic mosi      ;
logic wr_clk    ;
logic wr_rst_n  ;
logic rx_data   ;
logic wr_en     ;

spi_slave slave (
    .sclk      (sclk    ) ,
    .cs_n      (cs_n    ) ,
    .mosi      (mosi    ) ,
    .wr_clk    (wr_clk  ) ,
    .wr_rst_n  (wr_rst_n) ,
    .rx_data   (rx_data ) ,
    .wr_en     (wr_en   ) 
);

spi_sva u_sva (
  .sclk      (sclk    ),
  .cs_n      (cs_n    ),
  .mosi      (mosi    ),
  .wr_clk    (wr_clk  ),
  .wr_rst_n  (wr_rst_n),
  .wr_full   (/*TODO*/),
  .rx_data   (rx_data ),
  .wr_en     (wr_en   ),
);

always #2.5 wr_clk = ~wr_clk;

task automatic spi_send_byte();
  integer i;
  begin
    cs_n = 0;
    @(posedge wr_clk);
    for (i = 7; i >= 0; i--) begin
      mosi = $urandom_range(1,0);
      #5 sclk = 1; // rising edge
      #5 sclk = 0; // falling edge
    end
      #5 sclk = 1; // rising edge
      #5 sclk = 0; // falling edge

    #10;      // idle time before next transfer
    cs_n = 1; // end transfer
    #10;      // idle time before next transfer
  end
endtask

initial begin
    sclk   = 0;
    cs_n   = 1;
    mosi   = 0;
    wr_clk = 0;
end

initial begin
  // Reset logic
  wr_rst_n = 0;
  #20;
  wr_rst_n = 1;
  #20;

  // Send bytes
  spi_send_byte();
  spi_send_byte();
  #100;

  $finish;
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, spi_slave_tb); // or top module name
end

endmodule