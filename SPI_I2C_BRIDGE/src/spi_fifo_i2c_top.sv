module spi_fifo_i2c_top #(
  parameter DATA_WIDTH = 8
)(
  // TX Side (SPI Domain)
  input  logic                   spi_clk     ,
  input  logic                   spi_wr_clk  ,
  input  logic                   spi_rst_n   ,
  input  logic                   spi_cs_n    ,
  input  logic [DATA_WIDTH-1:0]  spi_tx_byte ,
  input  logic                   spi_mosi    ,
  output logic                   spi_miso    , // unused

  // RX Side (I2C Domain)
  input  logic                   i2c_clk     ,
  input  logic                   i2c_rst_n   ,
  inout  logic                   i2c_scl     ,
  inout  logic                   i2c_sda     ,
  output logic [DATA_WIDTH-1:0]  i2c_rx_byte 
);

logic [DATA_WIDTH-1:0] data_spi_to_fifo;
logic [DATA_WIDTH-1:0] rd_data_fifo_i2c;

spi_slave spi_slave (
  .sclk     (spi_clk)             ,   
  .cs_n     (spi_cs_n)            ,
  .mosi     (spi_mosi)            ,
  .wr_clk   (spi_wr_clk)          ,
  .wr_rst_n (spi_rst_n)           ,
  .wr_full  (wr_full_fifo_to_spi) ,
  .rx_data  (data_spi_to_fifo)    ,
  .wr_en    (wr_en_spi_to_fifo) 
);

cdc_harness async_fifo (
  .wr_clk         (spi_wr_clk)          ,
  .wr_rst_n_async (spi_rst_n)           ,
  .wr_data        (data_spi_to_fifo)    ,
  .wr_en          (wr_en_spi_to_fifo)   ,
  .wr_full        (wr_full_fifo_to_spi) ,

  .rd_clk         (i2c_clk)             ,
  .rd_rst_n_async (i2c_rst_n)           ,
  .rd_data        (rd_data_fifo_i2c)    ,
  .rd_en          (rd_en_i2c_fifo)      ,
  .rd_empty       (rd_empty_fifo_i2c)
);


i2c_slave i2c_slave (
  .scl          (i2c_scl)               ,     
  .sda          (i2c_sda)               ,     
  .rd_clk       (i2c_clk)               ,       
  .rd_rst_n     (i2c_rst_n)             ,
  .rd_data      (rd_data_fifo_i2c)      , 
  .rd_empty     (rd_empty_fifo_i2c)     ,
  .rd_en        (rd_en_i2c_fifo) 
);

assign i2c_rx_byte = rd_data_fifo_i2c;
endmodule