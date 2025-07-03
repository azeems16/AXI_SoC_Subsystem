module spi_fifo_i2c_top_tb;

parameter int DATA_WIDTH = 8;

logic                   spi_clk     ; // SPI Domain Master CLK
logic                   spi_wr_clk  ; // SPI Domain FIFO wrclk
logic                   spi_rst_n   ; // SPI Master Reset to SPI Slave and rdFIFO
logic                   spi_cs_n    ; // SPI Master Chip Select 
logic [DATA_WIDTH-1:0]  spi_tx_byte ; // TX Byte to be written to SPI Domain
logic                   spi_miso    ; 
logic                   spi_mosi    ;

logic                   i2c_clk     ; // I2C Domain Master CLK, FIFO rdclk   
logic                   i2c_rst_n   ; // I2C Master Reset to I2C Slave and rdFIFO
logic [DATA_WIDTH-1:0]  i2c_rx_byte ; // RX Byte to be read from I2C Domain
wire                    i2c_scl     ; // I2C i2c_scl inout
wire                    i2c_sda     ; // I2C SDA inout
logic                   scl_tb_drive;
logic                   sda_tb_drive;

assign i2c_scl = scl_tb_drive ? 1'b1 : 1'b0;
assign i2c_sda = sda_tb_drive ? 1'b0 : 1'bz;   
pullup(i2c_sda);

spi_fifo_i2c_top top (
    .spi_clk     (spi_clk)      ,
    .spi_wr_clk  (spi_wr_clk)   ,
    .spi_rst_n   (spi_rst_n)    ,
    .spi_cs_n    (spi_cs_n)     ,
    .spi_tx_byte (spi_tx_byte)  ,
    .spi_miso    (spi_miso)     ,
    .spi_mosi    (spi_mosi)     ,
    .i2c_clk     (i2c_clk)      ,
    .i2c_rst_n   (i2c_rst_n)    ,
    .i2c_scl     (i2c_scl)      ,
    .i2c_sda     (i2c_sda)      ,
    .i2c_rx_byte (i2c_rx_byte) 
);

// Testbench Tasks
task automatic write(input logic [DATA_WIDTH-1:0] tx_byte);
    spi_tx_byte = tx_byte;
    spi_cs_n    = 0;

    for (int i = 0; i < DATA_WIDTH; i++) begin
        spi_mosi = tx_byte[DATA_WIDTH - 1 - i];
        @(posedge spi_clk);
    end

    @(posedge spi_clk);
    spi_cs_n    = 1;
endtask

logic [DATA_WIDTH-1:0] rx_byte;
bit addr_ack_bit;
task automatic read(input logic [6:0] addr_bits);
    // Start Condition
    sda_tb_drive = 0;
    #1250;
    scl_tb_drive = 1;
    #1250;
    sda_tb_drive = 1;

    #600;
    // Address Phase - Master to Slave
    for (int i = 0; i < 9; i++) begin
        if (i < 7) begin
            if (i == 0 ) begin
                @(posedge i2c_clk);
                @(posedge i2c_clk);
            end
            scl_tb_drive = 0;
            sda_tb_drive = ~addr_bits[6 - i];   // Drive SDA
            #1250;
            scl_tb_drive = 1;    // i2c_scl bit transfer window, send on posedge of i2c_scl
            #1250;
            scl_tb_drive = 0;
            #1250;
        end
        else if (i == 7) begin
            scl_tb_drive = 0;            // send RW bit
            sda_tb_drive = 0;   // R == 1
            #1250;
            scl_tb_drive = 1;
            #1250;
            scl_tb_drive = 0;
        end
        else if (i == 8) begin
            scl_tb_drive = 0;
            sda_tb_drive = 0; // release SDA line to let slave drive ACK
            #1250;
            scl_tb_drive = 1;
            repeat (3) @(posedge i2c_clk); // ensure FSM transition & edge are consumed
            #50;
            addr_ack_bit = i2c_sda;
            #1200;
            scl_tb_drive = 0;
        end


    end

    #2500;
    // Data Phase - Slave to Master
    if (!addr_ack_bit) begin
            @(posedge i2c_clk);
            @(posedge i2c_clk);
        for (int i = 0; i < 9; i++) begin
            scl_tb_drive = 0;
            // sda_tb_drive = 0; // stop driving SDA
            #1250;
            scl_tb_drive = 1;
            rx_byte[7 - i] = i2c_sda;
            #1250;
            scl_tb_drive = 0;

            if (i == 8) begin
                scl_tb_drive = 0;
                sda_tb_drive = 0; // NACK
                #1250;
                scl_tb_drive = 1;
                #1250;
                scl_tb_drive = 0;             
            end
        end
    end
    else begin
        $display("[I2C Master]: No ACK after Address Phase");
    end

    #600;
    // Stop Condition
    @(posedge i2c_clk);
    @(posedge i2c_clk);
    scl_tb_drive = 0;
    sda_tb_drive = 1;
    #1250;
    scl_tb_drive = 1;
    #1250; 
    sda_tb_drive = 0;
    #1250; 
    scl_tb_drive = 0;
endtask

//  Clocks
initial #73  spi_clk    = 0;
initial #19  spi_wr_clk = 0;
initial #112 i2c_clk    = 0;

always #250 spi_clk    = ~spi_clk;
always #50  spi_wr_clk = ~spi_wr_clk;
always #151 i2c_clk    = ~i2c_clk;

// Initialization
initial begin
    spi_cs_n     =  1;
    spi_tx_byte  = '0;

    sda_tb_drive =  0;
    scl_tb_drive =  1;
end

// Stimulus
initial begin
    spi_rst_n   =  0;
    i2c_rst_n   =  0;
    #1500;
    spi_rst_n   = 1;
    i2c_rst_n   = 1;
    #300;

    // Writes
    for (int i = 0; i < 5; i++) begin
        write(8'hA0 + i);
    end

    // Reads
    for (int i = 0; i < 5; i++) begin
        read(7'h25);
    end
    
    #2500;
    $finish;
end

initial begin
    $dumpfile("spi_fifo_i2c_top_tb.vcd");
    $dumpvars(0, spi_fifo_i2c_top_tb);
    $dumpvars(0, spi_fifo_i2c_top_tb.top); // Dumps everything inside your DUT
end


endmodule