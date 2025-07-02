module i2c_slave_tb;

logic       scl         ;     // from master
wire        sda_line    ;     // from master
logic       rd_clk      ;     // from fifo
logic       rd_rst_n    ;     // from fifo
logic [7:0] rd_data     ;     // from fifo
logic       rd_empty    ;     // from fifo
logic       rd_en       ;     // slave to fifo
logic       sda_tb_drive;

assign sda_line = sda_tb_drive ? 1'b0 : 1'bz;   
pullup(sda_line);
i2c_slave slave (
    .scl       (scl     ) ,
    .sda       (sda_line) ,
    .rd_clk    (rd_clk  ) ,
    .rd_rst_n  (rd_rst_n) ,
    .rd_data   (rd_data ) ,
    .rd_empty  (rd_empty) ,
    .rd_en     (rd_en   ) 
);

always #5 rd_clk = ~rd_clk;
logic [7:0] rx_byte;
bit ack_bit;
logic [6:0] addr_bits_probe;
logic ack_bit_probe;
task automatic i2c_read(input bit rw_bit, input logic [6:0] addr_bits);
    addr_bits_probe = addr_bits;
    // START
    sda_tb_drive = 0;   
    #5;
    scl          = 1;   
    #5;
    sda_tb_drive = 1;   
    #10;
    #30;
    // ADDR
    for (int i = 8; i > 0; i--) begin
        if (i >=2 ) begin
            @(posedge rd_clk);
            @(posedge rd_clk);
            scl = 0;
            sda_tb_drive = ~addr_bits[i-2];            
            #20;
            scl = 1;
            #20;
            scl = 0;
        end
        else if (i == 1) begin
            scl = 0;
            sda_tb_drive = 0;
            #20;
            scl = 1;
            #20;
            scl = 0;
        end
        else if (i == 0) begin
            scl = 0;
            sda_tb_drive = 0;
            #20;
            scl = 1;
            #20;
            ack_bit = sda_line;
            ack_bit_probe = ack_bit;
            #20;
            scl = 0;
        end
    end
    #30;

    //DATA
    if(rw_bit == 1 && ack_bit == 0) begin
        rd_empty = 1'b0;
        #5;

        for (int i = 8; i >= 0 ; i--) begin
            scl = 0;
            #20;
            scl = 1;
            #20;
            rx_byte[i] = sda_line;
            scl = 0;
            #20;
        end

        sda_tb_drive = 0;
        scl = 1;
        #20;
        scl = 0;
        rd_empty = 1'b1;
        #5;
    end

    #30;
    //STOP
    #20;
    @(posedge rd_clk);
    @(posedge rd_clk);
    scl          = 0;
    sda_tb_drive = 1; 
    #20;  
    scl          = 1;  
    #20;
    sda_tb_drive = 0;   
    #40;
    scl          = 0;   

endtask

initial begin
    // Initialize signals
    scl          = 0;
    sda_tb_drive = 0; // release SDA
    rd_clk       = 0;
    rd_data      = 8'hAD;  // data to be read by master
    rd_empty     = 0;      // simulate FIFO has data
    rd_rst_n     = 0;

    // Reset pulse
    #10;
    rd_rst_n = 1;

    // Wait for a few clock edges
    #20;

    // Perform an I2C read to slave at address 0x25
    i2c_read(1'b1, 7'h25);  // rw_bit=1 (read), addr=0x25
    $display("Read byte = %02h", rx_byte);
    #500;
    
    // Initialize signals
    rx_byte      = '0;
    scl          = 0;
    sda_tb_drive = 0; // release SDA
    rd_clk       = 0;
    rd_data      = 8'hB3;  // data to be read by master
    rd_empty     = 0;      // simulate FIFO has data
    rd_rst_n     = 0;

    // Reset pulse
    #10;
    rd_rst_n = 1;

    // Wait for a few clock edges
    #20;

    i2c_read(1'b1, 7'h25);  // rw_bit=1 (read), addr=0x25
    $display("Read byte = %02h", rx_byte);
    #500;
        
    // Initialize signals
    rx_byte      = '0;
    scl          = 0;
    sda_tb_drive = 0; // release SDA
    rd_clk       = 0;
    rd_data      = 8'hB3;  // data to be read by master
    rd_empty     = 0;      // simulate FIFO has data
    rd_rst_n     = 0;

    // Reset pulse
    #10;
    rd_rst_n = 1;

    // Wait for a few clock edges
    #20;
    
    i2c_read(1'b1, 7'h25);  // rw_bit=1 (read), addr=0x25
    $display("Read byte = %02h", rx_byte);

    // Done
    #100;
    $finish;
end


initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, i2c_slave_tb); // or top module name
end

endmodule