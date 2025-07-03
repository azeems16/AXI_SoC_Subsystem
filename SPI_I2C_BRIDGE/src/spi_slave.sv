module spi_slave #(
  parameter DATA_WIDTH = 8  // One SPI frame = 1 byte
) (
  input  logic        sclk      , // SPI clock (from master)
  input  logic        cs_n      , // Active-low chip select
  input  logic        mosi      , // Master Out, Slave In
  input  logic        wr_clk    , // Write clock (system domain)
  input  logic        wr_rst_n  , // Write domain reset
  input  logic        wr_full   , // Write full from FIFO
  output logic [7:0]  rx_data   , // Output data byte (valid when wr_en asserted)
  output logic        wr_en       // Write enable for FIFO
);

logic [7:0] shift_reg;
logic prev_sclk, sclk_meta, sclk_sync, sclk_rising;
logic [3:0] bit_count;
always_ff @(posedge wr_clk) begin
    sclk_meta <= sclk;       // 1st stage
    sclk_sync <= sclk_meta;  // 2nd stage: now use this
    prev_sclk <= sclk_sync;
end

assign sclk_rising = ~prev_sclk & sclk_sync;    // detect low to rise

always_ff @ (posedge wr_clk or negedge wr_rst_n) begin
    // Reset Logic
    if(~wr_rst_n) begin
        wr_en     <= '0;
        rx_data   <= '0;
        shift_reg <= '0;
        bit_count <= '0;
    end
    else begin
        wr_en <= 1'b0;
        if(!cs_n) begin
            if(sclk_rising && !wr_full) begin
                if (bit_count < DATA_WIDTH) begin
                    shift_reg <= {shift_reg[6:0], mosi};
                    bit_count <= bit_count + 1;
                end
                else begin
                    rx_data   <= shift_reg;
                    wr_en     <= 1'b1;
                    bit_count <= '0;
                end
            end
            else begin
                $display("Error: FIFO is currently full");
                // TODO: add the byte drop 
            end
        end
        else if (cs_n) begin
            bit_count <= '0;
        end
    end
end

endmodule
