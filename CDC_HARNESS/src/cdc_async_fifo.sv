// cdc_async_fifo.sv
// ---------------------------------------------------------
// Purpose: Asynchronous FIFO skeleton
//           - Separate write and read clocks
//           - Dual clock crossing FIFO
// ---------------------------------------------------------

module cdc_async_fifo #(
  parameter int DATA_WIDTH = 8,
  parameter int ADDR_WIDTH = 3  // Depth = 2^ADDR_WIDTH
) (
  // Write domain ports
  input  logic                  wr_clk   ,
  input  logic                  wr_rst_n ,
  input  logic [DATA_WIDTH-1:0] wr_data  ,
  input  logic                  wr_en    ,
  output logic                  wr_full  ,

  // Read domain ports
  input  logic                  rd_clk   ,
  input  logic                  rd_rst_n ,
  output logic [DATA_WIDTH-1:0] rd_data  ,
  input  logic                  rd_en    ,
  output logic                  rd_empty
);

// Memory and Pointers
logic [DATA_WIDTH-1:0] memory [(1 << ADDR_WIDTH)-1:0];
logic [ADDR_WIDTH:0] wr_ptr; // MSB: wrap around indicator, other bits = pointer addressor 
logic [ADDR_WIDTH:0] rd_ptr; // MSB: wrap around indicator, other bits = pointer addressor 
//Async Gray Pointers
logic [ADDR_WIDTH:0] gray_wr_ptr_async; 
logic [ADDR_WIDTH:0] gray_rd_ptr_async; 
//Synced Gray Pointers
logic [ADDR_WIDTH:0] gray_wr_ptr_sync; 
logic [ADDR_WIDTH:0] gray_rd_ptr_sync; 
//Synced Bin Pointers
logic [ADDR_WIDTH:0] bin_wr_ptr_sync; 
logic [ADDR_WIDTH:0] bin_rd_ptr_sync; 

function logic [ADDR_WIDTH:0] bin2gray(logic [ADDR_WIDTH:0] bin_ptr);
    logic [ADDR_WIDTH:0] gray_ptr;
    // Top-Down conversion
    gray_ptr[ADDR_WIDTH] = bin_ptr[ADDR_WIDTH];
    for(int i = ADDR_WIDTH-1 ; i >=0; i--) begin
        gray_ptr[i] = bin_ptr[i] ^ bin_ptr[i+1];
    end

    return gray_ptr;
endfunction

function logic [ADDR_WIDTH:0] gray2bin(logic [ADDR_WIDTH:0] gray_ptr);
    logic [ADDR_WIDTH:0] bin_ptr;
    //Top-Down conversion
    bin_ptr[ADDR_WIDTH] = gray_ptr[ADDR_WIDTH];
    for (int i = ADDR_WIDTH-1 ; i >=0; i--) begin
        bin_ptr[i] = bin_ptr[i+1] ^ gray_ptr[i];
    end

    return bin_ptr;
endfunction

// Write Logic
always_ff @ (posedge wr_clk or negedge wr_rst_n) begin
    logic [ADDR_WIDTH:0] wr_ptr_next;   // to ensure this isn't synthesized unnecessarily (helper register)
    wr_ptr_next = wr_ptr + 1;
    
    if (!wr_rst_n) begin
        wr_ptr  <= '0;
        wr_full <= '0;
    end
    else begin
        if (wr_full) begin
            wr_full <= (wr_ptr[ADDR_WIDTH] != bin_rd_ptr_sync[ADDR_WIDTH]) && (wr_ptr[ADDR_WIDTH-1:0] == bin_rd_ptr_sync[ADDR_WIDTH-1:0]);
        end
        else begin
            if (wr_en && !wr_full) begin
                memory[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
                wr_ptr <= wr_ptr_next;
            end
            else begin
//                 $display("[CDC ASYNC FIFO]: FIFO is full.");
            end
            wr_full <= (wr_ptr_next[ADDR_WIDTH] != bin_rd_ptr_sync[ADDR_WIDTH]) && (wr_ptr_next[ADDR_WIDTH-1:0] == bin_rd_ptr_sync[ADDR_WIDTH-1:0]);
        end
    end
end

// CDC: Wr Ptr Synced to Rd Clk Domain
assign gray_wr_ptr_async = bin2gray(wr_ptr); // convert write pointer to gray code
cdc_2flop_sync write_ptr_synchronizer(       // sync write pointer to read domain
    .clk        (rd_clk),
    .rst_n      (rd_rst_n),
    .d_async    (gray_wr_ptr_async),
    .d_sync     (gray_wr_ptr_sync)
);
assign bin_wr_ptr_sync = gray2bin(gray_wr_ptr_sync); // convert gray code write to bin for read domain usage

// Read Logic
always_ff @ (posedge rd_clk or negedge rd_rst_n) begin
    logic [ADDR_WIDTH:0] rd_ptr_next;   // to ensure this isn't synthesized unnecessarily (helper register)
    rd_ptr_next = rd_ptr + 1;
    
    if(!rd_rst_n) begin
        rd_ptr   <= '0;
        rd_empty <= '1;
        rd_data  <= '0;
    end
      else begin
        if (rd_empty) begin
          rd_empty <= (rd_ptr == bin_wr_ptr_sync);
        end
        else begin
            if (rd_en && !rd_empty) begin
                rd_data <= memory[rd_ptr[ADDR_WIDTH-1:0]];
                rd_ptr  <= rd_ptr_next;
            end
            else begin
                $display("[CDC ASYNC FIFO]: FIFO is empty");
            end
            rd_empty <= (rd_ptr_next == bin_wr_ptr_sync);
        end
    end
end

// CDC: Rd Ptr Synced to Write Clk Domain
assign gray_rd_ptr_async = bin2gray(rd_ptr);    // convert read pointer to gray code
cdc_2flop_sync read_ptr_synchronizer (          // sync read pointer to write domain
    .clk        (wr_clk),
    .rst_n      (wr_rst_n),
    .d_async    (gray_rd_ptr_async),
    .d_sync     (gray_rd_ptr_sync)
);
assign bin_rd_ptr_sync = gray2bin(gray_rd_ptr_sync);    // convert gray code read back to bin for write domain usage

endmodule
