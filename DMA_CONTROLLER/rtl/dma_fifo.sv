module dma_data_fifo #(
    parameter DATA_WIDTH = 32,
    parameter DEPTH      = 16  // Number of data words the FIFO can hold
)(
    input  wire                  clk,
    input  wire                  rst_n,

    // Write side (from AXI Read FSM)
    input  wire                  wr_en,
    input  wire [DATA_WIDTH-1:0] wr_data,
    output wire                  full,

    // Read side (to AXI Write FSM)
    input  wire                  rd_en,
    output wire [DATA_WIDTH-1:0] rd_data,
    output wire                  empty
);

localparam PTR_WIDTH = $clog2(DEPTH) + 1; // +1 for wraparound

logic [DATA_WIDTH-1:0] memory [DEPTH-1:0];
logic [PTR_WIDTH -1:0] wr_ptr, rd_ptr;
logic [DATA_WIDTH-1:0] rd_data_reg;

integer i;
always_ff @ (posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_ptr <= 0;
    end
    else begin
        if (wr_en) begin
            if (!full) begin
                memory[wr_ptr[PTR_WIDTH-2:0]] <= wr_data;
                wr_ptr<= wr_ptr + 1;
            end
        end
    end
end

always_ff @ (posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rd_ptr <= 0;
    end
    else begin
        if (rd_en) begin
            if (!empty) begin
                rd_data_reg <= memory[rd_ptr[PTR_WIDTH-2:0]];
                rd_ptr <= rd_ptr + 1;
            end
        end
    end
end

assign rd_data = rd_data_reg;

assign full  = (wr_ptr[PTR_WIDTH-1] != rd_ptr[PTR_WIDTH-1]) && (wr_ptr[PTR_WIDTH-2:0] == rd_ptr[PTR_WIDTH-2:0]);
assign empty = (wr_ptr == rd_ptr);
endmodule

