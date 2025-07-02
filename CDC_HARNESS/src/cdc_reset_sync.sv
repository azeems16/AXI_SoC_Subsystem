module cdc_reset_sync #(
  parameter int SYNC_DEPTH = 2
) (
  input  logic dst_clk,
  input  logic rst_n_async,
  output logic rst_n_sync
);

  logic [SYNC_DEPTH-1:0] sync_reg;

  always_ff @(posedge dst_clk or negedge rst_n_async) begin
    if (!rst_n_async) begin
      sync_reg <= '0;                               // we assert the async reset
    end else begin
      sync_reg <= {sync_reg[SYNC_DEPTH-2:0], 1'b1}; // make deassert of rst to propagate through chain of synchronizers for it to eventually settle if metastable, also to filter any glitch
    end
  end

  assign rst_n_sync = sync_reg[SYNC_DEPTH-1];

endmodule