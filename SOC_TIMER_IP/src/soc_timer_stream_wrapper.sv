module soc_timer_stream_wrapper #(
    parameter ADDR_WIDTH  = 5,
    parameter DATA_WIDTH  = 32,
    parameter TIMER_WIDTH = 32
)(
    input  logic                      ACLK,
    input  logic                      ARESETN,

    // AXI-Lite Slave Interface (copied from soc_timer)
    input  logic [ADDR_WIDTH-1:0]     AWADDR,
    input  logic                      AWVALID,
    output logic                      AWREADY,

    input  logic [DATA_WIDTH-1:0]     WDATA,
    input  logic [(DATA_WIDTH/8)-1:0] WSTRB,
    input  logic                      WVALID,
    output logic                      WREADY,

    output logic [1:0]                BRESP,
    output logic                      BVALID,
    input  logic                      BREADY,
  
    input  logic [ADDR_WIDTH-1:0]     ARADDR,
    input  logic                      ARVALID,
    output logic                      ARREADY,
  
    output logic [DATA_WIDTH-1:0]     RDATA,
    output logic [1:0]                RRESP,
    output logic                      RVALID,
    input  logic                      RREADY,

    // IRQ line
    output logic                      irq,

    // New AXIS Output Ports
    output logic [DATA_WIDTH-1:0]     TDATA,
    output logic                      TVALID,
    input  logic                      TREADY,
    output logic                      TLAST,

    input  bit                        timer_event
);

soc_timer #(
    .ADDR_WIDTH     (ADDR_WIDTH)     ,
    .DATA_WIDTH     (DATA_WIDTH)     ,
    .TIMER_WIDTH    (TIMER_WIDTH)
) u_timer (
    .ACLK           (ACLK)           ,
    .ARESETN        (ARESETN)        ,
    .AWADDR         (AWADDR)         ,
    .AWVALID        (AWVALID)        ,
    .AWREADY        (AWREADY)        ,
    .WDATA          (WDATA)          ,
    .WSTRB          (WSTRB)          ,
    .WVALID         (WVALID)         ,
    .WREADY         (WREADY)         ,
    .BRESP          (BRESP)          ,
    .BVALID         (BVALID)         ,
    .BREADY         (BREADY)         ,
    .ARADDR         (ARADDR)         ,
    .ARVALID        (ARVALID)        ,
    .ARREADY        (ARREADY)        ,
    .RDATA          (RDATA)          ,
    .RRESP          (RRESP)          ,
    .RVALID         (RVALID)         ,
    .RREADY         (RREADY)         ,
    .irq            (irq)            ,

    .timer_event    (timer_event)
);

logic [31:0] event_counter;
logic        send_event;
always @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        TVALID        <=  0;
        TDATA         <= '0;
        event_counter <= '0;
        send_event    <=  0;
    end
    else begin
        if (timer_event) begin
            event_counter <= event_counter + 1;
            send_event    <= 1;
        end

        if (send_event && !TVALID) begin
            TVALID <= 1;
            TDATA  <= event_counter;
        end

        if (TVALID && TREADY) begin
            TVALID     <= 0;
            send_event <= 0;
        end
    end
end

assign TLAST = 1'b1;

endmodule