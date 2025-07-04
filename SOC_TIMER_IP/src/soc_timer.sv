import soc_timer_reg_pkg::*;

module soc_timer #(
    parameter integer ADDR_WIDTH   = 5,           // 16B address space = 6 registers max
    parameter integer DATA_WIDTH   = 32,
    parameter integer TIMER_WIDTH  = 32,
    parameter         BASE_ADDR    = 32'h0000_0000
)(
    // AXI-Lite Slave Interface
    input  logic                      ACLK,
    input  logic                      ARESETN,
 
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
 
    // Output: interrupt line 
    output logic                      irq,
 
    output bit                        timer_event
);

logic awc_hs, wc_hs, ar_hs;
logic [1:0] bresp, rresp;

logic [ADDR_WIDTH-1:0] aw_addr_reg, ar_addr_reg;
logic [DATA_WIDTH-1:0] wdata_reg, rdata_reg;

logic [DATA_WIDTH-1:0] timer_val_reg;
logic [DATA_WIDTH-1:0] control_reg;
logic [DATA_WIDTH-1:0] int_clear_reg;

logic write_en, timer_en;
assign write_en = awc_hs && wc_hs;

bit irq_flag;
bit first_cntdwn;
logic [TIMER_WIDTH-1:0] counter;
// Register Updating/Handshake Tracking Always Block
always @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        AWREADY       <=  0;
        WREADY        <=  0;

        BRESP         <=  0;
        BVALID        <=  0;

        ARREADY       <=  0;

        RDATA         <= '0;
        RRESP         <= '0;
        RVALID        <=  0;

        awc_hs        <=  0;
        wc_hs         <=  0;
        ar_hs         <=  0;
        
        bresp         <= '0;
        rresp         <= '0;

        aw_addr_reg   <= '0;
        ar_addr_reg   <= '0;
        wdata_reg     <= '0;
        rdata_reg     <= '0;

        timer_val_reg <= '0;
        control_reg   <= '0;
        int_clear_reg <= '0;

        timer_en      <=  0;
    end
    else begin
    // Write Path
        if (AWVALID && !BVALID && !awc_hs) begin
            AWREADY     <= 1;
            awc_hs      <= 1;
            aw_addr_reg <= AWADDR;
        end

        if (WVALID && !BVALID && !wc_hs) begin  
            WREADY    <= 1;                  
            wc_hs     <= 1;                     
            wdata_reg <= WDATA;
        end   

        // Pulldowns
        if (awc_hs) begin               
            AWREADY <= 0;      
        end

        if (wc_hs) begin                 
            WREADY <= 0;        
        end

        if (BREADY && BVALID) begin          
            BVALID <= 0;        
            awc_hs <= 0;
            wc_hs  <= 0;
        end

        if (write_en) begin
            bresp <= 2'b00; // OKAY
            case(aw_addr_reg)
                LOAD_REG_OFFSET : begin
                    timer_val_reg <= wdata_reg;
                    first_cntdwn  <= 0;
                end

                CONTROL_REG_OFFSET : begin
                    control_reg <= wdata_reg;
                end

                INT_CLEAR_REG_OFFSET : begin
                    int_clear_reg <= wdata_reg;
                end
                default: bresp <= 2'b10; // SLVERR
            endcase

            awc_hs <= 0;  
            wc_hs  <= 0;  
            BVALID <= 1;  
            BRESP  <= bresp; 
        end
    end

    // Read Path
    if (ARVALID && !ar_hs) begin 
        ARREADY     <= 1;         
        ar_hs       <= 1;
        ar_addr_reg <= ARADDR;
    end

    if (ar_hs && RREADY) begin           
        rresp <= 2'b00; // OKAY
        RVALID <= 1;                  
        case(ar_addr_reg)
            CONTROL_REG_OFFSET : begin
                RDATA <= control_reg;
            end

            COUNTER_REG_OFFSET : begin
                RDATA <= counter;
            end

            INT_STATUS_REG_OFFSET: begin
                RDATA <= {31'd0, irq_flag};
            end

            default: begin
                RDATA <= '0;
                rresp <= 2'b10; //SLVERR
            end
        endcase
        
        RRESP  <= rresp;      
        ar_hs  <=  0;                  
    end

    if (ar_hs) begin
        ARREADY <= 0;
    end

    if (RREADY && RVALID) begin
        RVALID <= 0;
    end
end

// Countdown Timer Always Block
always @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        counter      <= 0;
        irq_flag     <= 0;
        timer_en     <= 0;
        first_cntdwn <= 0;
        timer_event  <= 0;
    end
    else begin
        // Timer Enable, Counter Loading
        if (control_reg[CTRL_ENABLE_BIT] && !timer_en && !first_cntdwn) begin
            counter  <= timer_val_reg;
            timer_en <= 1;
        end

        // Timer Countdown
        timer_event <= 0;
        if (timer_en) begin
            if (counter > 0) begin
                counter <= counter - 1;
            end
            else if (counter == 0) begin
                if(control_reg[CTRL_AUTO_RELOAD_BIT]) begin
                    counter     <= timer_val_reg;
                    timer_event <= 1;
                end
                else if (!control_reg[CTRL_AUTO_RELOAD_BIT]) begin
                    timer_en     <= 0;
                    timer_event  <= 1;
                    first_cntdwn <= 1;
                end
                irq_flag     <= 1;
            end
        end

        // Interrupt
        if (int_clear_reg[IRQ_FLAG_BIT]) begin
            irq_flag <= 0;
        end
    end
end

assign irq = (irq_flag && !control_reg[CTRL_IRQ_MASK_BIT]);

// Assertions
property maskon_irqoff;
    @(posedge ACLK) disable iff (!ARESETN)
    control_reg[CTRL_IRQ_MASK_BIT] |-> !irq;
endproperty

property irqon_when_timerexpire_maskoff;
    @(posedge ACLK) disable iff (!ARESETN)
    irq |-> !control_reg[CTRL_IRQ_MASK_BIT] && (counter == 0);
endproperty

property oneshot_timer_disables;
    @(posedge ACLK) disable iff (!ARESETN)
    (!control_reg[CTRL_AUTO_RELOAD_BIT] && counter == 0 && timer_en) |-> ##1 !timer_en;
endproperty

property autoreload_restarts_timer;
    @(posedge ACLK) disable iff (!ARESETN)
    (control_reg[CTRL_AUTO_RELOAD_BIT] && counter == 0 && timer_en) |-> ##1 counter == timer_val_reg;
endproperty

property no_read_from_write_only;
    @(posedge ACLK) disable iff (!ARESETN)
    (ARVALID && ARREADY && ARADDR == INT_CLEAR_REG_OFFSET) |-> 0;
endproperty

property no_write_to_read_only;
    @(posedge ACLK) disable iff (!ARESETN)
    (AWVALID && AWREADY && 
     (AWADDR == INT_STATUS_REG_OFFSET || AWADDR == COUNTER_REG_OFFSET)) |-> 0;
endproperty

// When IRQ mask bit is set, IRQ must be low
assert property (maskon_irqoff);

// When counter hits 0 and IRQ is unmasked, IRQ should be high
assert property (irqon_when_timerexpire_maskoff);

// One-shot mode disables timer after expiry
assert property (oneshot_timer_disables);

// Auto-reload mode reloads timer after expiry
assert property (autoreload_restarts_timer);

// Clear register is write-only: reading it is illegal
assert property (no_read_from_write_only);

// Interrupt status and counter registers are read-only: writing is illegal
assert property (no_write_to_read_only);

endmodule
