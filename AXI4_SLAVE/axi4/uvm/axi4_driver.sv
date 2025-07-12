class axi4_driver extends uvm_driver#(axi_txn#(32,32));
`uvm_component_utils(axi4_driver)

virtual axi4_intf.driver vif;
axi_txn#(32,32) tr;

function new(input string name = "axi4_driver", uvm_component parent = null);
    super.new(name, parent);
endfunction

virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = axi_txn#(32, 32)::type_id::create("tr");

    if(!uvm_config_db#(virtual axi4_intf.driver)::get(this,"","vif",vif)) begin
    `uvm_error("DRV","Unable to access Interface");
    end
endfunction

task reset_dut();
    repeat(5) begin
        vif.ARESETN <=  0;
        vif.AWADDR  <= '0;
        vif.AWLEN   <= '0;
        vif.AWSIZE  <= '0;
        vif.AWBURST <= '0;
        vif.AWVALID <= '0;

        vif.WDATA   <= '0;
        vif.WSTRB   <= '1;
        vif.WVALID  <=  0;
        vif.WLAST   <=  0;

        vif.BREADY  <=  0;

        vif.ARADDR  <= '0;
        vif.ARLEN   <= '0;
        vif.ARSIZE  <= '0;
        vif.ARBURST <= '0;
        vif.ARVALID <= '0;

        vif.RREADY  <=  0;
        `uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM);
        @(posedge vif.ACLK);
    end

    // Release reset
    vif.ARESETN <= 1;
    `uvm_info("DRV", "System Reset : deasserted", UVM_LOW)
endtask

task drive_write(axi_txn#(32, 32) tr);
    logic [31:0] wdata[]; 
    wdata = tr.wdata;
    fork
        begin
            @(posedge vif.ACLK); // latch, then assert VALID , both at clock edge
            vif.AWADDR  <= tr.addr;
            vif.AWLEN   <= tr.len;
            vif.AWSIZE  <= tr.size;
            vif.AWBURST <= tr.burst;
            vif.AWVALID <= 1;
            
            wait (vif.AWREADY && vif.AWVALID);  // wait for handshake
            @(posedge vif.ACLK); // deassert VALID at next clock edge
            vif.AWVALID <= 0;
        end

        begin
            for (int i = 0; i <= tr.len; i++) begin
                @(posedge vif.ACLK);            // latch, assert VALID, both at clock edge
                vif.WDATA    <= wdata[i];
                vif.WSTRB    <= tr.wstrb;
                vif.WLAST    <= (i == tr.len);
                vif.WVALID   <= 1;

                wait (vif.WREADY && vif.WVALID);  // wait for handshake
                @(posedge vif.ACLK );
                vif.WVALID <= 0;    // deassert VALID at next clock edge
            end
            @(posedge vif.ACLK);    
            vif.WLAST  <= 0;
        end
    join
    
    @(posedge vif.ACLK);    //once write_en == 1, assert BREADY at clock edge
    vif.BREADY <= 1;
    wait (vif.BVALID && vif.BREADY);      // wait for handshake
    tr.resp <= vif.BRESP;  // apply resp from intf to transaction obj
    @(posedge vif.ACLK);
    vif.BREADY <= 0;        // deassert BREADY at clock edge
endtask

task drive_read(axi_txn#(32, 32) tr);
    tr.rdata = new[tr.len + 1];
    @(posedge vif.ACLK);    // latch, assert ARVALID at posedge of clock
    vif.ARADDR  <= tr.addr;
    vif.ARLEN   <= tr.len;
    vif.ARSIZE  <= tr.size;
    vif.ARBURST <= tr.burst;
    vif.ARVALID <= 1;
    wait (vif.ARREADY && vif.ARVALID);  // wait for handshake
    
    @(posedge vif.ACLK);
    vif.ARVALID <= 0;   // deassert ARVALID
    vif.RREADY  <= 1;   // read_en == 1, assert RREADY 
    
    for (int i = 0; i <= tr.len; i++) begin
        wait(vif.RVALID && vif.RREADY); // must wait for handshake before assigning RDATA
        @(posedge vif.ACLK);
        tr.rdata[i]  = vif.RDATA;
        if (vif.RLAST) tr.resp   <= vif.RRESP; // on RLAST, assign resp 
    end

    @ (posedge vif.ACLK);
    vif.RREADY <= 0;
endtask

virtual task run_phase(uvm_phase phase);
    reset_dut();
    forever begin
        seq_item_port.get_next_item(tr);
        if(tr.is_write) begin
            drive_write(tr);
        end
        else begin
            drive_read(tr);
        end
        seq_item_port.item_done(tr);
    end
endtask

endclass
            