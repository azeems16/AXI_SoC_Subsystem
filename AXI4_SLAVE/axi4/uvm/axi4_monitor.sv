class axi_monitor extends uvm_monitor;
`uvm_component_utils(axi_monitor)

uvm_analysis_port#(axi_txn#(32,32)) send;
virtual axi4_intf.monitor vif;

function new(input string name = "monitor", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    send = new("send", this);
    if(!uvm_config_db#(virtual axi4_intf.monitor)::get(this, "", "vif", vif))
    `uvm_error("MON","Unable to access Interface");
endfunction

virtual task monitor_write();
    forever begin
        axi_txn#(32,32) trm;
        trm = axi_txn#(32,32)::type_id::create("trm", this);
        @(posedge vif.ACLK);
        if (vif.AWVALID && vif.AWREADY) begin   // if instead of wait as this is entirely passive
            trm.addr     = vif.AWADDR;
            trm.len      = vif.AWLEN;
            trm.size     = vif.AWSIZE;
            trm.burst    = vif.AWBURST;
            trm.wdata    = new[vif.AWLEN+1];
            trm.is_write = 1;
        
            for (int i = 0; i <= vif.AWLEN; i++) begin  // use wait instead of if so we dont miss a beat
                wait(vif.WVALID && vif.WREADY);
                trm.wdata[i] = vif.WDATA;
                trm.wstrb    = vif.WSTRB;
                @(posedge vif.ACLK);
            end

            wait (vif.BVALID && vif.BREADY); 
            @(posedge vif.ACLK);
            trm.resp = vif.BRESP;

            send.write(trm);
        end
    end
endtask

virtual task monitor_read();
    forever begin
        axi_txn#(32,32) trm;
        trm = axi_txn#(32,32)::type_id::create("trm", this);
        wait (vif.ARVALID && vif.ARREADY); 
        @ (posedge vif.ACLK);
        trm.addr     = vif.ARADDR;
        trm.len      = vif.ARLEN;
        trm.size     = vif.ARSIZE;
        trm.burst    = vif.ARBURST;
        trm.is_write = 0;
        trm.rdata = new[vif.ARLEN + 1];
        for (int i = 0; i <= vif.ARLEN; i++) begin
            wait(vif.RREADY && vif.RVALID);
            trm.rdata[i] = vif.RDATA;
            if (vif.RLAST) begin
                trm.resp = vif.RRESP;
            end
            @ (posedge vif.ACLK);
        end
        send.write(trm);
    end
endtask

virtual task run_phase(uvm_phase phase);
    wait (!vif.ARESETN);
    wait (vif.ARESETN);
    fork
        monitor_write();
        monitor_read();
    join_none
endtask

endclass



