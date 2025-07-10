class axi4_scoreboard extends uvm_scoreboard
`uvm_component_utils(axi4_scoreboard)

uvm_analysis_imp#(axi_txn#(32,32), axi4_scoreboard) recv;

function new(input string name = "axi4_scoreboard", uvm_component parent = null);
    super.new(name, parent);
endfunction

virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    recv = new("recv", this);
endfunction

axi_txn#(32,32) write_q[$]; // write queue
axi_txn#(32,32) read_q[$];  // read queue

virtual function void write(axi_txn#(32,32) tr);
    if (tr.is_write) begin
        write_q.push_back(tr);
        `uvm_info("SCO", $sformatf("Captured WRITE txn: addr=0x%08h, len=%0d, resp=%0h", 
                    tr.addr, tr.len, tr.resp), UVM_MEDIUM);
    end 
    else begin
        bit match_found = 0;

        for (int i = 0; i < write_q.size(); i++) begin
            if (write_q[i].addr == tr.addr) begin
                match_found = 1;

                for (int j = 0; j <= tr.len; j++) begin
                    if (write_q[i].wdata[j] !== tr.rdata[j]) begin
                        `uvm_error("SCO", $sformatf("Mismatch @ beat %0d: expected=0x%08h, got=0x%08h", 
                            j, write_q[i].wdata[j], tr.rdata[j]));
                    end
                    else begin
                        `uvm_info("SCO", $sformatf("Match @ beat %0d: 0x%08h", j, tr.rdata[j]), UVM_LOW);
                    end
                end

                write_q.delete(i);      
                break;
            end
        end

        if (!match_found) begin
            `uvm_info("SCO", $sformatf("No match found for READ txn: addr=0x%08h, len=%0d, resp=%0h", 
                tr.addr, tr.len, tr.resp), UVM_MEDIUM);
        end
    end
endfunction


endclass