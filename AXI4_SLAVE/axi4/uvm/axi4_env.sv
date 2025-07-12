class axi4_env extends uvm_env;
`uvm_component_utils(axi4_env)

axi4_agent agent;
axi4_scoreboard sco;

function new(input string name = "env", uvm_component parent = null);   
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = axi4_agent::type_id::create("agent", this);
    sco   = axi4_scoreboard::type_id::create("sco", this);
endfunction

function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agent.mon.send.connect(sco.recv);
endfunction

endclass