class single_beat_fixed_write extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(single_beat_fixed_write)

axi_txn#(32, 32) txn;

function new(string name = "single_beat_fixed_write");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 1;
                len      == 0;
                burst    == 2'b00;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_fixed_write extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_fixed_write)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_fixed_write");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 1;
                len   inside {[1:8]};
                burst == 2'b00;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_incr_write extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_incr_write)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_incr_write");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 1;
                len   inside {[1:8]};
                burst == 2'b01;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_wrap_write extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_wrap_write)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_wrap_write");
    super.new(name);
endfunction

virtual task body();
    int wrap_lengths[] = '{1, 3, 7, 15};
    foreach (wrap_lengths[i]) begin
        txn = axi_txn#(32,32)::type_id::create("txn");
        start_item(txn);
        assert(txn.randomize() with {
            is_write == 1;
            len      == wrap_lengths[i];
            burst    == 2'b10;
        });
        finish_item(txn);
    end
endtask

endclass

class single_beat_fixed_read extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(single_beat_fixed_read)

axi_txn#(32, 32) txn;

function new(string name = "single_beat_fixed_read");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 0;
                len      == 0;
                burst    == 2'b00;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_fixed_read extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_fixed_read)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_fixed_read");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 0;
                len   inside {[1:8]};
                burst == 2'b00;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_incr_read extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_incr_read)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_incr_read");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            txn = axi_txn#(32,32)::type_id::create("txn");
            start_item(txn);
            assert(txn.randomize() with {
                is_write == 0;
                len   inside {[1:8]};
                burst == 2'b01;
            });
            finish_item(txn);
        end
endtask

endclass

class multi_beat_wrap_read extends uvm_sequence#(axi_txn#(32, 32));
`uvm_object_utils(multi_beat_wrap_read)

axi_txn#(32, 32) txn;

function new(string name = "multi_beat_wrap_read");
    super.new(name);
endfunction

virtual task body();
    int wrap_lengths[] = '{1, 3, 7, 15};
    foreach (wrap_lengths[i]) begin
        txn = axi_txn#(32,32)::type_id::create("txn");
        start_item(txn);
        assert(txn.randomize() with {
            is_write == 0;
            len      == wrap_lengths[i];
            burst    == 2'b10;
        });
        finish_item(txn);
    end
endtask

endclass

class invalid_wstrb extends uvm_sequence#(axi_txn#(32,32));
`uvm_object_utils(invalid_wstrb)

axi_txn#(32, 32) txn;

function new(input name = "invalid_wstrb");
    super.new(name);
endfunction

virtual task body();
    txn = axi_txn#(32,32)::type_id::create("txn");
    start_item(txn);
    txn.legal_wstrb.constraint_mode(0);
    assert(txn.randomize() with {
        is_write == 1;
        len      == 1;
        burst    == 2'b00;
        wstrb    == '0;
    });
    finish_item(txn);
endtask

endclass

class invalid_burst extends uvm_sequence#(axi_txn#(32,32));
`uvm_object_utils(invalid_burst)

axi_txn#(32, 32) txn;

function new(input name = "invalid_burst");
    super.new(name);
endfunction

virtual task body();
    txn = axi_txn#(32,32)::type_id::create("txn");
    start_item(txn);
    txn.legal_burst.constraint_mode(0);
    assert(txn.randomize() with {
        burst == 2'b11;
    });
    finish_item(txn);
endtask

endclass

class misaligned_addr extends uvm_sequence#(axi_txn#(32,32));
`uvm_object_utils(misaligned_addr)

axi_txn#(32,32) txn;

function new(input string name = "misaligned_addr");
    super.new(name);
endfunction

virtual task body();
    txn = axi_txn#(32,32)::type_id::create("txn");
    txn.addr_align.constraint_mode(0);
    start_item(txn);
    assert(txn.randomize() with {
      size == 2; // 4-byte beat
      addr % (1 << size) != 0; // misaligned address
    });
    finish_item(txn);
endtask

endclass