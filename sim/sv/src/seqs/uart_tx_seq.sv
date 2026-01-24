class uart_tx_seq extends uvm_sequence #(uart_tx_transaction);
    `uvm_object_utils(uart_tx_seq)
    `uvm_declare_p_sequencer(uart_tx_sequencer) 

    uart_configuration  uart_tx_cfg;
    rand bit [7:0]      tx_data;
    rand bit            inject_parity_error;
    rand bit            inject_stop_error;

    function new(string name = "uart_tx_seq");
        super.new(name);
    endfunction : new

    virtual task pre_start();
        super.pre_start();
        uart_tx_cfg = p_sequencer.uart_tx_cfg;
    endtask : pre_start

    virtual task body();
        req = uart_tx_transaction::type_id::create("req");
        `uvm_do_with(req, {
            uart_tx_data_frame  == tx_data;
            inject_parity_error == this.inject_parity_error;
            inject_stop_error   == this.inject_stop_error;
        })
    endtask : body

endclass : uart_tx_seq