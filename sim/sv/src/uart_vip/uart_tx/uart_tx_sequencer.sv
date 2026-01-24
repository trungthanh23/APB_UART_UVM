class uart_tx_sequencer extends uvm_sequencer #(uart_tx_transaction);

    // UVM Factory
    `uvm_component_utils(uart_tx_sequencer)

    //Config for sequeces
    uart_configuration      uart_tx_cfg;
    
    //Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase to get the config
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in TX sequencer", UVM_LOW);
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_tx_cfg", uart_tx_cfg) && uart_tx_cfg == null) begin
            `uvm_fatal("build_phase", "Cannot get UART TX configuration in sequencer")
        end
        
    endfunction : build_phase

endclass : uart_tx_sequencer 