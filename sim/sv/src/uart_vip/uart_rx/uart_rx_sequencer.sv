class uart_rx_sequencer extends uvm_sequencer #(uart_rx_transaction);

    `uvm_component_utils(uart_rx_sequencer)

    //Config for sequeces
    uart_configuration      uart_rx_cfg;

    
    //Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase to get the config
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in rx sequencer", UVM_LOW);
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_rx_cfg", uart_rx_cfg) && uart_rx_cfg == null)
            `uvm_fatal("build_phase", "Cannot get UART RX configuration in sequencer")
    endfunction : build_phase

endclass : uart_rx_sequencer 