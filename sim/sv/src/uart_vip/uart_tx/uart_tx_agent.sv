class uart_tx_agent extends uvm_agent;
    //UART TX config
    uart_configuration  uart_tx_cfg;

    //UART TX components
    uart_tx_driver      driver;
    uart_tx_sequencer   sequencer;
    uart_tx_monitor     monitor;

    //Utils
    `uvm_component_utils(uart_tx_agent)

    //Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info(this.get_full_name(), "Build Phase in TX agent", UVM_HIGH);
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_tx_cfg", uart_tx_cfg) && uart_tx_cfg == null) begin
          `uvm_fatal("build_phase", "Cannot get UART TX configuration");
        end
        uvm_config_db #(uart_configuration)::set(this, "*", "uart_tx_cfg", uart_tx_cfg);

        monitor = uart_tx_monitor::type_id::create("monitor", this);
        if (uart_tx_cfg.is_active == UVM_ACTIVE) begin
            sequencer = uart_tx_sequencer::type_id::create("sequencer", this);
            driver = uart_tx_driver::type_id::create("driver", this);
        end
    endfunction : build_phase

    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in TX agent", UVM_HIGH);
        monitor.uart_tx_cfg = uart_tx_cfg; 
        monitor.tx_if       = uart_tx_cfg.tx_if;

        if (uart_tx_cfg.is_active == UVM_ACTIVE) begin
          driver.seq_item_port.connect(sequencer.seq_item_export);
          sequencer.uart_tx_cfg = uart_tx_cfg;
          driver.uart_tx_cfg    = uart_tx_cfg;
          driver.tx_if          = uart_tx_cfg.tx_if;
        end
    endfunction :connect_phase

endclass : uart_tx_agent