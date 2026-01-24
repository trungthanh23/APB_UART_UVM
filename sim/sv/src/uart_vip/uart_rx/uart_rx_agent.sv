class uart_rx_agent extends uvm_agent;
    //UART RX config
    uart_configuration  uart_rx_cfg;

    //UART RX components
    uart_rx_driver      driver;
    uart_rx_sequencer   sequencer;
    uart_rx_monitor     monitor;

    //Utils
    `uvm_component_utils(uart_rx_agent)

    //Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info(this.get_full_name(), "Build Phase in RX agent", UVM_HIGH);
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_rx_cfg", uart_rx_cfg) && uart_rx_cfg == null) begin
          `uvm_fatal("build_phase", "Cannot get UART RX configuration");
        end
        uvm_config_db #(uart_configuration)::set(this, "*", "uart_rx_cfg", uart_rx_cfg);

        monitor = uart_rx_monitor::type_id::create("monitor", this);
        if (uart_rx_cfg.is_active == UVM_ACTIVE) begin
            sequencer = uart_rx_sequencer::type_id::create("sequencer", this);
            driver = uart_rx_driver::type_id::create("driver", this);
        end
    endfunction : build_phase

    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in RX agent", UVM_HIGH);
        monitor.uart_rx_cfg = uart_rx_cfg; 
        monitor.rx_if       = uart_rx_cfg.rx_if;

        if (uart_rx_cfg.is_active == UVM_ACTIVE) begin
          driver.seq_item_port.connect(sequencer.seq_item_export);
          sequencer.uart_rx_cfg = uart_rx_cfg;
          driver.uart_rx_cfg    = uart_rx_cfg;
          driver.rx_if          = uart_rx_cfg.rx_if;
        end
    endfunction :connect_phase
endclass : uart_rx_agent