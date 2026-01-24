class uart_apb_env_base extends uvm_env;
    `uvm_component_utils(uart_apb_env_base)

    apb_master_agent            apb_agent;
    uart_rx_agent               uart_rx; 
    uart_tx_agent               uart_tx; 

    uart_apb_scoreboard         scoreboard;

    apb_master_configuration    apb_m_cfg;
    uart_configuration          uart_cfg;

    function new(string name = "uart_apb_env_base", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db #(apb_master_configuration)::get(this, "", "apb_m_cfg", apb_m_cfg))
            `uvm_fatal("build_phase", "Cannot get APB master configuration")

        if (!uvm_config_db #(uart_configuration)::get(this, "", "uart_cfg", uart_cfg))
            `uvm_fatal("build_phase", "Cannot get UART configuration")

        uvm_config_db#(apb_master_configuration)::set(this, "apb_agent*", "master_cfg", apb_m_cfg);
        uvm_config_db#(uart_configuration)::set(this, "uart_tx*", "uart_tx_cfg", uart_cfg);
        uvm_config_db#(uart_configuration)::set(this, "uart_rx*", "uart_rx_cfg", uart_cfg);

        apb_agent  = apb_master_agent::type_id::create("apb_agent", this);
        uart_rx    = uart_rx_agent::type_id::create("uart_rx", this);
        uart_tx    = uart_tx_agent::type_id::create("uart_tx", this);
        scoreboard = uart_apb_scoreboard::type_id::create("scoreboard", this);
        
    endfunction : build_phase

    function void end_of_elaboration_phase(uvm_phase phase);

        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();

    endfunction : end_of_elaboration_phase

    function void connect_phase(uvm_phase phase);

        apb_agent.monitor.master_monitor_port.connect(scoreboard.apb_imp);
        uart_rx.monitor.rx_monitor_port.connect(scoreboard.uart_rx_imp);
        uart_tx.monitor.tx_monitor_port.connect(scoreboard.uart_tx_imp);

    endfunction : connect_phase

endclass : uart_apb_env_base