class uart_apb_base_test extends uvm_test;
    
    //UVM Factory
    `uvm_component_utils(uart_apb_base_test)

    // APB
    uart_apb_env_base           uart_apb_env;
    apb_master_configuration    apb_m_cfg;
    virtual apb_master_itf      apb_m_if;

    // UART
    uart_configuration          uart_cfg;
    virtual uart_tx_if          tx_if;
    virtual uart_rx_if          rx_if;

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase 
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        uart_apb_env = uart_apb_env_base::type_id::create("uart_apb_env", this);
        apb_m_cfg  = apb_master_configuration::type_id::create("apb_m_cfg", this);
        uart_cfg = uart_configuration::type_id::create("uart_cfg", this);

        void'(uvm_config_db#(virtual uart_tx_if)::get(null, get_full_name(), "tx_if", tx_if));
        void'(uvm_config_db#(virtual uart_rx_if)::get(null, get_full_name(), "rx_if", rx_if));
        if (!uvm_config_db#(virtual apb_master_itf)::get(null, get_full_name(), "apb_m_if", apb_m_if))
          `uvm_fatal("get_intf", "no interface found!") 

        // Get interface
        uart_cfg.tx_if = tx_if;
        uart_cfg.rx_if = rx_if;
        apb_m_cfg.master_itf = apb_m_if;

        // Create sub configs
        uvm_config_db#(apb_master_configuration)::set(this, "uart_apb_env", "apb_m_cfg", apb_m_cfg);
        uvm_config_db#(uart_configuration)::set(this, "uart_apb_env", "uart_cfg", uart_cfg);
        uvm_config_db#(virtual apb_master_itf)::set(this, "uart_apb_env.apb_agent*", "master_itf", apb_m_if);
    
    endfunction : build_phase
endclass : uart_apb_base_test

class uart_apb_simple_test extends uart_apb_base_test;

    `uvm_component_utils(uart_apb_simple_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq;
    uart_rx_seq         u_rx_seq;

    function new(string name = "uart_apb_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("TEST", "System is out of reset and clock is stable. Starting sequences...", UVM_LOW)
        
        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq = apb_read_regs_seq::type_id::create("apb_r_seq");
        u_tx_seq  = uart_tx_seq::type_id::create("u_tx_seq");
        u_rx_seq  = uart_rx_seq::type_id::create("u_rx_seq");

        // --- APB send --- //
        // -- Config -- //
        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG;
            data_bit_num == APB_DATA_8BIT;   
            stop_bit_num == APB_CFG_ONE_STOP_BIT; 
            parity_en    == APB_CFG_PARITY_DIS;   
        }) `uvm_error("TEST", "Randomization failed for Config")
        uart_cfg.parity_en = UART_PARITY_DIS;
        apb_w_seq.start(uart_apb_env.apb_agent.sequencer);

        fork
            u_rx_seq.start(uart_apb_env.uart_rx.sequencer);
        join_none

        // -- Send data -- //
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_TX_DATA; 
            data == 32'h55;
        }) `uvm_error("TEST", "Randomization failed for TX_DATA")
        apb_w_seq.start(uart_apb_env.apb_agent.sequencer);

        // -- Start -- //
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CTRL_REG; 
        }) `uvm_error("TEST", "Randomization failed for CTRL_REG")
        apb_w_seq.start(uart_apb_env.apb_agent.sequencer);

        wait(uart_cfg.tx_if.tx_done == 1'b0);
        wait(uart_cfg.tx_if.tx_done == 1'b1);

        // --- UART send -- //
        if (!u_tx_seq.randomize() with {
            tx_data == 8'hAA; 
            inject_parity_error == 1'b0; 
            inject_stop_error   == 1'b0; 
        }) `uvm_error("TEST", "Randomization failed")
        u_tx_seq.start(uart_apb_env.uart_tx.sequencer);

        wait(uart_cfg.rx_if.rx_done == 1'b1);

        if (!apb_r_seq.randomize() with {
            addr == `ADDR_RX_DATA; 
        }) `uvm_error("TEST", "Randomization failed for RX_DATA read")
        apb_r_seq.start(uart_apb_env.apb_agent.sequencer);

        phase.drop_objection(this);
    endtask : run_phase

endclass : uart_apb_simple_test

class 