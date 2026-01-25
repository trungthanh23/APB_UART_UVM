class apb_uart_base_test extends uvm_test;
    
    //UVM Factory
    `uvm_component_utils(apb_uart_base_test)

    // APB
    apb_uart_env_base           apb_uart_env;
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

        apb_uart_env = apb_uart_env_base::type_id::create("apb_uart_env", this);
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
        uvm_config_db#(apb_master_configuration)::set(this, "apb_uart_env", "apb_m_cfg", apb_m_cfg);
        uvm_config_db#(uart_configuration)::set(this, "apb_uart_env", "uart_cfg", uart_cfg);
        uvm_config_db#(virtual apb_master_itf)::set(this, "apb_uart_env.apb_agent*", "master_itf", apb_m_if);
        uvm_config_db#(virtual apb_master_itf)::set(this, "apb_uart_env.scoreboard", "apb_vif", apb_m_if);
    
    endfunction : build_phase
endclass : apb_uart_base_test

class apb_uart_simple_test extends apb_uart_base_test;

    `uvm_component_utils(apb_uart_simple_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq;
    uart_rx_seq         u_rx_seq;

    function new(string name = "apb_uart_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("APB_UART_TEST", "System is out of reset and clock is stable. Starting sequences...", UVM_LOW)
        
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
        }) `uvm_error("APB_UART_TEST", "Randomization failed for Config")
        uart_cfg.parity_en = UART_PARITY_DIS;
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        fork
            u_rx_seq.start(apb_uart_env.uart_rx.sequencer);
        join_none

        // -- Send data -- //
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_TX_DATA; 
            data == 32'h55;
        }) `uvm_error("APB_UART_TEST", "Randomization failed for TX_DATA")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        // -- Start -- //
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CTRL_REG; 
        }) `uvm_error("APB_UART_TEST", "Randomization failed for CTRL_REG")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        wait(uart_cfg.tx_if.tx_done == 1'b0);
        wait(uart_cfg.tx_if.tx_done == 1'b1);

        // --- UART send -- //
        if (!u_tx_seq.randomize() with {
            tx_data == 8'hAA; 
            inject_parity_error == 1'b0; 
            inject_stop_error   == 1'b0; 
        }) `uvm_error("APB_UART_TEST", "Randomization failed")
        u_tx_seq.start(apb_uart_env.uart_tx.sequencer);

        wait(uart_cfg.rx_if.rx_done == 1'b1);

        if (!apb_r_seq.randomize() with {
            addr == `ADDR_STT_REG; 
        }) `uvm_error("APB_UART_TEST", "Randomization failed for RX_DATA read")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with {
            addr == `ADDR_RX_DATA; 
        }) `uvm_error("APB_UART_TEST", "Randomization failed for RX_DATA read")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        phase.drop_objection(this);
    endtask : run_phase

endclass : apb_uart_simple_test

class apb_rand_num_bit_test extends apb_uart_base_test;
    `uvm_component_utils(apb_rand_num_bit_test)

    apb_write_regs_seq  apb_w_seq;
    uart_rx_seq         u_rx_seq;

    apb_data_bit_num_e  history_q_data_bit_num[$];

    function new(string name = "apb_uart_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("APB_UART_TEST", "\nSystem is out of reset and clock is stable. \nStarting sequences...", UVM_LOW)

        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        u_rx_seq  = uart_rx_seq::type_id::create("u_rx_seq");

        fork
            u_rx_seq.start(apb_uart_env.uart_rx.sequencer);
        join_none

        history_q_data_bit_num.delete();

        for (int i = 0; i < 4; ++i) begin
            `uvm_info("APB_UART_TEST", $sformatf("\n\n================================\n===== Transaction number %0d =====\n================================\n", i+1), UVM_MEDIUM);
            // --- APB send --- //
            // -- Config Randdom -- //
            if (!apb_w_seq.randomize() with {
                addr         == `ADDR_CFG_REG;   
                stop_bit_num == APB_CFG_ONE_STOP_BIT; 
                parity_en    == APB_CFG_PARITY_DIS; 
                !(data_bit_num inside {history_q_data_bit_num});  
            }) `uvm_error("APB_UART_TEST", "Randomization failed for Config")

            history_q_data_bit_num.push_back(apb_w_seq.data_bit_num);
            
            // Send cfg to uart vip
            uart_cfg.parity_en = UART_PARITY_DIS;

            case (apb_w_seq.data_bit_num)
                APB_DATA_5BIT: uart_cfg.data_bit_num = UART_5BIT;
                APB_DATA_6BIT: uart_cfg.data_bit_num = UART_6BIT;
                APB_DATA_7BIT: uart_cfg.data_bit_num = UART_7BIT;
                APB_DATA_8BIT: uart_cfg.data_bit_num = UART_8BIT;
            endcase
            
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            // -- Send data -- //
            if (!apb_w_seq.randomize() with {
                addr == `ADDR_TX_DATA; 
            }) `uvm_error("APB_UART_TEST", "Randomization failed for TX_DATA")
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            // -- Start -- //
            if (!apb_w_seq.randomize() with {
                addr == `ADDR_CTRL_REG; 
            }) `uvm_error("APB_UART_TEST", "Randomization failed for CTRL_REG")
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            wait(uart_cfg.tx_if.tx_done == 1'b0);
            wait(uart_cfg.tx_if.tx_done == 1'b1);
        end

        phase.drop_objection(this);

    endtask : run_phase

endclass : apb_rand_num_bit_test

class apb_rand_cfg_test extends apb_uart_base_test;
    `uvm_component_utils(apb_rand_cfg_test)

    apb_write_regs_seq  apb_w_seq;
    uart_rx_seq         u_rx_seq;

    apb_stop_bit_num_e  history_q_stop_bit_num[$];
    apb_parity_en_e     history_q_parity_en[$];
    apb_parity_type_e   history_q_parity_type[$];

    function new(string name = "apb_uart_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("APB_UART_TEST", "\nSystem is out of reset and clock is stable. \nStarting sequences...", UVM_LOW)

        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        u_rx_seq  = uart_rx_seq::type_id::create("u_rx_seq");

        fork
            u_rx_seq.start(apb_uart_env.uart_rx.sequencer);
        join_none

        // Delete history
        history_q_stop_bit_num.delete();
        history_q_parity_en.delete();
        history_q_parity_type.delete();

        // Start transfer
        for (int i = 0; i < 1; ++i) begin
            `uvm_info("APB_UART_TEST", $sformatf("\n\n================================\n===== Transaction number %0d =====\n================================\n", i+1), UVM_MEDIUM);
            
            // -- Config Randdom -- //
            if (!apb_w_seq.randomize() with {
                addr         == `ADDR_CFG_REG;
                !(stop_bit_num inside {history_q_stop_bit_num}); 
                !(parity_en inside {history_q_parity_en});
                !(parity_type inside {history_q_parity_type});
            }) `uvm_error("APB_UART_TEST", "Randomization failed for Config")
            
            // Send cfg to uart vip
            uart_cfg.parity_en = apb_w_seq.parity_en;
            
            case (apb_w_seq.data_bit_num)
                APB_DATA_5BIT: uart_cfg.data_bit_num = UART_5BIT;
                APB_DATA_6BIT: uart_cfg.data_bit_num = UART_6BIT;
                APB_DATA_7BIT: uart_cfg.data_bit_num = UART_7BIT;
                APB_DATA_8BIT: uart_cfg.data_bit_num = UART_8BIT;
            endcase
            
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            // -- Send data -- //
            if (!apb_w_seq.randomize() with {
                addr == `ADDR_TX_DATA; 
            }) `uvm_error("APB_UART_TEST", "Randomization failed for TX_DATA")
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            // -- Start -- //
            if (!apb_w_seq.randomize() with {
                addr == `ADDR_CTRL_REG; 
            }) `uvm_error("APB_UART_TEST", "Randomization failed for CTRL_REG")
            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            wait(uart_cfg.tx_if.tx_done == 1'b0);
            wait(uart_cfg.tx_if.tx_done == 1'b1);
        end

        phase.drop_objection(this);

    endtask : run_phase

endclass : apb_rand_cfg_test

class apb_write_addr_error_test extends apb_uart_base_test;
    `uvm_component_utils(apb_write_addr_error_test)

    apb_write_error_addr_seq err_seq;

    function new(string name = "apb_write_addr_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("APB_UART_TEST", "System Reset Done. Starting Error Tests...", UVM_LOW)

        err_seq = apb_write_error_addr_seq::type_id::create("err_seq");


        // CASE 1: Write into RO register - CFG 
        `uvm_info("APB_UART_TEST", "\n>>> TEST CASE 1: Write to RO Register (0x04)\n", UVM_LOW)
        if (!err_seq.randomize() with { addr == 12'h004; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize failed")
        
        err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        // CASE 2: Write into RO register - STT
        `uvm_info("APB_UART_TEST", "\n>>> TEST CASE 2: Write to STATUS Register (0x10)\n", UVM_LOW)
        if (!err_seq.randomize() with { addr == 12'h010; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize failed")
        
        err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        // CASE 3: Write into Invalid register
        `uvm_info("APB_UART_TEST", "\n>>> TEST CASE 3: Write to Invalid Address\n", UVM_LOW)
        if (!err_seq.randomize() with { !(addr inside {12'h000, 12'h004, 12'h008, 12'h00C, 12'h010}); }) 
            `uvm_fatal("APB_UART_TEST", "Randomize failed")
        
        err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        
        phase.drop_objection(this);
    endtask : run_phase

endclass : apb_write_addr_error_test

