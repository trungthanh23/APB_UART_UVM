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

class apb_simple_write_test extends apb_uart_base_test;
    `uvm_component_utils(apb_simple_write_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_rx_seq         u_rx_seq;

    function new(string name = "apb_simple_write_test", uvm_component parent = null);
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

        `uvm_info("APB_UART_TEST", $sformatf("\n\n================================\n===== Transaction =====\n================================\n"), UVM_MEDIUM);

        // --- APB send --- //
        // -- Config Randdom -- //
        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG; 
            data_bit_num == APB_DATA_8BIT;
            stop_bit_num == APB_CFG_ONE_STOP_BIT; 
            parity_en    == APB_CFG_PARITY_DIS;  
        }) `uvm_error("APB_UART_TEST", "Randomization failed for Config")
        
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

        phase.drop_objection(this);

    endtask : run_phase

endclass : apb_simple_write_test

class apb_write_rand_cfg_test extends apb_uart_base_test;
    `uvm_component_utils(apb_write_rand_cfg_test)

    apb_write_regs_seq  apb_w_seq;
    uart_rx_seq         u_rx_seq;

    apb_data_bit_num_e  history_q_data_bit_num[$];
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
        history_q_data_bit_num.delete();
        history_q_stop_bit_num.delete();
        history_q_parity_en.delete();
        history_q_parity_type.delete();

        // Start transfer
        for (int i = 0; i < 24; ++i) begin
            `uvm_info("APB_UART_TEST", $sformatf("\n\n================================\n===== Transaction number %0d =====\n================================\n", i+1), UVM_MEDIUM);
            
            // -- Config Randdom -- //
            if (!apb_w_seq.randomize() with {
                addr         == `ADDR_CFG_REG;
                !(data_bit_num inside {history_q_data_bit_num}) || 
                !(stop_bit_num inside {history_q_stop_bit_num}) || 
                !(parity_en    inside {history_q_parity_en})    ||
                !(parity_type  inside {history_q_parity_type});
            }) begin
                history_q_data_bit_num.delete();
                history_q_stop_bit_num.delete();
                history_q_parity_en.delete();
                history_q_parity_type.delete();
                if (!apb_w_seq.randomize() with {addr == `ADDR_CFG_REG;})
                    `uvm_fatal("APB_UART_TEST", "Randomize APB Config Failed")
            end
            
            // Send cfg to uart vip
            case (apb_w_seq.data_bit_num)
                APB_DATA_5BIT: uart_cfg.data_bit_num = UART_5BIT;
                APB_DATA_6BIT: uart_cfg.data_bit_num = UART_6BIT;
                APB_DATA_7BIT: uart_cfg.data_bit_num = UART_7BIT;
                APB_DATA_8BIT: uart_cfg.data_bit_num = UART_8BIT;
            endcase
            uart_cfg.stop_bit_num = (apb_w_seq.stop_bit_num == APB_CFG_TWO_STOP_BIT) ? UART_TWO_STOP_BIT : UART_ONE_STOP_BIT;
            uart_cfg.parity_en    = (apb_w_seq.parity_en == APB_CFG_PARITY_EN) ? UART_PARITY_EN : UART_PARITY_DIS;
            uart_cfg.parity_type  = (apb_w_seq.parity_type == APB_CFG_PARITY_EVEN) ? UART_PARITY_EVEN : UART_PARITY_ODD;
            
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

endclass : apb_write_rand_cfg_test

class apb_write_addr_error_test extends apb_uart_base_test;
    `uvm_component_utils(apb_write_addr_error_test)

    apb_write_regs_seq       apb_w_seq;
    apb_read_regs_seq        apb_r_seq;
    apb_write_error_addr_seq apb_err_seq;

    function new(string name = "apb_write_addr_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        apb_w_seq   = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq   = apb_read_regs_seq::type_id::create("apb_r_seq");
        apb_err_seq = apb_write_error_addr_seq::type_id::create("apb_err_seq");

        if (!apb_err_seq.randomize() with { addr == 12'h004; }) 
            `uvm_fatal("TEST", "Randomize failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        if (!apb_err_seq.randomize() with { addr == 12'h010; }) 
            `uvm_fatal("TEST", "Randomize failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        if (!apb_err_seq.randomize() with { !(addr inside {12'h000, 12'h004, 12'h008, 12'h00C, 12'h010}); }) 
            `uvm_fatal("TEST", "Randomize failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);
        repeat(5) @(posedge apb_m_if.pclk);

        if (!apb_w_seq.randomize() with { 
            addr == `ADDR_CFG_REG; 
            data == 32'h0000_0000; 
        }) `uvm_fatal("TEST", "Randomize Valid Write Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_err_seq.randomize() with { 
            (addr & 12'h0FF) == `ADDR_CFG_REG; 
            addr > 12'h0FF;                    
            data == 32'hFFFF_FFFF;             
        }) `uvm_fatal("TEST", "Randomize Alias Addr Failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_CFG_REG; }) 
            `uvm_fatal("TEST", "Randomize Read Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data !== 32'h0000_0000) begin
            `uvm_error("TEST", $sformatf("BUG DETECTED: Address Aliasing! Addr 0x%h overwrote 0x08! Val: %h", apb_err_seq.addr, apb_r_seq.read_data))
        end else begin
            `uvm_info("TEST", "PASS: No Address Aliasing detected.", UVM_NONE)
        end
        
        phase.drop_objection(this);
    endtask

endclass : apb_write_addr_error_test

class apb_config_readback_test extends apb_uart_base_test;
    `uvm_component_utils(apb_config_readback_test)

    apb_write_regs_seq apb_w_seq;
    apb_read_regs_seq  apb_r_seq;

    function new(string name = "apb_config_readback_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        bit [31:0] expected_data;

        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq = apb_read_regs_seq::type_id::create("apb_r_seq");

        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CFG_REG;
        }) `uvm_fatal("APB_UART_TEST", "\n\nRandomize Write Seq Failed\n")

        expected_data = {27'h0, apb_w_seq.parity_type, apb_w_seq.parity_en, apb_w_seq.stop_bit_num, apb_w_seq.data_bit_num};
        apb_w_seq.data = expected_data;

        `uvm_info("APB_UART_TEST", $sformatf("\n\nWriting Config Data: 0x%0h\n", expected_data), UVM_NONE)
        
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        repeat(10) @(posedge apb_m_if.pclk);

        if (!apb_r_seq.randomize() with {
            addr == `ADDR_CFG_REG;
        }) `uvm_fatal("APB_UART_TEST", "\n\nRandomize Read Seq Failed\n")

        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        `uvm_info("APB_UART_TEST", $sformatf("\n\nRead Back Data: 0x%0h\n", apb_r_seq.read_data), UVM_NONE)

        if (apb_r_seq.read_data !== expected_data) begin
            `uvm_error("APB_UART_TEST", $sformatf("\n\nFAILURE: Config Mismatch! Wrote: 0x%0h, Read: 0x%0h\n", expected_data, apb_r_seq.read_data))
        end else begin
            `uvm_info("APB_UART_TEST", "\n\nSUCCESS: Config Register Readback Matched!\n", UVM_NONE)
        end

        phase.drop_objection(this);

    endtask : run_phase
endclass : apb_config_readback_test

class apb_full_coverage_test extends apb_uart_base_test;
    `uvm_component_utils(apb_full_coverage_test)

    apb_write_regs_seq       apb_w_seq;
    apb_read_regs_seq        apb_r_seq;
    apb_write_error_addr_seq apb_err_seq; 

    function new(string name = "apb_full_coverage_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        apb_w_seq     = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq     = apb_read_regs_seq::type_id::create("apb_r_seq");
        apb_err_seq = apb_write_error_addr_seq::type_id::create("apb_err_seq");

        if (!apb_w_seq.randomize() with { addr == `ADDR_TX_DATA; data == 32'hAA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Write TX Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_TX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read TX Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_err_seq.randomize() with { addr == `ADDR_RX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Err Write RX Failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_RX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read RX Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_w_seq.randomize() with { 
            addr == `ADDR_CFG_REG; 
            data_bit_num == APB_DATA_8BIT;
        }) `uvm_fatal("APB_UART_TEST", "Randomize Write CFG Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_CFG_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read CFG Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_w_seq.randomize() with { addr == `ADDR_CTRL_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Write CTRL Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_CTRL_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read CTRL Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);
        
        wait(uart_cfg.tx_if.tx_done == 1'b1); 

        if (!apb_err_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Err Write STT Failed")
        apb_err_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read STT Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        phase.drop_objection(this);

    endtask : run_phase

endclass : apb_full_coverage_test
class uart_tx_rand_cfg_test extends apb_uart_base_test;
    `uvm_component_utils(uart_tx_rand_cfg_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq;

    apb_data_bit_num_e   hist_data_bit_num[$];
    apb_stop_bit_num_e   hist_stop_bit_num[$];
    apb_parity_en_e      hist_parity_en[$];
    apb_parity_type_e    hist_parity_type[$];

    function new(string name = "uart_tx_rand_cfg_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        
        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq   = apb_read_regs_seq::type_id::create("apb_rdseq");
        u_tx_seq    = uart_tx_seq::type_id::create("u_tx_seq");

        hist_data_bit_num.delete();
        hist_stop_bit_num.delete();
        hist_parity_en.delete();
        hist_parity_type.delete();

        for (int i = 0; i < 24; i++) begin
            `uvm_info("APB_UART_TEST", $sformatf("\n\n================================\n===== Transaction number %0d =====\n================================\n", i+1), UVM_MEDIUM);

            if (!apb_w_seq.randomize() with {
                addr == `ADDR_CFG_REG;
                !(data_bit_num inside {hist_data_bit_num}) ||
                !(stop_bit_num inside {hist_stop_bit_num}) ||
                !(parity_en    inside {hist_parity_en}) ||
                !(parity_type  inside {hist_parity_type});
            }) begin
                hist_data_bit_num.delete();
                hist_stop_bit_num.delete();
                hist_parity_en.delete();
                hist_parity_type.delete();
                if (!apb_w_seq.randomize() with { addr == `ADDR_CFG_REG; })
                    `uvm_fatal("APB_UART_TEST", "Randomize APB Config Failed")
            end

            if (hist_data_bit_num.size() >= 4 || hist_stop_bit_num.size() >= 2 || hist_parity_en.size() >= 2) begin
                `uvm_info("TEST", "History queues saturated. Clearing history to avoid Constraint Conflict.", UVM_LOW)
                hist_data_bit_num.delete();
                hist_stop_bit_num.delete();
                hist_parity_en.delete();
                hist_parity_type.delete();
            end

            // if (!apb_w_seq.randomize() with {
            //     addr == `ADDR_CFG_REG;
            //     (hist_data_bit_num.size() > 0) -> !(data_bit_num inside {hist_data_bit_num}) ||
            //     (hist_stop_bit_num.size() > 0) -> !(stop_bit_num inside {hist_stop_bit_num}) ||
            //     (hist_parity_en.size()    > 0) -> !(parity_en    inside {hist_parity_en})    ||
            //     (hist_parity_type.size()  > 0) -> !(parity_type  inside {hist_parity_type});
            // }) begin
            //     `uvm_fatal("APB_UART_TEST", "Randomize APB Config Failed even after check")
            // end

            // hist_data_bit_num.push_back(apb_w_seq.data_bit_num);
            // hist_stop_bit_num.push_back(apb_w_seq.stop_bit_num);
            // hist_parity_en.push_back(apb_w_seq.parity_en);
            // hist_parity_type.push_back(apb_w_seq.parity_type);

            apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

            case(apb_w_seq.data_bit_num)
                APB_DATA_5BIT: uart_cfg.data_bit_num = UART_5BIT;
                APB_DATA_6BIT: uart_cfg.data_bit_num = UART_6BIT;
                APB_DATA_7BIT: uart_cfg.data_bit_num = UART_7BIT;
                APB_DATA_8BIT: uart_cfg.data_bit_num = UART_8BIT;
            endcase
            uart_cfg.stop_bit_num = (apb_w_seq.stop_bit_num == APB_CFG_TWO_STOP_BIT) ? UART_TWO_STOP_BIT : UART_ONE_STOP_BIT;
            uart_cfg.parity_en    = (apb_w_seq.parity_en == APB_CFG_PARITY_EN) ? UART_PARITY_EN : UART_PARITY_DIS;
            uart_cfg.parity_type  = (apb_w_seq.parity_type == APB_CFG_PARITY_EVEN) ? UART_PARITY_EVEN : UART_PARITY_ODD;

            if (!u_tx_seq.randomize() with {
                inject_parity_error == 1'b0;
                inject_stop_error   == 1'b0;
            }) `uvm_fatal("APB_UART_TEST", "Randomize UART TX SEQ Failed")
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
        end

        phase.drop_objection(this);

    endtask : run_phase

endclass : uart_tx_rand_cfg_test

class uart_tx_simple_test extends apb_uart_base_test;
    `uvm_component_utils(uart_tx_simple_test)

    apb_write_regs_seq  apb_w_seq;
    uart_tx_seq         u_tx_seq;
    apb_read_regs_seq   apb_r_seq;

    function new(string name = "uart_tx_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        
        apb_w_seq  = apb_write_regs_seq::type_id::create("apb_w_seq");
        u_tx_seq = uart_tx_seq::type_id::create("u_tx_seq");
        apb_r_seq  = apb_read_regs_seq::type_id::create("apb_r_seq");

        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG;
            data_bit_num == APB_DATA_6BIT;
            stop_bit_num == APB_CFG_ONE_STOP_BIT;
            parity_en    == APB_CFG_PARITY_EN;
            parity_type  == APB_CFG_PARITY_ODD;
        }) `uvm_fatal("APB_UART_TEST", "Randomize APB Config Failed")

        uart_cfg.data_bit_num = UART_6BIT;
        uart_cfg.stop_bit_num = UART_ONE_STOP_BIT;
        uart_cfg.parity_en    = UART_PARITY_EN;
        uart_cfg.parity_type  = UART_PARITY_ODD;

        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!u_tx_seq.randomize() with {
            tx_data             == 8'hA5; 
            inject_parity_error == 1'b0;
            inject_stop_error   == 1'b0;
        }) `uvm_fatal("APB_UART_TEST", "Randomize UART TX SEQ Failed")
        
        u_tx_seq.start(apb_uart_env.uart_tx.sequencer);

        wait(uart_cfg.rx_if.rx_done === 1'b1);

        if (!apb_r_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize STT Read Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_RX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize RX Data Read Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        phase.drop_objection(this);
    endtask : run_phase

endclass : uart_tx_simple_test

class uart_tx_parity_error_test extends apb_uart_base_test;
    `uvm_component_utils(uart_tx_parity_error_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq; 

    function new(string name = "uart_tx_parity_error_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        apb_read_regs_seq poll_seq;

        phase.raise_objection(this);
        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq = apb_read_regs_seq::type_id::create("apb_r_seq");
        u_tx_seq  = uart_tx_seq::type_id::create("u_tx_seq");

        `uvm_info("APB_UART_TEST", "\nConfiguring DUT with Parity Enabled...\n", UVM_LOW)

        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG;
            data_bit_num == APB_DATA_8BIT;
            stop_bit_num == APB_CFG_ONE_STOP_BIT;
            parity_en    == APB_CFG_PARITY_EN;   
            parity_type  == APB_CFG_PARITY_ODD;  
        }) `uvm_fatal("APB_UART_TEST", "Randomize APB Config Failed")

        uart_cfg.data_bit_num = UART_8BIT;
        uart_cfg.stop_bit_num = UART_ONE_STOP_BIT;
        uart_cfg.parity_en    = UART_PARITY_EN;
        uart_cfg.parity_type  = UART_PARITY_ODD;

        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        `uvm_info("APB_UART_TEST", "\nInjecting Parity Error Transaction...\n", UVM_LOW)
        
        uart_cfg.disable_parity_check_error = 1;
        uart_cfg.expect_parity_error = 1;

        fork
            begin
                if (!u_tx_seq.randomize() with {
                    tx_data             == 8'hA5;
                    inject_parity_error == 1'b1;
                    inject_stop_error   == 1'b0;
                }) `uvm_fatal("APB_UART_TEST", "Randomize UART TX Failed")
                u_tx_seq.start(apb_uart_env.uart_tx.sequencer);

                wait(uart_cfg.rx_if.rx_done == 1'b1);
            end

            begin
                apb_uart_env.scoreboard.set_report_severity_id_override(UVM_ERROR, "SCB_STS_FAIL", UVM_INFO);
                apb_uart_env.apb_agent.monitor.set_report_verbosity_level(UVM_NONE);
                forever begin
                    if (uart_cfg.expect_parity_error == 0) break;

                    poll_seq = apb_read_regs_seq::type_id::create("poll_seq");
                    if (!poll_seq.randomize() with {
                        addr == `ADDR_STT_REG; 
                    }) `uvm_error("APB_UART_TEST", "Randomize Poll Seq Failed")
                    poll_seq.start(apb_uart_env.apb_agent.sequencer);
                end

                apb_uart_env.apb_agent.monitor.set_report_verbosity_level(UVM_HIGH);
                apb_uart_env.scoreboard.set_report_severity_id_override(UVM_ERROR, "SCB", UVM_ERROR);
            end
        join
        if (uart_cfg.rx_if.rx_done !== 1'b1) 
            wait(uart_cfg.rx_if.rx_done === 1'b1);

        apb_uart_env.scoreboard.set_report_severity_id_override(UVM_ERROR, "SCB", UVM_INFO);

        uart_cfg.disable_parity_check_error = 0;
        phase.drop_objection(this);

    endtask : run_phase

endclass : uart_tx_parity_error_test

class uart_tx_glitch_test extends apb_uart_base_test;
    `uvm_component_utils(uart_tx_glitch_test)

    apb_write_regs_seq   apb_w_seq;
    apb_read_regs_seq    apb_r_seq;

    function new(string name = "uart_tx_glitch_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        real bit_period_ns;
        
        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq = apb_read_regs_seq::type_id::create("apb_r_seq");

        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        uart_cfg.data_bit_num = UART_8BIT;
        uart_cfg.stop_bit_num = UART_ONE_STOP_BIT;
        uart_cfg.parity_en    = UART_PARITY_DIS;
        uart_cfg.parity_type  = UART_PARITY_ODD;

        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CFG_REG;
            data == {24'h0, uart_cfg.parity_type, uart_cfg.parity_en, uart_cfg.stop_bit_num, uart_cfg.data_bit_num};
        }) `uvm_fatal("APB_UART_TEST", "Randomize CFG Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        bit_period_ns = 1000000000.0 / uart_cfg.baudrate;

        wait(uart_cfg.tx_if.tx === 1'b1);
        repeat(100) @(posedge apb_m_if.pclk);

        apb_uart_env.uart_tx.monitor.set_report_severity_id_override(UVM_ERROR, "UART_TX_MON", UVM_INFO);
        
        if (!uvm_hdl_force("apb_uart_test_top.tx_if.tx", 1'b0)) begin
             `uvm_error("APB_UART_TEST", "\n\nForce fail! Check again path 'apb_uart_test_top.tx_if.tx'\n")
        end
        
        #(bit_period_ns / 4.0 * 1ns);
        
        if (!uvm_hdl_release("apb_uart_test_top.tx_if.tx")) begin
             `uvm_error("APB_UART_TEST", "\n\nRelease fail!\n")
        end

        #(bit_period_ns * 12 * 1ns);

        apb_uart_env.uart_tx.monitor.set_report_severity_id_override(UVM_ERROR, "UART_TX_MON", UVM_INFO);

        if (!apb_r_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_error("APB_UART_TEST", "Randomize Check Seq Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data[1] === 1'b1) begin
            `uvm_error("APB_UART_TEST", "\n\nFAILURE: DUT accepted Glitch as valid Transaction (RX_DONE set)!\n")
        end else begin
            `uvm_info("APB_UART_TEST", "\n\nSUCCESS: DUT ignored Glitch (RX_DONE not set)\n", UVM_NONE)
        end

        if (!apb_r_seq.randomize() with { addr == `ADDR_RX_DATA; }) 
            `uvm_error("APB_UART_TEST", "Randomize Check Seq Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data !== 0) begin
             `uvm_error("APB_UART_TEST", "\n\nFAILURE: RX Data Register contains unexpected data!\n")
        end

        phase.drop_objection(this);

    endtask : run_phase

endclass : uart_tx_glitch_test

class apb_uart_full_duplex_test extends apb_uart_base_test;
    `uvm_component_utils(apb_uart_full_duplex_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq;
    uart_rx_seq         u_rx_seq;

    function new(string name = "apb_uart_full_duplex_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);

        apb_w_seq  = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq   = apb_read_regs_seq::type_id::create("apb_r_seq");
        u_tx_seq = uart_tx_seq::type_id::create("u_tx_seq");
        u_rx_seq = uart_rx_seq::type_id::create("u_rx_seq");

        fork
            u_rx_seq.start(apb_uart_env.uart_rx.sequencer);
        join_none

        uart_cfg.data_bit_num = UART_8BIT;
        uart_cfg.stop_bit_num = UART_ONE_STOP_BIT;
        uart_cfg.parity_en    = UART_PARITY_EN;
        uart_cfg.parity_type  = UART_PARITY_ODD;

        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG;
            data_bit_num == APB_DATA_8BIT;
            stop_bit_num == APB_CFG_ONE_STOP_BIT;
            parity_en    == APB_CFG_PARITY_EN;
            parity_type  == APB_CFG_PARITY_ODD;
        }) `uvm_fatal("APB_UART_TEST", "Randomize CFG Failed")
        
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        fork
            begin
                if (!u_tx_seq.randomize() with {
                    tx_data             == 8'hC3; 
                    inject_parity_error == 1'b0;
                    inject_stop_error   == 1'b0;
                }) `uvm_fatal("APB_UART_TEST", "Randomize UART TX SEQ Failed")
                u_tx_seq.start(apb_uart_env.uart_tx.sequencer);
            end

            begin
                if (!apb_w_seq.randomize() with {
                    addr == `ADDR_TX_DATA; 
                    data == 32'h5A;
                }) `uvm_fatal("APB_UART_TEST", "Randomize APB Write TX Failed")
                apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

                if (!apb_w_seq.randomize() with {
                    addr == `ADDR_CTRL_REG; 
                }) `uvm_fatal("APB_UART_TEST", "Randomize APB Write CTRL Failed")
                apb_w_seq.start(apb_uart_env.apb_agent.sequencer);
            end
        join

        fork
            wait(uart_cfg.rx_if.rx_done === 1'b1);
            wait(uart_cfg.tx_if.tx_done === 1'b1);
        join

        if (!apb_r_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize STT Read Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_r_seq.randomize() with { addr == `ADDR_RX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize RX Data Read Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        phase.drop_objection(this);
    endtask
endclass : apb_uart_full_duplex_test

class apb_uart_reset_registers_test extends apb_uart_base_test;
    `uvm_component_utils(apb_uart_reset_registers_test)

    apb_write_regs_seq  apb_w_seq;
    apb_read_regs_seq   apb_r_seq;
    uart_tx_seq         u_tx_seq;

    function new(string name = "apb_uart_reset_registers_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        wait(apb_m_if.presetn === 1'b0); 
        wait(apb_m_if.presetn === 1'b1);
        repeat(10) @(posedge apb_m_if.pclk);
        `uvm_info("APB_UART_TEST", "System Reset Done...", UVM_LOW)

        apb_w_seq = apb_write_regs_seq::type_id::create("apb_w_seq");
        apb_r_seq = apb_read_regs_seq::type_id::create("apb_r_seq");
        u_tx_seq  = uart_tx_seq::type_id::create("u_tx_seq");

        `uvm_info("APB_UART_TEST", "\nWriting non-default config to registers...\n", UVM_LOW)
        if (!apb_w_seq.randomize() with {
            addr         == `ADDR_CFG_REG;
            data_bit_num == APB_DATA_8BIT; 
            stop_bit_num == APB_CFG_ONE_STOP_BIT;
            parity_en    == APB_CFG_PARITY_EN;   
            parity_type  == APB_CFG_PARITY_ODD;  
        }) `uvm_fatal("APB_UART_TEST", "Randomize CFG Failed")

        uart_cfg.data_bit_num = UART_8BIT;
        uart_cfg.stop_bit_num = UART_ONE_STOP_BIT;
        uart_cfg.parity_en    = UART_PARITY_EN;
        uart_cfg.parity_type  = UART_PARITY_ODD;

        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_w_seq.randomize() with {
            addr == `ADDR_TX_DATA;
            data == 32'hA5;  
        }) `uvm_fatal("APB_UART_TEST", "Randomize TX_DATA Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CTRL_REG;
            data[0] == 1'b1; 
        }) `uvm_fatal("APB_UART_TEST", "Randomize CTRL Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        fork
            begin
                repeat(200) @(posedge apb_m_if.pclk); 

                `uvm_info("APB_UART_TEST", "\nAsserting reset during transfer...\n", UVM_LOW)
                apb_m_if.presetn = 0;
                repeat(5) @(posedge apb_m_if.pclk);  
                apb_m_if.presetn = 1;
                `uvm_info("APB_UART_TEST", "\nDeasserted reset...\n", UVM_LOW)
            end

            begin
                wait(uart_cfg.tx_if.tx_done == 1'b1);
            end
        join_any
        disable fork;

        // Wait for reset stable
        repeat(10) @(posedge apb_m_if.pclk);

        `uvm_info("APB_UART_TEST", "\nChecking registers after reset...\n", UVM_LOW)

        // Read CFG_REG, expect 0
        if (!apb_r_seq.randomize() with { addr == `ADDR_CFG_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read CFG Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data !== 32'h0) begin
            `uvm_error("APB_UART_TEST", $sformatf("FAIL: CFG_REG not reset to default! Got: 0x%0h, Expected: 0x0", apb_r_seq.read_data))
        end else begin
            `uvm_info("APB_UART_TEST", "PASS: CFG_REG reset to 0x0", UVM_NONE)
        end

        // Read TX_DATA, expect 0
        if (!apb_r_seq.randomize() with { addr == `ADDR_TX_DATA; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read TX_DATA Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data !== 32'h0) begin
            `uvm_error("APB_UART_TEST", $sformatf("FAIL: TX_DATA not reset to default! Got: 0x%0h, Expected: 0x0", apb_r_seq.read_data))
        end else begin
            `uvm_info("APB_UART_TEST", "PASS: TX_DATA reset to 0x0", UVM_NONE)
        end

        // Read CTRL_REG, expect 0
        if (!apb_r_seq.randomize() with { addr == `ADDR_CTRL_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read CTRL Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data !== 32'h0) begin
            `uvm_error("APB_UART_TEST", $sformatf("FAIL: CTRL_REG not reset to default! Got: 0x%0h, Expected: 0x0", apb_r_seq.read_data))
        end else begin
            `uvm_info("APB_UART_TEST", "PASS: CTRL_REG reset to 0x0", UVM_NONE)
        end

        if (!apb_r_seq.randomize() with { addr == `ADDR_STT_REG; }) 
            `uvm_fatal("APB_UART_TEST", "Randomize Read STT Failed")
        apb_r_seq.start(apb_uart_env.apb_agent.sequencer);

        if (apb_r_seq.read_data[0] !== 1'b1 || apb_r_seq.read_data[31:1] !== 31'h0) begin
            `uvm_error("APB_UART_TEST", $sformatf("FAIL: STT_REG not reset to default! Got: 0x%0h, Expected: tx_done=1, others=0", apb_r_seq.read_data))
        end else begin
            `uvm_info("APB_UART_TEST", "PASS: STT_REG reset correctly (tx_done=1)", UVM_NONE)
        end

        // Check UART signals idle 
        if (uart_cfg.tx_if.tx !== 1'b1) begin
            `uvm_error("APB_UART_TEST", "FAIL: TX signal not idle after reset!")
        end else begin
            `uvm_info("APB_UART_TEST", "PASS: TX idle after reset", UVM_NONE)
        end

        `uvm_info("APB_UART_TEST", "\nRecovering DUT after reset...\n", UVM_LOW)
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer); 

        // Re-write TX_DATA 0xA5
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_TX_DATA;
            data == 32'hA5;
        }) `uvm_fatal("APB_UART_TEST", "Randomize Recover TX_DATA Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        // Re-start CTRL
        if (!apb_w_seq.randomize() with {
            addr == `ADDR_CTRL_REG;
            data[0] == 1'b1;
        }) `uvm_fatal("APB_UART_TEST", "Randomize Recover CTRL Failed")
        apb_w_seq.start(apb_uart_env.apb_agent.sequencer);

        wait(uart_cfg.tx_if.tx_done == 1'b1);

        `uvm_info("APB_UART_TEST", "PASS: DUT recovered and completed transfer after reset", UVM_NONE)

        phase.drop_objection(this);
    endtask : run_phase

endclass : apb_uart_reset_registers_test