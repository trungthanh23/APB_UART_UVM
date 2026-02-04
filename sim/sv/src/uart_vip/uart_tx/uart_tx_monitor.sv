class uart_tx_monitor extends uvm_monitor;

    // UART TX interface
    virtual uart_tx_if  tx_if;

    //UART TX config
    uart_configuration  uart_tx_cfg;

    //UART TX transaction
    uart_tx_transaction item;

    // Analysis port monitor.
    uvm_analysis_port #(uart_tx_transaction) tx_monitor_port;

    //Sample with Baudrate
    real    num_of_clk;
    real    sys_clk_period_ns;
    int     num_data_bits;

    // Global variable
    bit parity;
    bit received_parity;

    `uvm_component_utils(uart_tx_monitor)

    //Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tx_monitor_port = new("tx_monitor_port", this);

        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_tx_cfg", uart_tx_cfg) && uart_tx_cfg == null)
        `uvm_fatal("build_phase", "Cannot get UART TX configuration in monitor")
    endfunction : build_phase

    //Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase", UVM_HIGH)
        this.tx_if = uart_tx_cfg.tx_if;
    endfunction : connect_phase

    //Run phase
    virtual task run_phase(uvm_phase phase);
        uart_tx_transaction item;
        `uvm_info(this.get_full_name(), "Run Phase in TX monitor", UVM_HIGH)

        //Caculator the clk per bit
        sys_clk_period_ns = 1000000000.0 / uart_tx_cfg.frequency;
        num_of_clk = ((uart_tx_cfg.frequency)/(uart_tx_cfg.baudrate));
        `uvm_info("run_phase", $sformatf("baudrate = %0d num_of_clk = %0f", uart_tx_cfg.baudrate, num_of_clk), UVM_HIGH)

        forever begin
            item = uart_tx_transaction::type_id::create("item");
            
            // Wait start bit
            wait(tx_if.tx === 1'b0);
            #(num_of_clk * sys_clk_period_ns * 0.5ns);
            
            // // Glitch checking
            // if (tx_if.tx !== 1'b0) begin
            //      `uvm_warning("UART_TX_MON", "Glitch detected on Start Bit, ignoring...")
            //      continue; 
            // end
            #(num_of_clk * sys_clk_period_ns * 1ns);

            // Determine the number of data bits
            case (uart_tx_cfg.data_bit_num)
                UART_5BIT: num_data_bits = `UART_FRAME_5BIT;
                UART_6BIT: num_data_bits = `UART_FRAME_6BIT;
                UART_7BIT: num_data_bits = `UART_FRAME_7BIT;
                UART_8BIT: num_data_bits = `UART_FRAME_8BIT;
                default:   num_data_bits = `UART_FRAME_8BIT;
            endcase

            item.uart_tx_data_frame = '0;
            parity = 0; 

            // Collect Data
            for(int i = 0; i < num_data_bits; i++) begin
                item.uart_tx_data_frame[i] = tx_if.tx;
                `uvm_info("UART_TX_MON", $sformatf("Collect bit %0b", tx_if.tx), UVM_HIGH)
                parity ^= item.uart_tx_data_frame[i]; 
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end

            // Checking parity if parity is enable
            if (uart_tx_cfg.parity_en) begin
                received_parity = tx_if.tx;
                if(uart_tx_cfg.parity_type == UART_PARITY_ODD) 
                    parity = ~parity;
                if (received_parity !== parity) begin
                    if (!uart_tx_cfg.disable_parity_check_error) begin
                        `uvm_error("UART_TX_MON", $sformatf("Parity Error! Expected: %b, Received: %b", parity, received_parity))
                    end else begin
                        `uvm_info("UART_TX_MON", "Parity Error detected (Injected), suppressing UVM_ERROR...", UVM_HIGH)
                    end
                    item.parity_error = 1'b1; 
                end
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end

            // Colect and checking stop bit
            if (tx_if.tx !== 1'b1) begin
                `uvm_error("UART_TX_MON", "Framing Error! Stop bit is not HIGH.")
                item.stop_error = 1'b1;
            end
            if (uart_tx_cfg.stop_bit_num == UART_TWO_STOP_BIT) begin
                 #(num_of_clk * sys_clk_period_ns * 1ns);;
                 if (tx_if.tx !== 1'b1) 
                    `uvm_error("UART_TX_MON", "Framing Error! 2nd Stop bit is not HIGH.")
            end

            // Send the transaction
            `uvm_info("UART_TX_MON", $sformatf("Collected: %h", item.uart_tx_data_frame), UVM_HIGH)
            tx_monitor_port.write(item);
        end
    endtask : run_phase

endclass : uart_tx_monitor