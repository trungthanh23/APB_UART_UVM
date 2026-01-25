class uart_rx_monitor extends uvm_monitor;
    // UART RX Config
    uart_configuration  uart_rx_cfg;

    // UART RX Interface
    virtual uart_rx_if          rx_if;

    // Analysis port monitor
    uvm_analysis_port #(uart_rx_transaction) rx_monitor_port;

    //Sample with Baudrate
    real    num_of_clk;
    real    sys_clk_period_ns;

    // Global variable
    bit parity;
    int num_data_bits;

    `uvm_component_utils(uart_rx_monitor)

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        rx_monitor_port = new("rx_monitor_port", this);

        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_rx_cfg", uart_rx_cfg) && uart_rx_cfg == null)
        `uvm_fatal("build_phase", "Cannot get UART RX configuration in monitor")
    endfunction : build_phase

    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase", UVM_MEDIUM)
        this.rx_if = uart_rx_cfg.rx_if;
    endfunction : connect_phase

    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_rx_transaction item;
        `uvm_info(this.get_full_name(), "Run Phase in RX monitor", UVM_MEDIUM)

        //Caculator the clk per bit
        sys_clk_period_ns = 1000000000.0 / uart_rx_cfg.frequency;
        num_of_clk = ((uart_rx_cfg.frequency)/(uart_rx_cfg.baudrate));
        `uvm_info("run_phase", $sformatf("baudrate = %0d num_of_clk = %0f", uart_rx_cfg.baudrate, num_of_clk), UVM_MEDIUM)

        forever begin
            item = uart_rx_transaction::type_id::create("item");
            
            // Wait start bit
            @(negedge rx_if.rx);
            #(num_of_clk * sys_clk_period_ns * 0.5ns);
            
            // Glitch checking
            if (rx_if.driver_rx_cb.rx !== 1'b0) begin
                 `uvm_warning("UART_RX_MON", "Glitch detected on Start Bit, ignoring...")
                 continue; 
            end
            #(num_of_clk * sys_clk_period_ns * 1ns);

            // Determine the number of data bits
            case (uart_rx_cfg.data_bit_num)
                UART_5BIT: num_data_bits = `UART_FRAME_5BIT;
                UART_6BIT: num_data_bits = `UART_FRAME_6BIT;
                UART_7BIT: num_data_bits = `UART_FRAME_7BIT;
                UART_8BIT: num_data_bits = `UART_FRAME_8BIT;
                default:   num_data_bits = `UART_FRAME_8BIT;
            endcase

            item.uart_rx_data_frame = '0;
            parity = 0; 

            // Collect Data
            for(int i = 0; i < num_data_bits; i++) begin
                item.uart_rx_data_frame[i] = rx_if.driver_rx_cb.rx;
                `uvm_info("UART_RX_MON", $sformatf("Collect bit %0b", rx_if.driver_rx_cb.rx), UVM_HIGH)
                parity ^= item.uart_rx_data_frame[i]; 
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end
            `uvm_info("UART_RX_MON", $sformatf("\n\n============================\n=== COLLECTED DATA: 0x%h ===\n============================\n", item.uart_rx_data_frame), UVM_LOW)

            // Checking parity if parity is enable
            if (uart_rx_cfg.parity_en) begin
                if(uart_rx_cfg.parity_type == UART_PARITY_ODD) 
                    parity = ~parity;
                if (rx_if.driver_rx_cb.rx !== parity) begin
                    `uvm_error("UART_RX_MON", $sformatf("\n\n====================\nParity bit Error! Expected: %b, Received: %b\n====================\n", parity, rx_if.driver_rx_cb.rx))
                    item.parity_error = 1'b1; 
                end else begin
                    `uvm_info("UART_RX_MON", $sformatf("\n\n===========================\nParity bit deteced - %s\n===========================\n", (rx_if.driver_rx_cb.rx ? "Even" : "Odd")), UVM_MEDIUM)
                end
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end

            // Colect and checking stop bit
            if (rx_if.driver_rx_cb.rx !== 1'b1) begin
                `uvm_error("UART_RX_MON", "\n\n====================\nFraming Error! Stop bit is not HIGH.\n====================\n")
                item.stop_error = 1'b1;
            end else begin
                
            end
            if (uart_rx_cfg.stop_bit_num == UART_TWO_STOP_BIT) begin
                #(num_of_clk * sys_clk_period_ns * 1ns);
                if (rx_if.driver_rx_cb.rx !== 1'b1) 
                    `uvm_error("UART_RX_MON", "\n\n====================\nFraming Error! 2nd Stop bit is not HIGH.\n====================\n")
            end

            // Send the transaction
            `uvm_info("UART_RX_MON", $sformatf("\n\n====================\nCollected: %h\n====================\n", item.uart_rx_data_frame), UVM_HIGH)
            rx_monitor_port.write(item);
        end
    endtask : run_phase
    
endclass : uart_rx_monitor