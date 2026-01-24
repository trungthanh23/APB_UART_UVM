class uart_rx_driver extends uvm_driver #(uart_rx_transaction);
    
    //UART RX interface
    virtual uart_rx_if  rx_if;

    //UART RX config
    uart_configuration  uart_rx_cfg;

    //Variable for rx to create signals
    bit     rts_n;
    bit     parity;
    int     num_data_bits;
    real    num_of_clk;
    real    sys_clk_period_ns;

    `uvm_component_utils(uart_rx_driver)

    //Constructor
    function new(string name = "uart_rx_driver", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase to get config
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in RX driver", UVM_MEDIUM)
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_rx_cfg", uart_rx_cfg) && uart_rx_cfg == null)
            `uvm_fatal("build_phase", "Cannot get UART RX configuration in sequencer")
    endfunction : build_phase

    //Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in RX driver", UVM_MEDIUM)
        this.rx_if = uart_rx_cfg.rx_if;
    endfunction : connect_phase

    //Run phase
    task run_phase(uvm_phase phase);
        `uvm_info("run_phase", "Run Phase in RX driver", UVM_MEDIUM)
        sys_clk_period_ns = 1000000000.0 / uart_rx_cfg.frequency;
        num_of_clk = ((uart_rx_cfg.frequency) / (uart_rx_cfg.baudrate));
        
        // Handshake
        rx_if.rts_n <= 1; 

        forever begin
            wait(rx_if.reset_n === 1'b1);
            fork
                begin : DRIVER_LOGIC
                    get_and_sample_item();
                end

                begin : RESET_WATCHDOG
                    @(negedge rx_if.reset_n);
                    `uvm_info("UART_RX_DRV", "Reset detected during transaction!", UVM_MEDIUM)
                    rx_if.rts_n <= 1;
                end
            join_any
            disable fork; 
        end
    endtask : run_phase

    task get_and_sample_item();
        seq_item_port.get_next_item(req);
        
        // Init variables
        req.uart_rx_data_frame = '0;
        rx_if.uart_frame_rx = '0; 
        parity = 0;

        // Handshake
        rx_if.rts_n <= 0; 
        
        // Wait Start bit
        @(negedge rx_if.rx);
        
        // Delay to center of Start bit
        #(num_of_clk * sys_clk_period_ns * 0.5ns);
        
        // Glitch check
        if (rx_if.rx !== 1'b0) begin
            `uvm_warning("UART_RX_DRV", "Glitch on Start bit")
            seq_item_port.item_done(); 
            return; 
        end
        
        // Delay to center of D0
        #(num_of_clk * sys_clk_period_ns * 1ns);

        // Define number of data bits
        case (uart_rx_cfg.data_bit_num) 
            UART_5BIT: num_data_bits = `UART_FRAME_5BIT;
            UART_6BIT: num_data_bits = `UART_FRAME_6BIT;
            UART_7BIT: num_data_bits = `UART_FRAME_7BIT;
            UART_8BIT: num_data_bits = `UART_FRAME_8BIT;
            default:   num_data_bits = `UART_FRAME_8BIT;
        endcase

        // Sample Data
        for(int i = 0; i < num_data_bits; i++) begin
            req.uart_rx_data_frame[i] = rx_if.rx;
            parity = parity ^ rx_if.rx;
            rx_if.uart_frame_rx = req.uart_rx_data_frame; 
            #(num_of_clk * sys_clk_period_ns * 1ns);
        end

        // Check Parity
        if (uart_rx_cfg.parity_en) begin
            if (uart_rx_cfg.parity_type == UART_PARITY_ODD) 
                parity = ~parity;
            
            if (parity != rx_if.rx) 
                req.parity_error = 1; 
            #(num_of_clk * sys_clk_period_ns * 1ns);
        end

        // Handshake
        rx_if.rts_n <= 1; 

        // Check Stop bit
        if (uart_rx_cfg.stop_bit_num == UART_TWO_STOP_BIT) begin
            repeat(2) #(num_of_clk * sys_clk_period_ns * 1ns);
        end else begin
            #(num_of_clk * sys_clk_period_ns * 1ns);
        end

        seq_item_port.item_done(); 
    endtask

endclass