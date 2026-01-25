class uart_tx_driver extends uvm_driver #(uart_tx_transaction);

    //UART TX interface
    virtual uart_tx_if  tx_if;

    //UART TX config
    uart_configuration  uart_tx_cfg;

    //Variable for tx to create signals
    bit     stop;
    bit     parity;
    int     num_data_bits;
    real    num_of_clk;
    real    sys_clk_period_ns;

    // String log
    string d_str, s_str, p_str;

    // UVM Factory
    `uvm_component_utils(uart_tx_driver)

    //Constructor
    function new(string name = "uart_tx_driver", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //Build phase to get config
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in UART TX driver", UVM_MEDIUM)
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_tx_cfg", uart_tx_cfg) && uart_tx_cfg == null)
            `uvm_fatal("build_phase", "Cannot get UART TX configuration in sequencer")
    endfunction : build_phase

    //Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in TX driver", UVM_MEDIUM)
        this.tx_if = uart_tx_cfg.tx_if;
    endfunction : connect_phase

    // Run phase
    task run_phase(uvm_phase phase);
        `uvm_info("run_phase", "Run Phase in TX driver", UVM_MEDIUM)
        
        // Reset signals
        `uvm_info("run_phase", "Reset signal is asserted", UVM_DEBUG)
        reset_signals();

        //Caculator the clk per bit
        sys_clk_period_ns = 1000000000.0 / uart_tx_cfg.frequency;
        num_of_clk = ((uart_tx_cfg.frequency)/(uart_tx_cfg.baudrate));
        `uvm_info("run_phase", $sformatf("baudrate = %0d num_of_clk = %0f", uart_tx_cfg.baudrate, num_of_clk), UVM_MEDIUM)

        forever begin
            wait(tx_if.reset_n === 1'b1);
            fork
                begin
                    get_and_drive(); 
                end
                begin
                    @(negedge tx_if.reset_n);
                    `uvm_info("UART_TX_DRV", "Reset detected!", UVM_MEDIUM)
                    //wait(tx_if.reset_n === 1'b0);
                end
            join_any 

            disable fork; 

            if (tx_if.reset_n === 1'b0) begin
                reset_signals();
                //if (req != null) seq_item_port.item_done(); 
            end
        end
    endtask : run_phase

    //Reset 
    task reset_signals();
        tx_if.tx <= 1;
        tx_if.uart_frame_tx <= '0;
    endtask : reset_signals

    //Get and Drive
    task get_and_drive();
        //wait the reset is posedge
        wait(tx_if.reset_n === 1'b1);
        forever begin
            seq_item_port.get_next_item(req);
            //`uvm_info(get_type_name(), $sformatf("Driving UART TX Transaction:\n%s", req.sprint()), UVM_MEDIUM)

            // Define the data number bits
            case (uart_tx_cfg.data_bit_num)
                UART_5BIT: begin
                    num_data_bits = `UART_FRAME_5BIT;
                    d_str         =  "5-bit";
                end
                UART_6BIT: begin 
                    num_data_bits = `UART_FRAME_6BIT;
                    d_str         =  "6-bit";
                end
                UART_7BIT: begin
                    num_data_bits = `UART_FRAME_7BIT;
                    d_str         =  "7-bit";
                end
                UART_8BIT: begin
                    num_data_bits = `UART_FRAME_8BIT;
                    d_str         =  "8-bit";
                end
                default: begin
                    num_data_bits = `UART_FRAME_8BIT;
                    d_str         =  "8-bit";
                end
            endcase

            p_str = (uart_tx_cfg.parity_en) ? 
                                $sformatf("Parity(%s)", uart_tx_cfg.parity_type.name()) : "No-Parity";
            s_str = (uart_tx_cfg.stop_bit_num == UART_TWO_STOP_BIT) ? "2-stop" : "1-stop";

            `uvm_info("UART_TX_DRV", $sformatf("\n\n====================\nDriving UART TX Transaction: \nData = 0x%h\nDATA FRAME: [%s, %s, %s]\n====================\n", 
                                    req.uart_tx_data_frame, d_str, p_str, s_str), UVM_LOW)

            parity = 0;
            // Wait RX ready
            `uvm_info("run_phase", "Wait RX ready", UVM_MEDIUM)
            wait(tx_if.cts_n === 0);
            @(negedge tx_if.clk);

           // Start transfer
            tx_if.tx = 1'b0;
            tx_if.uart_frame_tx = req.uart_tx_data_frame;
            `uvm_info("UART_TX_DRV", $sformatf("\n\n====================\nStart transfer\n====================\n"), UVM_MEDIUM)
            #(num_of_clk * sys_clk_period_ns * 1ns);
            
            // Driving the data
            //Support for 5,6,7,8 bit data
            for(int i = 0; i < num_data_bits; i++) begin
                parity = parity ^ req.uart_tx_data_frame[i];
                tx_if.tx <= req.uart_tx_data_frame[i];
                `uvm_info("UART_TX_DRV", $sformatf(" Drive bit %0b", req.uart_tx_data_frame[i]), UVM_HIGH)
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end

            //Parity bit calculation and drive it
            if (uart_tx_cfg.parity_en) begin
              if (uart_tx_cfg.parity_type == UART_PARITY_ODD) begin
                parity = ~parity;
              end
              if (req.inject_parity_error) begin
                `uvm_info("UART_TX_DRV", "\n\n====================\nInjecting Parity Error...\n====================\n", UVM_MEDIUM)
                parity = ~parity; 
            end
              tx_if.tx <= parity;
              `uvm_info("UART_TX_DRV", $sformatf("\n\n====================\nDrive parity_bit %0b\n====================\n", parity), UVM_MEDIUM)
              #(num_of_clk * sys_clk_period_ns * 1ns);
            end

            // Stop condition
            repeat (uart_tx_cfg.stop_bit_num == UART_TWO_STOP_BIT ? 2 : 1) begin
                tx_if.tx <= req.inject_stop_error ? 1'b0 : 1'b1;
                #(num_of_clk * sys_clk_period_ns * 1ns);
            end
            `uvm_info("UART_TX_DRV", "\n\n==============================\nDone tx vip transaction send to rx\n==============================\n", UVM_MEDIUM)
            seq_item_port.item_done();
        end
    endtask : get_and_drive

endclass : uart_tx_driver