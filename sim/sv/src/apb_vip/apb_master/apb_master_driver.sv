class apb_master_driver extends uvm_driver #(apb_master_transaction);
    // UVM Factory
    `uvm_component_utils(apb_master_driver)

    // APB MASTER interface
    virtual apb_master_itf              master_itf;

    // APB MASTER configuration
    apb_master_configuration            master_cfg;

    // APB transaction
    int     item_count;

    // Contructor
    function new(string name = "apb_master_driver", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in APB MASTER driver", UVM_MEDIUM)
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(apb_master_configuration)::get(null, get_full_name(), "master_cfg", master_cfg) && master_cfg == null) begin
            `uvm_fatal("build_phase", "Cannot get APB MASTER configuration in driver")
        end

    endfunction : build_phase 

    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in APB MASTER driver", UVM_MEDIUM)
        this.master_itf = master_cfg.master_itf;
    endfunction : connect_phase

    // Run phase
    virtual task run_phase(uvm_phase phase);
        //Reset
        reset_signals();
        forever begin
            wait(master_itf.presetn === 1'b1); 

            fork
                begin : drive_process
                    forever begin
                        seq_item_port.get_next_item(req);
                        drive_transaction();
                        seq_item_port.item_done();
                    end
                end

                begin : reset_monitor
                    @(negedge master_itf.presetn);
                    reset_signals(); 
                end
            join_any

            disable fork; 
        end

    endtask : run_phase

    // Driver transaction
    task drive_transaction();
        `uvm_info("APB_MASTER_DRV",$sformatf("Item bus len: %0d", req.bus_len), UVM_HIGH)
        for (int i = 0; i < req.bus_len; i++) begin
            `uvm_info("APB_MASTER_DRV",$sformatf("Transaction number:  %0d", i), UVM_HIGH)
            repeat (req.apb_delay[i]) @(posedge master_itf.pclk);

            // Setup Phase 
            @(posedge master_itf.pclk);
            master_itf.psel    <= 1'b1;
            master_itf.penable <= 1'b0; 
            master_itf.paddr   <= req.apb_addr[i];
            master_itf.pwrite  <= req.apb_write[i];
            master_itf.pstrb   <= req.apb_strb[i];
            master_itf.pwdata  <= req.apb_write[i] ? req.apb_data[i] : 'b0;

            @(posedge master_itf.pclk);

            // Access Phase 
            master_itf.penable <= 1'b1;

            while (master_itf.pready !== 1'b1) begin
                @(posedge master_itf.pclk);
            end

            // Take error
            req.apb_pslverr[i] = master_itf.pslverr;

            // Take data if transaction is read
            if (!req.apb_write[i]) begin
                req.apb_prdata[i] = master_itf.prdata; 
            end

            // End transaction
            master_itf.penable <= 1'b0;
            if(i == req.bus_len - 1) begin
                master_itf.psel    <= 1'b0;
                @(posedge master_itf.pclk);
            end
        end
    endtask : drive_transaction

    // Reset signals
    task reset_signals();
        master_itf.psel    <= 1'b0;
        master_itf.penable <= 1'b0;
        master_itf.pwrite  <= 1'b0;
        master_itf.paddr   <= '0;
        master_itf.pwdata  <= '0;
        master_itf.pstrb   <= '0;
    endtask : reset_signals

endclass : apb_master_driver