class apb_master_monitor extends uvm_monitor;
    // APB MASTER interface
    virtual apb_master_itf              master_itf;

    // APB MASTER configuration
    apb_master_configuration            master_cfg;

    // Global variable
    int num_trans;

    // APB Factory
    `uvm_component_utils(apb_master_monitor)

    // APB TLM analysis port
    uvm_analysis_port #(apb_master_transaction) master_monitor_port;

    // Contruction
    function new(string name = "apb_master_monitor", uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in APB MASTER monitor", UVM_MEDIUM)
        super.build_phase(phase);
        master_monitor_port = new("master_monitor_port", this);

        // Get the config
        if (!uvm_config_db #(apb_master_configuration)::get(null, get_full_name(), "master_cfg", master_cfg) && master_cfg == null) begin
            `uvm_fatal("build_phase", "Cannot get APB MASTER configuration in monitor")
        end

    endfunction : build_phase 

    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Connect Phase in APB MASTER driver", UVM_MEDIUM)
        this.master_itf = master_cfg.master_itf;
    endfunction : connect_phase

    // Run phase 
    task run_phase(uvm_phase phase);
        apb_master_transaction item;
        `uvm_info(this.get_full_name(), "Run Phase in APB MASTER monitor", UVM_MEDIUM)
        num_trans = 0;

        forever begin
            @(posedge master_itf.pclk);

            if (master_itf.psel && master_itf.penable && master_itf.pready) begin
                item = apb_master_transaction::type_id::create("item");
                // Setup bus length
                void'(item.randomize() with {bus_len == 1;});

                // Take data from interface
                item.apb_write[0]   = master_itf.pwrite;
                item.apb_addr[0]    = master_itf.paddr;
                item.apb_pslverr[0] = master_itf.pslverr;

                if (master_itf.pwrite) begin
                    item.apb_pwdata[0] = master_itf.pwdata;
                end else begin
                    item.apb_prdata[0] = master_itf.prdata;
                end

                master_monitor_port.write(item);
                num_trans++;

                if (master_itf.pwrite) begin
                    `uvm_info("APB_MASTER_MON", "\n\n====================\nWrite analysis port done!\n====================\n", UVM_MEDIUM)
                end else begin
                    `uvm_info("APB_MASTER_MON", "\n\n====================\nRead analysis port done!\n====================\n", UVM_MEDIUM)
                end
                
            end
        end
        
    endtask : run_phase

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("APB_MASTER_MON", $sformatf("SUMMARY: %0d of APB transactions on the Bus have been collected.", num_trans), UVM_LOW)
    endfunction : report_phase

endclass