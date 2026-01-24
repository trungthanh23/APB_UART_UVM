class apb_master_agent extends uvm_agent;
    // UVM Factory
    `uvm_component_utils(apb_master_agent)

    // APB MASTER Components
    apb_master_driver           driver;
    apb_master_monitor          monitor;
    apb_master_sequencer        sequencer;
    apb_master_coverage         coverage;

    // APB MASTER Config
    apb_master_configuration    master_cfg;

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(this.get_full_name(), "Build Phase in APB MASTER agent", UVM_MEDIUM)
        
        if (!uvm_config_db#(apb_master_configuration)::get(this, "", "master_cfg", master_cfg))
            `uvm_fatal("build_phase", "Cannot get apb master configuration")

        monitor = apb_master_monitor::type_id::create("monitor", this); 

        // Conditional creation 
        if (master_cfg.has_functional_coverage) begin
            coverage = apb_master_coverage::type_id::create("coverage", this); 
        end

        if (master_cfg.is_active == UVM_ACTIVE) begin
            driver    = apb_master_driver::type_id::create("driver", this); 
            sequencer = apb_master_sequencer::type_id::create("sequencer", this); 
        end
    endfunction : build_phase

    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        monitor.master_itf = master_cfg.master_itf; 
        monitor.master_cfg = master_cfg; 

        // TLM Connection from Monitor to Coverage
        if (master_cfg.has_functional_coverage) begin
            monitor.master_monitor_port.connect(coverage.analysis_export); 
        end

        // TLM Connection from Driver to Sequencer
        if (master_cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export); 
            driver.master_itf = master_cfg.master_itf; 
            driver.master_cfg = master_cfg; 
            sequencer.master_cfg = master_cfg; 
        end
    endfunction : connect_phase

endclass : apb_master_agent