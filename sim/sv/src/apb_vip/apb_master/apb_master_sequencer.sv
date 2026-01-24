class apb_master_sequencer extends uvm_sequencer #(apb_master_transaction);

    // UVM Factory
    `uvm_component_utils(apb_master_sequencer)

    //Config for sequences
    apb_master_configuration    master_cfg;

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), "Build Phase in APB MASTER sequencer", UVM_MEDIUM)
        super.build_phase(phase);

        // Get the config
        if (!uvm_config_db #(apb_master_configuration)::get(null, get_full_name(), "master_cfg", master_cfg) && master_cfg == null) begin
            `uvm_fatal("build_phase", "Cannot get APB MASTER configuration in sequencer")
        end

    endfunction : build_phase

endclass : apb_master_sequencer