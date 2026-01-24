class apb_master_configuration extends uvm_object;
    //APB interface
    virtual apb_master_itf  master_itf;

    //set active
    uvm_active_passive_enum is_active = UVM_ACTIVE;

    // Controll flag
    bit has_functional_coverage = 1;
    bit has_protocol_checker = 1;
    bit enable_pslverr_check = 1;

    // UVM macros
    `uvm_object_utils_begin(apb_master_configuration)
      `uvm_field_enum   (uvm_active_passive_enum,  is_active, UVM_ALL_ON)
      `uvm_field_int    (has_functional_coverage,             UVM_ALL_ON)
      `uvm_field_int    (has_protocol_checker,                UVM_ALL_ON)
      `uvm_field_int    (enable_pslverr_check,                UVM_ALL_ON)
    `uvm_object_utils_end

    // Contructor
    function new (string name = "apb_master_configuration");
        super.new(name);
    endfunction : new
endclass