class apb_base_seq extends uvm_sequence #(apb_master_transaction);
    
    // Factory
    `uvm_object_utils(apb_base_seq)

    string reg_name, data_desc;
    string d_str, s_str, p_str;
    bit [31:0] mask_val;

    // Contructor
    function new(string name = "apb_base_seq");
        super.new(name);
    endfunction : new

    // Pre Body
    task pre_body();
        uvm_phase phase;
        `ifdef UVM_VERSION_1_2
            phase = get_starting_phase();
        `else 
            phase = starting_phase;
        `endif 
        if(phase != null) begin
            phase.raise_objection(this, get_type_name());
            `uvm_info(get_type_name(), "raise objection", UVM_MEDIUM)
        end
        
    endtask : pre_body

    // Post Body
     task post_body();
        uvm_phase phase;
        `ifdef UVM_VERSION_1_2
            phase = get_starting_phase();
        `else 
            phase = starting_phase;
        `endif 
        if(phase != null) begin
            phase.drop_objection(this, get_type_name());
            `uvm_info(get_type_name(), "drop objection", UVM_MEDIUM)
        end
        
    endtask : post_body   

endclass : apb_base_seq

class apb_write_regs_seq extends apb_base_seq;
    `uvm_object_utils(apb_write_regs_seq)

    // Variable
    rand bit [11:0] addr;
    rand bit [31:0] data;

    // Field
    rand apb_data_bit_num_e   data_bit_num;
    rand apb_stop_bit_num_e   stop_bit_num;
    rand apb_parity_en_e      parity_en;
    rand apb_parity_type_e    parity_type;

    // Constraint
    constraint c_cfg_packing {
        (addr == `ADDR_CFG_REG) -> {
            data[1:0] == data_bit_num;
            data[2]   == stop_bit_num;
            data[3]   == parity_en;
            data[4]   == parity_type;
        }
    }

    constraint c_tx_data {
        (addr == `ADDR_TX_DATA) -> {data[31:8] == 0;}
    }

    constraint c_ctrl_data {
        (addr == `ADDR_CTRL_REG) -> {data[0] == 1'b1;}
    }

    // Factory
    function new(string name = "apb_write_regs_seq");
        super.new(name);
    endfunction : new

    // Body
    virtual task body();
        //apb_master_transaction tr;
        case(addr)
            `ADDR_CFG_REG:  reg_name = "CONFIG_REGISTER";
            `ADDR_TX_DATA:  reg_name = "UART_TX_DATA";
            `ADDR_CTRL_REG: reg_name = "CONTROL_REGISTER";
            default:        reg_name = "UNKNOWN_REGISTER";
        endcase

        if (addr == `ADDR_CFG_REG) begin
            //d_str = (data_bit_num == APB_DATA_8BIT) ? "" : "7-bit Data";
            case (data_bit_num)
                APB_DATA_8BIT: d_str = "8-bit Data";
                APB_DATA_7BIT: d_str = "7-bit Data";
                APB_DATA_6BIT: d_str = "6-bit Data";
                APB_DATA_5BIT: d_str = "5-bit Data";
                default:       d_str = "8-bit Data";
            endcase
            s_str = (stop_bit_num == APB_CFG_ONE_STOP_BIT) ? "1 Stop Bit" : "2 Stop Bits";
            p_str = (parity_en == APB_CFG_PARITY_DIS) ? "Parity Disabled" : $sformatf("Parity Enabled (%s)", (parity_type ? "Even" : "Odd"));
            data_desc = $sformatf("[%s, %s, %s]", d_str, s_str, p_str);
        end 
        else if (addr == `ADDR_CTRL_REG) begin
            data_desc = "START UART TX";
        end
        else begin
            case (data_bit_num)
                APB_DATA_5BIT: mask_val = 32'h1F; 
                APB_DATA_6BIT: mask_val = 32'h3F; 
                APB_DATA_7BIT: mask_val = 32'h7F; 
                default:       mask_val = 32'hFF; 
            endcase
            
            data_desc = $sformatf("Value: 0x%0h", data & mask_val);
        end

        `uvm_info("APB_WRITE_SEQ", $sformatf("\n\n====================\n=== [Write APB] ===\n%s - 0x%0h\n%s\n====================\n", reg_name, addr, data_desc), UVM_LOW)
        
        `uvm_do_with(req, {
            req.apb_addr.size()  == 1;
            req.apb_data.size()  == 1;
            req.apb_write.size() == 1;
            req.apb_strb.size()  == 1;
            req.apb_delay.size() == 1;
            req.apb_prdata.size()== 1;
            req.apb_addr[0]  == addr;
            req.apb_data[0]  == data;
            req.apb_write[0] == 1'b1;
            req.apb_strb[0]  == 4'hF;
            req.bus_len      == 1'b1;
        })
    endtask : body

endclass : apb_write_regs_seq

class apb_read_regs_seq extends apb_base_seq;

    // Factory
    `uvm_object_utils(apb_read_regs_seq)

    // Variable
    rand bit [11:0] addr;
    bit [31:0]      read_data;
    string          stt_desc; 

    //Contructor
    function new(string name = "apb_read_regs_seq");
        super.new(name);
    endfunction : new

    // Body
    virtual task body();

        case(addr)
            `ADDR_CFG_REG:  reg_name = "CONFIG_REGISTER";
            `ADDR_TX_DATA:  reg_name = "UART_TX_DATA";
            `ADDR_RX_DATA:  reg_name = "UART_RX_DATA";   
            `ADDR_CTRL_REG: reg_name = "CONTROL_REGISTER";
            `ADDR_STT_REG:  reg_name = "STATUS_REGISTER";   
            default:        reg_name = "UNKNOWN_REGISTER";
        endcase

        `uvm_do_with(req, {
            req.apb_addr.size()  == 1;
            req.apb_data.size()  == 1;
            req.apb_write.size() == 1;
            req.apb_strb.size()  == 1;
            req.apb_delay.size() == 1;
            req.apb_prdata.size()== 1;
            req.apb_addr[0]  == addr;   
            req.apb_write[0] == 1'b0;
            req.apb_strb[0]  == 4'h0;
            req.bus_len      == 1;
        })
        read_data = req.apb_prdata[0]; 
        //`uvm_info("APB_READ_SEQ", $sformatf("\n\n====================\n=== [Read APB] ===\n%s - 0x%0h\n%0h\n====================\n",reg_name, addr, read_data), UVM_MEDIUM)
        stt_desc = "";
        if (addr == `ADDR_STT_REG) begin
            if (read_data[1]) stt_desc = {stt_desc, " RX Done"};
            else              stt_desc = {stt_desc, " RX Not Done"};

            if (read_data[2]) stt_desc = {stt_desc, " Parity Error"};
            
            if (read_data[0]) stt_desc = {stt_desc, " TX Done"};
            
            if (read_data == 0) stt_desc = " [IDLE/OK]";

            stt_desc = {"Status:", stt_desc};
        end 
        else if (addr == `ADDR_RX_DATA) begin
            stt_desc = $sformatf("Value: 0x%02h", read_data);
        end

        `uvm_info("APB_READ_SEQ", $sformatf("\n\n====================\n=== [Read APB] ===\nReg: %s (0x%0h)\n%s\n====================\n", reg_name, addr, stt_desc), UVM_MEDIUM)
    endtask : body

endclass : apb_read_regs_seq

class apb_write_error_addr_seq extends apb_base_seq;
    `uvm_object_utils(apb_write_error_addr_seq)

    rand bit [11:0] addr;
    rand bit [31:0] data;

    // Constraint
    constraint c_error_addr {
        addr inside {12'h004, 12'h010} || (addr > 12'h010);
    }

    function new(string name = "apb_write_error_addr_seq");
        super.new(name);
    endfunction : new


    virtual task body();
        `uvm_info(get_type_name(), $sformatf("\n\n====================\nExecuting Error Write Sequence to Addr: 0x%0h\n\n====================", addr), UVM_LOW)
        
        `uvm_create(req)
        
        req.c_valid_uart_addr.constraint_mode(0); 

        if (!req.randomize() with {
            apb_addr[0]  == addr;      
            apb_data[0]  == data;
            apb_write[0] == 1'b1; 
            apb_strb[0]  == 4'hF;
            bus_len      == 1;
            apb_addr.size()  == 1;
            apb_data.size()  == 1;
            apb_write.size() == 1;
            apb_strb.size()  == 1;
            apb_delay.size() == 1;
            apb_prdata.size()== 1;
        }) begin
            `uvm_fatal("SEQ", "Randomization failed in apb_write_error_addr_seq")
        end

        `uvm_send(req)
    endtask : body

endclass : apb_write_error_addr_seq

// class apb_write_tx_data_seq extends apb_base_seq;
    
//     // Factory
//     `uvm_object_utils(apb_write_tx_data_seq)

//     apb_master_transaction  apb_trans;
//     rand bit [31:0]         data;


//     // Contructor
//     function new(string name = "apb_write_tx_data_seq");
//         super.new(name);
//     endfunction : new

//     // Body
//     virtual task body();
//         `uvm_info(get_type_name(), "Executing apb_write_data_seq sequence", UVM_LOW)
//         `uvm_do_with(apb_trans,
//         {   apb_trans.apb_addr  = `ADDR_TX_DATA;
//             apb_trans.apb_data  = data;
//             apb_trans.apb_write = 1'b1;
//             apb_trans.apb_strb  = 4'hF;
//         })
//         `uvm_info(get_type_name(), $sformatf("APB MASTER Write address: %0d data: %h %d", `ADDR_TX_DATA, data, data), UVM_MEDIUM)
//     endtask : body

// endclass : apb_write_tx_data_seq

// class apb_write_cfg_seq extends apb_base_seq;
    
//     // Factory
//     `uvm_object_utils(apb_write_cfg_seq)

//     // Variable
//     apb_master_transaction      apb_trans;
//     rand bit [31:0]             data;
//     rand data_bit_num_e [1:0]   data_bit_num;
//     rand stop_bit_num_e         stop_bit_num;
//     rand parity_en_e            parity_en;
//     rand parity_type_e          parity_type;

//     // Contraint
//     contraint c_data_cfg {
//         data[1:0]   == data_bit_num;
//         data[2]     == stop_bit_num;
//         data[3]     == parity_en;
//         data[4]     == parity_type;
//     }

//     // Contructor
//     function new(string name = "apb_write_cfg_seq");
//         super.new(name);
//     endfunction : new

//     // Body
//     virtual task body();
//         `uvm_info(get_type_name(), "Executing apb_write_data_seq sequence", UVM_LOW)
//         `uvm_do_with(apb_trans,
//         {   apb_trans.apb_addr  = `ADDR_CFG_REG;
//             apb_trans.apb_data  = data;
//             apb_trans.apb_write = 1'b1;
//             apb_trans.apb_strb  = 4'hF;
//         })
//         `uvm_info(get_type_name(), $sformatf("APB MASTER Write address: %0d data: %h %d", `ADDR_CFG_REG, data, data), UVM_MEDIUM)

//     endtask : body

// endclass : apb_write_cfg_seq

// class apb_write_ctrl_seq extends apb_base_seq;
//     // Factory
//     `uvm_object_utils(apb_write_ctrl_seq)

//     // Variable
//     apb_master_transaction      apb_trans;
//     rand bit [31:0]             data;

//     // Contructor
//     function new(string name = "apb_write_ctrl_seq");
//         super.new(name);
//     endfunction : new

//     // Body
//     virtual task body();
//         `uvm_info(get_type_name(), "Executing apb_write_data_seq sequence", UVM_LOW)
//         `uvm_do_with(apb_trans,
//         {   apb_trans.apb_addr       = `ADDR_CTRL_REG;
//             apb_trans.apb_data[0]    = 1'b1;
//             apb_trans.apb_data[31:1] = data[31:1];
//             apb_trans.apb_write      = 1'b1;
//             apb_trans.apb_strb       = 4'hF;
//         })
//         `uvm_info(get_type_name(), $sformatf("APB MASTER Write address: %0d data: %h %d", `ADDR_CTRL_REG, data, data), UVM_MEDIUM)

//     endtask : body

// endclass : apb_write_ctrl_seq

// class apb_read_rx_data_seq extends apb_base_seq;
//     // Factory
//     `uvm_object_utils(apb_read_rx_data_seq)

//     // Variable
//     apb_master_transaction      apb_trans;
//     bit [31:0]                  data;

//     // Contructor
//     function new(string name = "apb_read_rx_data_seq");
//         super.new(name);
//     endfunction : new

//     // Body
//     virtual task body();
//         `uvm_info(get_type_name(), "Executing apb_write_data_seq sequence", UVM_LOW)
//         `uvm_do_with(apb_trans,
//         {   apb_trans.apb_addr       = `ADDR_RX_DATA;
//             apb_trans.apb_write      = 1'b0;
//             apb_trans.apb_strb       = 4'hF;
//         })
//         data = apb_trans.apb_data;
//         `uvm_info(get_type_name(), $sformatf("APB MASTER Write address: %0d data: %h %d", `ADDR_RX_DATA, data, data), UVM_MEDIUM)

//     endtask : body

// endclass : apb_read_rx_data_seq



