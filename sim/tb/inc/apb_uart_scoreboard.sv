`uvm_analysis_imp_decl(_apb)
`uvm_analysis_imp_decl(_uart_rx)
`uvm_analysis_imp_decl(_uart_tx)

class apb_uart_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(apb_uart_scoreboard)

  uart_configuration uart_cfg;

  virtual apb_master_itf apb_vif;

  bit [7:0] q_expect_dut_tx[$];
  bit [7:0] q_actual_dut_tx[$];

  bit [7:0] q_expect_dut_rx[$];
  bit [7:0] q_actual_dut_rx[$];

  bit [7:0] masked_data;
  bit [7:0] rx_masked_data;

  bit [31:0] dut_reg_val; 
  bit [1:0]  dut_data_bit_num;
  bit        dut_stop_bit_num;
  bit        dut_parity_en;
  bit        dut_parity_type;
  bit [7:0]  dut_tx_data;

  uvm_analysis_imp_apb     #(apb_master_transaction, apb_uart_scoreboard) apb_imp;
  uvm_analysis_imp_uart_rx #(uart_rx_transaction,    apb_uart_scoreboard) uart_rx_imp;
  uvm_analysis_imp_uart_tx #(uart_tx_transaction,    apb_uart_scoreboard) uart_tx_imp;

  function new(string name="apb_uart_scoreboard", uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    apb_imp     = new("apb_imp", this);
    uart_rx_imp = new("uart_rx_imp", this);
    uart_tx_imp = new("uart_tx_imp", this);
    if (!uvm_config_db #(uart_configuration)::get(this, "", "uart_cfg", uart_cfg)) begin
      uart_cfg = uart_configuration::type_id::create("uart_cfg");
    end
    if (!uvm_config_db #(virtual apb_master_itf)::get(this, "", "apb_vif", apb_vif)) begin
       `uvm_fatal("SCB", "Could not get virtual interface apb_vif")
    end
  endfunction

  virtual function void write_apb(apb_master_transaction item);
    int error_cfg = 0;

    case (uart_cfg.data_bit_num)
        UART_5BIT: masked_data = item.apb_data[0] & 8'h1F;
        UART_6BIT: masked_data = item.apb_data[0] & 8'h3F;
        UART_7BIT: masked_data = item.apb_data[0] & 8'h7F;
        default:   masked_data = item.apb_data[0] & 8'hFF;
    endcase

    if (item.apb_write[0] && item.apb_addr[0] == 12'h000) begin
        q_expect_dut_tx.push_back(masked_data);
        fork
            begin
                @(posedge apb_vif.pclk); 
                
                if (uvm_hdl_read("apb_uart_test_top.dut.tx_data", dut_tx_data)) begin
                    if (dut_tx_data !== item.apb_data[0][7:0]) begin
                         `uvm_error("SCB_APB_FAIL", $sformatf("\n\n==========================\n!!! Register Update Fail !!! Addr: 0x00 \nWrote: %h, DUT holds: %h\n==========================\n", item.apb_data[0][7:0], dut_tx_data))
                    end else begin
                         `uvm_info("SCB_APB_PASS", "\n\n==========================\nRegister TX_DATA Update OK\n==========================\n", UVM_MEDIUM)
                    end
                end
            end
        join_none
    end
    else if (item.apb_write[0] && item.apb_addr[0] == 12'h008) begin
        fork
             begin
                @(posedge apb_vif.pclk);
                
                void'(uvm_hdl_read("apb_uart_test_top.dut.data_bit_num", dut_data_bit_num));
                void'(uvm_hdl_read("apb_uart_test_top.dut.stop_bit_num", dut_stop_bit_num));
                void'(uvm_hdl_read("apb_uart_test_top.dut.parity_en",    dut_parity_en));
                void'(uvm_hdl_read("apb_uart_test_top.dut.parity_type",  dut_parity_type));

                if (dut_data_bit_num !== item.apb_data[0][1:0]) begin
                  error_cfg++;
                  `uvm_error("SCB_APB_FAIL", $sformatf("\n\n==========================\nConfig: data_bit_num update wrong!\nWrite: %0b\n==========================\n", dut_data_bit_num))
                end

                if (dut_stop_bit_num !== item.apb_data[0][2]) begin 
                  error_cfg++;
                  `uvm_error("SCB_APB_FAIL", $sformatf("\n\n==========================\nConfig: stop_bit_num update wrong!\nWrite: %0b\n==========================\n", dut_stop_bit_num))
                end

                if (dut_parity_en !== item.apb_data[0][3]) begin
                  error_cfg++;
                  `uvm_error("SCB_APB_FAIL", $sformatf("\n\n==========================\nConfig: parity_en update wrong!\nWrite: %0b\n==========================\n", dut_parity_en))
                end

                if ((dut_parity_type !== item.apb_data[0][4]) && item.apb_data[0][3]) begin
                  error_cfg++;
                  `uvm_error("SCB_APB_FAIL", $sformatf("\n\n==========================\nConfig: parity_type update wrong!\nWrite: %0b\n==========================\n", dut_parity_type))
                end
                
                if (error_cfg == 0) begin
                  `uvm_info("SCB_APB_PASS", "\n\n==========================\nRegister CONFIG Update OK\n==========================\n", UVM_MEDIUM)
                end
             end
        join_none
    end
    else if (item.apb_write[0] == 1'b0 && item.apb_addr[0] == 12'h004) begin
      q_actual_dut_rx.push_back(masked_data);
    end
  endfunction : write_apb

  // VIP RX 
  virtual function void write_uart_rx(uart_rx_transaction item);
    q_actual_dut_tx.push_back(item.uart_rx_data_frame);
  endfunction : write_uart_rx

  // VIP TX
  virtual function void write_uart_tx(uart_tx_transaction item);

    case (uart_cfg.data_bit_num)
        UART_5BIT: rx_masked_data = item.uart_tx_data_frame & 8'h1F;
        UART_6BIT: rx_masked_data = item.uart_tx_data_frame & 8'h3F;
        UART_7BIT: rx_masked_data = item.uart_tx_data_frame & 8'h7F;
        default:   rx_masked_data = item.uart_tx_data_frame & 8'hFF;
    endcase

    q_expect_dut_rx.push_back(rx_masked_data);
  endfunction : write_uart_tx

  task run_phase(uvm_phase phase);
    fork
        check_dut_tx();
        check_dut_rx();
    join
  endtask : run_phase

  task check_dut_tx();
    bit [7:0] exp, act;
    forever begin
      wait(q_expect_dut_tx.size() > 0 && q_actual_dut_tx.size() > 0);
      exp = q_expect_dut_tx.pop_front();
      act = q_actual_dut_tx.pop_front();

      if (exp !== act)
        `uvm_error("SCB_TX_FAIL", $sformatf("\n\n====================\n!!! DUT TX Mismatch !!!\nAPB VIP Wrote: 0x%0h\nDUT Sent: 0x%0h\n====================\n", exp, act))
      else
        `uvm_info("SCB_TX_PASS", $sformatf("\n\n====================\n=== DUT TX Match ===\nSend: 0x%0h\n====================\n", exp), UVM_LOW)
    end
  endtask

  task check_dut_rx();
    bit [7:0] exp, act;
    forever begin
      wait(q_expect_dut_rx.size() > 0 && q_actual_dut_rx.size() > 0);
      exp = q_expect_dut_rx.pop_front();
      act = q_actual_dut_rx.pop_front();

      if (exp !== act)
        `uvm_error("SCB_RX_FAIL", $sformatf("\n\n====================\n!!! DUT RX Mismatch !!!\nUART VIP Sent: 0x%0h\nAPB Read: 0x%0h\n====================\n", exp, act))
      else
        `uvm_info("SCB_RX_PASS", $sformatf("\n\n====================\n=== DUT RX Match ===\nReceive: 0x%0h\n====================\n", exp), UVM_LOW)
    end
  endtask

endclass