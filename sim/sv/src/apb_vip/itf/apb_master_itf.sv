`include "apb_define.sv"
interface apb_master_itf();
  logic                         pclk;
  logic                         presetn;
  logic [`APB_ADDR_WIDTH-1:0]   paddr;
  logic [`APB_DATA_WIDTH-1:0]   prdata;
  logic [`APB_DATA_WIDTH-1:0]   pwdata;
  logic [`APB_STRB_WIDTH-1:0]   pstrb;
  logic                         psel;
  logic                         penable;
  logic                         pwrite;
  logic                         pready;
  logic                         pslverr;

  modport master_mp_itf (
    input   pclk,
    input   presetn,
    input   pready,
    input   prdata,
    input   pslverr,  
    output  pstrb, 
    output  psel, 
    output  penable, 
    output  pwrite, 
    output  paddr, 
    output  pwdata
  );
endinterface