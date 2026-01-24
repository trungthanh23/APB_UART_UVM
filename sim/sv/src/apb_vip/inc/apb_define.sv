`ifndef APB_ADDR_WIDTH
	`define APB_ADDR_WIDTH 12
`endif

`ifndef APB_DATA_WIDTH
	`define APB_DATA_WIDTH 32
`endif

`ifndef APB_STRB_WIDTH
	`define APB_STRB_WIDTH `APB_DATA_WIDTH/8
`endif

`define ADDR_TX_DATA   12'h00
`define ADDR_RX_DATA   12'h04
`define ADDR_CFG_REG   12'h08
`define ADDR_CTRL_REG  12'h0C
`define ADDR_STT_REG   12'h10

`define APB_DATA_FRAME_5BIT           5
`define APB_DATA_FRAME_6BIT           6
`define APB_DATA_FRAME_7BIT           7
`define APB_DATA_FRAME_8BIT           8

`define APB_CFG_ONE_STOP_BIT         1
`define APB_CFG_TWO_STOP_BIT         2

typedef enum bit [1:0] {
  APB_DATA_5BIT = 2'b00,
  APB_DATA_6BIT = 2'b01,
  APB_DATA_7BIT = 2'b10,
  APB_DATA_8BIT = 2'b11
} apb_data_bit_num_e;

typedef enum bit {
  APB_CFG_ONE_STOP_BIT = 0,
  APB_CFG_TWO_STOP_BIT = 1
} apb_stop_bit_num_e;

typedef enum bit {
  APB_CFG_PARITY_DIS = 0,
  APB_CFG_PARITY_EN = 1
} apb_parity_en_e;

typedef enum bit {
  APB_CFG_PARITY_ODD = 0,
  APB_CFG_PARITY_EVEN = 1
} apb_parity_type_e;

typedef logic [`APB_ADDR_WIDTH-1:0] apb_addr_t;
typedef logic [`APB_DATA_WIDTH-1:0] apb_data_t;
typedef logic [`APB_STRB_WIDTH-1:0] apb_strb_t;