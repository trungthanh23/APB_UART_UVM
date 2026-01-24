`ifndef UART_DEFINE_SV   
`define UART_DEFINE_SV

`define UART_BAUDRATE_1200        1200
`define UART_BAUDRATE_2400        2400
`define UART_BAUDRATE_4800        4800
`define UART_BAUDRATE_9600        9600
`define UART_BAUDRATE_19200       19200
`define UART_BAUDRATE_38400       38400
`define UART_BAUDRATE_56000       56000
`define UART_BAUDRATE_57600       57600
`define UART_BAUDRATE_115200      115200
`define UART_BAUDRATE_128000      128000
`define UART_BAUDRATE_153600      153600
`define UART_BAUDRATE_230400      230400

`define UART_MAX_DATA_WIDTH       8
`define UART_FRAME_5BIT           5
`define UART_FRAME_6BIT           6
`define UART_FRAME_7BIT           7
`define UART_FRAME_8BIT           8

`define UART_ONE_STOP_BIT         1
`define UART_TWO_STOP_BIT         2

typedef enum bit [1:0] {
  UART_5BIT = 2'b00,
  UART_6BIT = 2'b01,
  UART_7BIT = 2'b10,
  UART_8BIT = 2'b11
} data_bit_num_e;

typedef enum bit {
  UART_ONE_STOP_BIT = 0,
  UART_TWO_STOP_BIT = 1
} stop_bit_num_e;

typedef enum bit {
  UART_PARITY_DIS = 0,
  UART_PARITY_EN = 1
} parity_en_e;

typedef enum bit {
  UART_PARITY_ODD = 0,
  UART_PARITY_EVEN = 1
} parity_type_e;

typedef logic [`UART_MAX_DATA_WIDTH - 1 : 0] uart_data_frame_t;

`endif