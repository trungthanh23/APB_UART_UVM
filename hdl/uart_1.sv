
module uart (clk,reset_n,pclk,preset_n,psel,penable,pwrite,pstrb,paddr,pwdata,rx,cts_n,pready,pslverr,prdata,tx,rts_n);
input   clk ;
input   reset_n ;
input   pclk ;
input   preset_n ;
input   psel ;
input   penable ;
input   pwrite ;
input  [3:0] pstrb ;
input  [11:0] paddr ;
input  [31:0] pwdata ;
input   rx ;
input   cts_n ;
output   pready ;
output   pslverr ;
output  [31:0] prdata ;
output   tx ;
output   rts_n ;
wire   clk_tx ;
wire   clk_rx ;
wire  [7:0] tx_data ;
wire  [7:0] rx_data ;
wire  [1:0] data_bit_num ;
wire   stop_bit_num ;
wire   parity_en ;
wire   parity_type ;
wire   start_tx ;
wire   tx_done ;
wire   rx_done ;
wire   parity_error ;
wire   clear_start_tx ;
wire   Tpl_30 ;
wire   Tpl_31 ;
wire   Tpl_32 ;
wire   Tpl_33 ;
wire  [7:0] Tpl_34 ;
wire  [1:0] Tpl_35 ;
wire   Tpl_36 ;
wire   Tpl_37 ;
wire   Tpl_38 ;
wire   Tpl_39 ;
logic   Tpl_40 ;
logic   Tpl_41 ;
logic   Tpl_42 ;
logic  [1:0] Tpl_43 ;
logic  [1:0] Tpl_44 ;
logic  [2:0] Tpl_45 ;
logic  [2:0] Tpl_46 ;
logic  [1:0] Tpl_47 ;
logic  [1:0] Tpl_48 ;
logic  [7:0] Tpl_49 ;
wire   Tpl_50 ;
wire   Tpl_51 ;
wire   Tpl_52 ;
wire   Tpl_53 ;
wire  [1:0] Tpl_54 ;
wire   Tpl_55 ;
wire   Tpl_56 ;
wire   Tpl_57 ;
wire  [7:0] Tpl_58 ;
wire   Tpl_59 ;
logic   Tpl_60 ;
logic   Tpl_61 ;
logic  [1:0] Tpl_62 ;
logic  [1:0] Tpl_63 ;
logic  [3:0] Tpl_64 ;
logic  [3:0] Tpl_65 ;
logic  [1:0] Tpl_66 ;
logic  [3:0] Tpl_67 ;
logic  [1:0] Tpl_68 ;
logic  [7:0] Tpl_69 ;
logic   Tpl_70 ;
logic   Tpl_71 ;
wire   Tpl_72 ;
wire   Tpl_73 ;
wire   Tpl_74 ;
wire   Tpl_75 ;
wire   Tpl_76 ;
wire   Tpl_77 ;
wire  [3:0] Tpl_78 ;
wire  [11:0] Tpl_79 ;
wire  [31:0] Tpl_80 ;
wire   Tpl_81 ;
logic   Tpl_82 ;
logic  [31:0] Tpl_83 ;
wire   Tpl_84 ;
wire   Tpl_85 ;
logic  [7:0] Tpl_86 ;
wire  [7:0] Tpl_87 ;
logic  [1:0] Tpl_88 ;
logic   Tpl_89 ;
logic   Tpl_90 ;
logic   Tpl_91 ;
logic   Tpl_92 ;
wire   Tpl_93 ;
wire   Tpl_94 ;
wire   Tpl_95 ;
wire   Tpl_96 ;
wire   Tpl_97 ;
wire   Tpl_98 ;
wire   Tpl_99 ;
wire   Tpl_100 ;
wire   Tpl_101 ;
wire   Tpl_102 ;
wire   Tpl_103 ;
wire   Tpl_104 ;
wire   Tpl_105 ;
wire   Tpl_106 ;
logic   Tpl_107 ;
logic   Tpl_108 ;
logic   Tpl_109 ;
logic  [7:0] Tpl_110 ;
wire  [31:0] Tpl_111 ;
wire  [31:0] Tpl_112 ;
wire  [31:0] Tpl_113 ;
wire  [31:0] Tpl_114 ;
wire  [31:0] Tpl_115 ;
logic   Tpl_116 ;
logic   Tpl_117 ;
wire   Tpl_118 ;
wire   Tpl_119 ;
wire   Tpl_120 ;
wire   Tpl_121 ;
logic  [4:0] Tpl_122 ;
logic  [8:0] Tpl_123 ;


assign Tpl_30 = clk;
assign Tpl_31 = reset_n;
assign Tpl_32 = clk_tx;
assign Tpl_33 = cts_n;
assign Tpl_34 = tx_data;
assign Tpl_35 = data_bit_num;
assign Tpl_36 = stop_bit_num;
assign Tpl_37 = parity_en;
assign Tpl_38 = parity_type;
assign Tpl_39 = start_tx;
assign tx = Tpl_40;
assign tx_done = Tpl_41;
assign clear_start_tx = Tpl_42;

assign Tpl_50 = clk;
assign Tpl_51 = reset_n;
assign Tpl_52 = clk_rx;
assign Tpl_53 = rx;
assign Tpl_54 = data_bit_num;
assign Tpl_55 = stop_bit_num;
assign Tpl_56 = parity_en;
assign Tpl_57 = parity_type;
assign rx_data = Tpl_58;
assign rts_n = Tpl_59;
assign rx_done = Tpl_60;
assign parity_error = Tpl_61;

assign Tpl_73 = pclk;
assign Tpl_74 = preset_n;
assign Tpl_75 = psel;
assign Tpl_76 = penable;
assign Tpl_77 = pwrite;
assign Tpl_78 = pstrb;
assign Tpl_79 = paddr;
assign Tpl_80 = pwdata;
assign pready = Tpl_81;
assign pslverr = Tpl_82;
assign prdata = Tpl_83;
assign Tpl_84 = clk;
assign Tpl_85 = reset_n;
assign tx_data = Tpl_86;
assign Tpl_87 = rx_data;
assign data_bit_num = Tpl_88;
assign stop_bit_num = Tpl_89;
assign parity_en = Tpl_90;
assign parity_type = Tpl_91;
assign start_tx = Tpl_92;
assign Tpl_93 = tx_done;
assign Tpl_94 = rx_done;
assign Tpl_95 = parity_error;
assign Tpl_96 = clear_start_tx;

assign Tpl_118 = clk;
assign Tpl_119 = reset_n;
assign clk_tx = Tpl_120;
assign clk_rx = Tpl_121;

always @(*)
begin
case (Tpl_35)
2'b00: begin
Tpl_45 = 3'd4;
Tpl_49 = Tpl_34[4:0];
end
2'b01: begin
Tpl_45 = 3'd5;
Tpl_49 = Tpl_34[5:0];
end
2'b10: begin
Tpl_45 = 3'd6;
Tpl_49 = Tpl_34[6:0];
end
2'b11: begin
Tpl_45 = 3'd7;
Tpl_49 = Tpl_34[7:0];
end
default: Tpl_45 = 3'd7;
endcase
end


always @(*)
begin
case ({{Tpl_37,Tpl_36}})
2'b00: Tpl_47 = 2'd0;
2'b01: Tpl_47 = 2'd1;
2'b10: Tpl_47 = 2'd1;
2'b11: Tpl_47 = 2'd2;
default: Tpl_47 = 2'd0;
endcase
end


always @( posedge Tpl_30 or negedge Tpl_31 )
begin
if ((~Tpl_31))
begin
Tpl_43 <= 2'b00;
end
else
begin
Tpl_43 <= Tpl_44;
case (Tpl_43)
2'b00: begin
Tpl_46 <= 0;
Tpl_48 <= 0;
end
2'b10: begin
if (Tpl_32)
begin
Tpl_46 <= (Tpl_46 + 1);
end
else
Tpl_46 <= Tpl_46;
end
2'b11: begin
if (Tpl_32)
begin
Tpl_48 <= (Tpl_48 + 1);
end
else
Tpl_48 <= Tpl_48;
end
default: begin
Tpl_46 <= 0;
Tpl_48 <= 0;
end
endcase
end
end


always @(*)
begin
case (Tpl_43)
2'b00: begin
if (((Tpl_39 && (!Tpl_33)) && Tpl_32))
begin
Tpl_44 = 2'b01;
Tpl_42 = 1;
end
else
Tpl_44 = 2'b00;
end
2'b01: begin
Tpl_42 = 0;
if (Tpl_32)
begin
Tpl_44 = 2'b10;
end
else
Tpl_44 = 2'b01;
end
2'b10: begin
if (Tpl_32)
begin
if ((Tpl_46 == Tpl_45))
begin
Tpl_44 = 2'b11;
end
else
Tpl_44 = 2'b10;
end
else
Tpl_44 = 2'b10;
end
2'b11: begin
if (Tpl_32)
begin
if ((Tpl_48 == Tpl_47))
begin
Tpl_44 = 2'b00;
end
else
Tpl_44 = 2'b11;
end
else
Tpl_44 = 2'b11;
end
default: Tpl_44 = 2'b00;
endcase
end


always @(*)
begin
case (Tpl_43)
2'b00: begin
Tpl_40 = 1'b1;
end
2'b01: begin
Tpl_40 = 1'b0;
end
2'b10: begin
Tpl_40 = Tpl_34[Tpl_46];
end
2'b11: begin
if ((Tpl_37 && (Tpl_48 == 0)))
begin
Tpl_40 = (Tpl_38 ? (^Tpl_49) : (~^Tpl_49));
end
else
Tpl_40 = 1'b1;
end
default: Tpl_40 = 1'b1;
endcase
end


always @( posedge Tpl_30 or negedge Tpl_31 )
begin
if ((~Tpl_31))
begin
Tpl_41 <= 1;
end
else
begin
if (Tpl_32)
begin
if ((((Tpl_43 == 2'b11) && (Tpl_48 == Tpl_47)) || (Tpl_43 == 2'b00)))
begin
Tpl_41 <= 1;
end
else
Tpl_41 <= 0;
end
else
Tpl_41 <= Tpl_41;
end
end


always @(*)
begin
case (Tpl_54)
2'b00: Tpl_65 = 4'd5;
2'b01: Tpl_65 = 4'd6;
2'b10: Tpl_65 = 4'd7;
2'b11: Tpl_65 = 4'd8;
default: Tpl_65 = 4'd8;
endcase
end


always @(*)
begin
case ({{Tpl_56,Tpl_55}})
2'b00: Tpl_66 = 2'd1;
2'b01: Tpl_66 = 2'd2;
2'b10: Tpl_66 = 2'd2;
2'b11: Tpl_66 = 2'd3;
default: Tpl_66 = 2'd1;
endcase
end


always @(*)
begin
case (Tpl_62)
2'b11: begin
if ((!Tpl_53))
Tpl_63 = 2'b00;
else
Tpl_63 = 2'b11;
end
2'b00: begin
if ((Tpl_64 == 15))
begin
Tpl_63 = 2'b01;
end
else
Tpl_63 = 2'b00;
end
2'b01: begin
if (((Tpl_64 == 15) && (Tpl_67 == Tpl_65)))
begin
Tpl_63 = 2'b10;
end
else
Tpl_63 = 2'b01;
end
2'b10: begin
if (((Tpl_64 == 15) && (Tpl_68 == Tpl_66)))
begin
Tpl_63 = 2'b11;
end
else
Tpl_63 = 2'b10;
end
default: Tpl_63 = 2'b11;
endcase
end


always @( posedge Tpl_50 or negedge Tpl_51 )
begin
if ((~Tpl_51))
begin
Tpl_62 <= 2'b11;
Tpl_67 <= 0;
Tpl_68 <= 0;
Tpl_64 <= 0;
Tpl_71 <= 0;
end
else
begin
Tpl_62 <= Tpl_63;
case (Tpl_62)
2'b11: begin
Tpl_64 <= 0;
Tpl_71 <= 0;
end
2'b00: begin
Tpl_67 <= 0;
Tpl_68 <= 0;
if (Tpl_52)
begin
Tpl_64 <= (Tpl_64 + 1'b1);
if ((Tpl_64 == 15))
begin
Tpl_64 <= 0;
end
end
else
Tpl_64 <= Tpl_64;
end
2'b01: begin
if (Tpl_52)
begin
Tpl_64 <= (Tpl_64 + 1'b1);
if ((Tpl_64 == 8))
begin
Tpl_67 <= (Tpl_67 + 1);
Tpl_69[Tpl_67] <= Tpl_53;
Tpl_71 <= (Tpl_71 ^ Tpl_53);
end
else
if ((Tpl_64 == 15))
begin
Tpl_64 <= 0;
end
end
else
Tpl_64 <= Tpl_64;
end
2'b10: begin
if (Tpl_52)
begin
Tpl_64 <= (Tpl_64 + 1);
if ((Tpl_64 == 8))
begin
Tpl_68 <= (Tpl_68 + 1);
end
else
if ((Tpl_64 == 15))
begin
Tpl_64 <= 0;
end
end
else
Tpl_64 <= Tpl_64;
end
endcase
end
end


always @(*)
begin
case (Tpl_62)
2'b11: begin
Tpl_60 = 1;
end
2'b00: begin
Tpl_60 = 1;
end
2'b01: begin
Tpl_60 = 0;
end
2'b10: begin
Tpl_60 = ((Tpl_64 == 15) && (Tpl_68 == Tpl_66));
if (((Tpl_68 == 0) && Tpl_56))
begin
Tpl_70 = Tpl_53;
end
Tpl_61 = (Tpl_56 ? (Tpl_57 ? (Tpl_71 != Tpl_70) : ((~Tpl_71) != Tpl_70)) : 1'b0);
end
default: begin
Tpl_60 = 0;
end
endcase
end

assign Tpl_59 = (~Tpl_60);
assign Tpl_58 = Tpl_69;
assign Tpl_97 = ((Tpl_75 && (~Tpl_77)) && Tpl_76);
assign Tpl_98 = ((Tpl_75 && Tpl_77) && Tpl_76);
assign Tpl_81 = ((Tpl_75 == 1'b1) ? ((Tpl_77 & Tpl_116) | ((~Tpl_77) & Tpl_117)) : 0);
assign Tpl_99 = (Tpl_97 && (Tpl_79 == 0));
assign Tpl_100 = (Tpl_98 && (Tpl_79 == 0));
assign Tpl_101 = (Tpl_97 && (Tpl_79 == 4));
assign Tpl_102 = (Tpl_97 && (Tpl_79 == 8));
assign Tpl_103 = (Tpl_98 && (Tpl_79 == 8));
assign Tpl_104 = (Tpl_97 && (Tpl_79 == 12));
assign Tpl_105 = (Tpl_98 && (Tpl_79 == 12));
assign Tpl_106 = (Tpl_97 && (Tpl_79 == 16));

always @(*)
begin
if ((!Tpl_98))
begin
Tpl_116 = 1'b0;
end
else
begin
Tpl_116 = 1'b1;
end
end


always @(*)
begin
if ((!Tpl_97))
begin
Tpl_117 = 1'b0;
end
else
begin
Tpl_117 = 1'b1;
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_tx_write_data_75
if ((~Tpl_85))
begin
Tpl_86 <= 0;
end
else
if (Tpl_100)
begin
if (Tpl_78[0])
Tpl_86 <= Tpl_80[7:0];
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_data_bit_num_78
if ((~Tpl_85))
begin
Tpl_88 <= 2'b00;
end
else
if (Tpl_103)
begin
if (Tpl_78[0])
Tpl_88 <= Tpl_80[1:0];
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_stop_bit_num_81
if ((~Tpl_85))
begin
Tpl_89 <= 1'b0;
end
else
if (Tpl_103)
begin
if (Tpl_78[0])
Tpl_89 <= Tpl_80[2];
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_parity_en_84
if ((~Tpl_85))
begin
Tpl_90 <= 1'b0;
end
else
if (Tpl_103)
begin
if (Tpl_78[0])
Tpl_90 <= Tpl_80[3];
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_parity_type_87
if ((~Tpl_85))
begin
Tpl_91 <= 1'b0;
end
else
if (Tpl_103)
begin
if (Tpl_78[0])
Tpl_91 <= Tpl_80[4];
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_start_tx_90
if ((~Tpl_85))
begin
Tpl_92 <= 0;
end
else
if (Tpl_105)
begin
if (Tpl_78[0])
Tpl_92 <= Tpl_80[0];
end
else
if (Tpl_96)
Tpl_92 <= 0;
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_rx_data_93
if ((~Tpl_85))
begin
Tpl_110 <= 8'b00000000;
end
else
begin
Tpl_110 <= Tpl_87;
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_tx_done_96
if ((~Tpl_85))
begin
Tpl_107 <= 1'b1;
end
else
begin
Tpl_107 <= Tpl_93;
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_rx_done_99
if ((~Tpl_85))
begin
Tpl_108 <= 1'b0;
end
else
begin
Tpl_108 <= Tpl_94;
end
end


always @( posedge Tpl_84 or negedge Tpl_85 )
begin: proc_parity_error_102
if ((~Tpl_85))
begin
Tpl_109 <= 0;
end
else
begin
Tpl_109 <= Tpl_95;
end
end

assign Tpl_111[7:0] = Tpl_86;
assign Tpl_111[31:8] = Tpl_80[31:8];
assign Tpl_112[7:0] = Tpl_110;
assign Tpl_112[31:8] = Tpl_80[31:8];
assign Tpl_113[1:0] = Tpl_88;
assign Tpl_113[2] = Tpl_89;
assign Tpl_113[3] = Tpl_90;
assign Tpl_113[4] = Tpl_91;
assign Tpl_113[31:5] = Tpl_80[31:5];
assign Tpl_114[0] = Tpl_92;
assign Tpl_114[31:1] = Tpl_80[31:1];
assign Tpl_115[0] = Tpl_107;
assign Tpl_115[1] = Tpl_108;
assign Tpl_115[2] = Tpl_109;
assign Tpl_115[31:3] = Tpl_80[31:3];

always @(*)
begin
Tpl_83 = 0;
case (1)
Tpl_99: Tpl_83 = Tpl_111;
Tpl_101: Tpl_83 = Tpl_112;
Tpl_102: Tpl_83 = Tpl_113;
Tpl_104: Tpl_83 = Tpl_114;
Tpl_106: Tpl_83 = Tpl_115;
default: Tpl_83 = 0;
endcase
end


always @(*)
begin
if ((Tpl_81 && Tpl_77))
begin
if ((Tpl_79 == 0))
begin
Tpl_82 = 0;
end
else
if ((Tpl_79 == 4))
begin
Tpl_82 = 1;
end
else
if ((Tpl_79 == 8))
begin
Tpl_82 = 0;
end
else
if ((Tpl_79 == 12))
begin
Tpl_82 = 0;
end
else
if ((Tpl_79 == 16))
begin
Tpl_82 = 1;
end
else
Tpl_82 = 1;
end
else
if ((Tpl_81 && (~Tpl_77)))
begin
if ((((((Tpl_79 != 0) && (Tpl_79 != 4)) && (Tpl_79 != 8)) && (Tpl_79 != 12)) && (Tpl_79 != 16)))
begin
Tpl_82 = 1;
end
else
Tpl_82 = 0;
end
else
Tpl_82 = 0;
end

assign Tpl_121 = (Tpl_122 == 0);
assign Tpl_120 = (Tpl_123 == 0);

always @( posedge Tpl_118 or negedge Tpl_119 )
begin
if ((~Tpl_119))
begin
Tpl_122 <= 0;
end
else
begin
if ((Tpl_122 == 27))
begin
Tpl_122 <= 0;
end
else
Tpl_122 <= (Tpl_122 + 1);
end
end


always @( posedge Tpl_118 or negedge Tpl_119 )
begin
if ((~Tpl_119))
begin
Tpl_123 <= 0;
end
else
begin
if ((Tpl_123 == 434))
begin
Tpl_123 <= 0;
end
else
Tpl_123 <= (Tpl_123 + 1);
end
end


endmodule