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
wire   Tpl_29 ;
wire   Tpl_30 ;
wire   Tpl_31 ;
wire   Tpl_32 ;
wire  [7:0] Tpl_33 ;
wire  [1:0] Tpl_34 ;
wire   Tpl_35 ;
wire   Tpl_36 ;
wire   Tpl_37 ;
wire   Tpl_38 ;
logic   Tpl_39 ;
logic   Tpl_40 ;
logic  [1:0] Tpl_41 ;
logic  [1:0] Tpl_42 ;
logic  [2:0] Tpl_43 ;
logic  [2:0] Tpl_44 ;
logic  [1:0] Tpl_45 ;
logic  [1:0] Tpl_46 ;
logic  [7:0] Tpl_47 ;
wire   Tpl_48 ;
wire   Tpl_49 ;
wire   Tpl_50 ;
wire   Tpl_51 ;
wire  [1:0] Tpl_52 ;
wire   Tpl_53 ;
wire   Tpl_54 ;
wire   Tpl_55 ;
wire  [7:0] Tpl_56 ;
wire   Tpl_57 ;
logic   Tpl_58 ;
logic   Tpl_59 ;
logic  [1:0] Tpl_60 ;
logic  [1:0] Tpl_61 ;
logic  [3:0] Tpl_62 ;
logic  [3:0] Tpl_63 ;
logic  [1:0] Tpl_64 ;
logic  [3:0] Tpl_65 ;
logic  [1:0] Tpl_66 ;
logic  [7:0] Tpl_67 ;
logic   Tpl_68 ;
logic   Tpl_69 ;
wire   Tpl_70 ;
wire   Tpl_71 ;
wire   Tpl_72 ;
wire   Tpl_73 ;
wire   Tpl_74 ;
wire   Tpl_75 ;
wire  [3:0] Tpl_76 ;
wire  [11:0] Tpl_77 ;
wire  [31:0] Tpl_78 ;
wire   Tpl_79 ;
logic   Tpl_80 ;
logic  [31:0] Tpl_81 ;
wire   Tpl_82 ;
wire   Tpl_83 ;
logic  [7:0] Tpl_84 ;
wire  [7:0] Tpl_85 ;
logic  [1:0] Tpl_86 ;
logic   Tpl_87 ;
logic   Tpl_88 ;
logic   Tpl_89 ;
logic   Tpl_90 ;
wire   Tpl_91 ;
wire   Tpl_92 ;
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
logic   Tpl_104 ;
logic   Tpl_105 ;
logic   Tpl_106 ;
logic  [7:0] Tpl_107 ;
wire  [31:0] Tpl_108 ;
wire  [31:0] Tpl_109 ;
wire  [31:0] Tpl_110 ;
wire  [31:0] Tpl_111 ;
wire  [31:0] Tpl_112 ;
logic   Tpl_113 ;
logic   Tpl_114 ;
wire   Tpl_115 ;
wire   Tpl_116 ;
wire   Tpl_117 ;
wire   Tpl_118 ;
logic  [4:0] Tpl_119 ;
logic  [8:0] Tpl_120 ;


assign Tpl_29 = clk;
assign Tpl_30 = reset_n;
assign Tpl_31 = clk_tx;
assign Tpl_32 = cts_n;
assign Tpl_33 = tx_data;
assign Tpl_34 = data_bit_num;
assign Tpl_35 = stop_bit_num;
assign Tpl_36 = parity_en;
assign Tpl_37 = parity_type;
assign Tpl_38 = start_tx;
assign tx = Tpl_39;
assign tx_done = Tpl_40;

assign Tpl_48 = clk;
assign Tpl_49 = reset_n;
assign Tpl_50 = clk_rx;
assign Tpl_51 = rx;
assign Tpl_52 = data_bit_num;
assign Tpl_53 = stop_bit_num;
assign Tpl_54 = parity_en;
assign Tpl_55 = parity_type;
assign rx_data = Tpl_56;
assign rts_n = Tpl_57;
assign rx_done = Tpl_58;
assign parity_error = Tpl_59;

assign Tpl_71 = pclk;
assign Tpl_72 = preset_n;
assign Tpl_73 = psel;
assign Tpl_74 = penable;
assign Tpl_75 = pwrite;
assign Tpl_76 = pstrb;
assign Tpl_77 = paddr;
assign Tpl_78 = pwdata;
assign pready = Tpl_79;
assign pslverr = Tpl_80;
assign prdata = Tpl_81;
assign Tpl_82 = clk;
assign Tpl_83 = reset_n;
assign tx_data = Tpl_84;
assign Tpl_85 = rx_data;
assign data_bit_num = Tpl_86;
assign stop_bit_num = Tpl_87;
assign parity_en = Tpl_88;
assign parity_type = Tpl_89;
assign start_tx = Tpl_90;
assign Tpl_91 = tx_done;
assign Tpl_92 = rx_done;
assign Tpl_93 = parity_error;

assign Tpl_115 = clk;
assign Tpl_116 = reset_n;
assign clk_tx = Tpl_117;
assign clk_rx = Tpl_118;

always @(*)
begin
case (Tpl_34)
2'b00: begin
Tpl_43 = 3'd4;
Tpl_47 = Tpl_33[4:0];
end
2'b01: begin
Tpl_43 = 3'd5;
Tpl_47 = Tpl_33[5:0];
end
2'b10: begin
Tpl_43 = 3'd6;
Tpl_47 = Tpl_33[6:0];
end
2'b11: begin
Tpl_43 = 3'd7;
Tpl_47 = Tpl_33[7:0];
end
default: Tpl_43 = 3'd7;
endcase
end


always @(*)
begin
case ({{Tpl_36,Tpl_35}})
2'b00: Tpl_45 = 2'd0;
2'b01: Tpl_45 = 2'd1;
2'b10: Tpl_45 = 2'd1;
2'b11: Tpl_45 = 2'd2;
default: Tpl_45 = 2'd0;
endcase
end


always @( posedge Tpl_29 or negedge Tpl_30 )
begin
if ((~Tpl_30))
begin
Tpl_41 <= 2'b00;
end
else
begin
Tpl_41 <= Tpl_42;
case (Tpl_41)
2'b00: begin
Tpl_44 <= 0;
Tpl_46 <= 0;
end
2'b10: begin
if (Tpl_31)
begin
Tpl_44 <= (Tpl_44 + 1);
end
else
Tpl_44 <= Tpl_44;
end
2'b11: begin
if (Tpl_31)
begin
Tpl_46 <= (Tpl_46 + 1);
end
else
Tpl_46 <= Tpl_46;
end
default: begin
Tpl_44 <= 0;
Tpl_46 <= 0;
end
endcase
end
end


always @(*)
begin
case (Tpl_41)
2'b00: begin
if (((Tpl_38 && (!Tpl_32)) && Tpl_31))
begin
Tpl_42 = 2'b01;
end
else
Tpl_42 = 2'b00;
end
2'b01: begin
if (Tpl_31)
begin
Tpl_42 = 2'b10;
end
else
Tpl_42 = 2'b01;
end
2'b10: begin
if (Tpl_31)
begin
if ((Tpl_44 == Tpl_43))
begin
Tpl_42 = 2'b11;
end
else
Tpl_42 = 2'b10;
end
else
Tpl_42 = 2'b10;
end
2'b11: begin
if (Tpl_31)
begin
if ((Tpl_46 == Tpl_45))
begin
Tpl_42 = 2'b00;
end
else
Tpl_42 = 2'b11;
end
else
Tpl_42 = 2'b11;
end
default: Tpl_42 = 2'b00;
endcase
end


always @(*)
begin
case (Tpl_41)
2'b00: begin
Tpl_39 = 1'b1;
end
2'b01: begin
Tpl_39 = 1'b0;
end
2'b10: begin
Tpl_39 = Tpl_33[Tpl_44];
end
2'b11: begin
if ((Tpl_36 && (Tpl_46 == 0)))
begin
Tpl_39 = (Tpl_37 ? (^Tpl_47) : (~^Tpl_47));
end
else
Tpl_39 = 1'b1;
end
default: Tpl_39 = 1'b1;
endcase
end


always @( posedge Tpl_29 or negedge Tpl_30 )
begin
if ((~Tpl_30))
begin
Tpl_40 <= 1;
end
else
begin
if (Tpl_31)
begin
if ((((Tpl_41 == 2'b11) && (Tpl_46 == Tpl_45)) || (Tpl_41 == 2'b00)))
begin
Tpl_40 <= 1;
end
else
Tpl_40 <= 0;
end
else
Tpl_40 <= Tpl_40;
end
end


always @(*)
begin
case (Tpl_52)
2'b00: Tpl_63 = 4'd5;
2'b01: Tpl_63 = 4'd6;
2'b10: Tpl_63 = 4'd7;
2'b11: Tpl_63 = 4'd8;
default: Tpl_63 = 4'd8;
endcase
end


always @(*)
begin
case ({{Tpl_54,Tpl_53}})
2'b00: Tpl_64 = 2'd1;
2'b01: Tpl_64 = 2'd2;
2'b10: Tpl_64 = 2'd2;
2'b11: Tpl_64 = 2'd3;
default: Tpl_64 = 2'd1;
endcase
end


always @(*)
begin
case (Tpl_60)
2'b11: begin
if ((!Tpl_51))
Tpl_61 = 2'b00;
else
Tpl_61 = 2'b11;
end
2'b00: begin
if ((Tpl_62 == 15))
begin
Tpl_61 = 2'b01;
end
else
Tpl_61 = 2'b00;
end
2'b01: begin
if (((Tpl_62 == 15) && (Tpl_65 == Tpl_63)))
begin
Tpl_61 = 2'b10;
end
else
Tpl_61 = 2'b01;
end
2'b10: begin
if (((Tpl_62 == 15) && (Tpl_66 == Tpl_64)))
begin
Tpl_61 = 2'b11;
end
else
Tpl_61 = 2'b10;
end
default: Tpl_61 = 2'b11;
endcase
end


always @( posedge Tpl_48 or negedge Tpl_49 )
begin
if ((~Tpl_49))
begin
Tpl_60 <= 2'b00;
Tpl_65 <= 0;
Tpl_66 <= 0;
Tpl_62 <= 0;
Tpl_69 <= 0;
end
else
begin
Tpl_60 <= Tpl_61;
case (Tpl_60)
2'b11: begin
Tpl_62 <= 0;
Tpl_69 <= 0;
end
2'b00: begin
Tpl_65 <= 0;
Tpl_66 <= 0;
if (Tpl_50)
begin
Tpl_62 <= (Tpl_62 + 1'b1);
if ((Tpl_62 == 15))
begin
Tpl_62 <= 0;
end
end
else
Tpl_62 <= Tpl_62;
end
2'b01: begin
if (Tpl_50)
begin
Tpl_62 <= (Tpl_62 + 1'b1);
if ((Tpl_62 == 8))
begin
Tpl_65 <= (Tpl_65 + 1);
Tpl_67[Tpl_65] <= Tpl_51;
Tpl_69 <= (Tpl_69 ^ Tpl_51);
end
else
if ((Tpl_62 == 15))
begin
Tpl_62 <= 0;
end
end
else
Tpl_62 <= Tpl_62;
end
2'b10: begin
if (Tpl_50)
begin
Tpl_62 <= (Tpl_62 + 1);
if ((Tpl_62 == 8))
begin
Tpl_66 <= (Tpl_66 + 1);
end
else
if ((Tpl_62 == 15))
begin
Tpl_62 <= 0;
end
end
else
Tpl_62 <= Tpl_62;
end
endcase
end
end


always @(*)
begin
case (Tpl_60)
2'b11: begin
Tpl_58 = 1;
end
2'b00: begin
Tpl_58 = 1;
end
2'b01: begin
Tpl_58 = 0;
end
2'b10: begin
Tpl_58 = ((Tpl_62 == 15) && (Tpl_66 == Tpl_64));
if (((Tpl_66 == 0) && Tpl_54))
begin
Tpl_68 = Tpl_51;
end
Tpl_59 = (Tpl_54 ? (Tpl_55 ? (Tpl_69 != Tpl_68) : ((~Tpl_69) != Tpl_68)) : 1'b0);
end
default: begin
Tpl_58 = 0;
end
endcase
end

assign Tpl_57 = (~Tpl_58);
assign Tpl_56 = Tpl_67;
assign Tpl_94 = ((Tpl_73 && (~Tpl_75)) && Tpl_74);
assign Tpl_95 = ((Tpl_73 && Tpl_75) && Tpl_74);
assign Tpl_79 = ((Tpl_73 == 1'b1) ? ((Tpl_75 & Tpl_113) | ((~Tpl_75) & Tpl_114)) : 0);
assign Tpl_96 = (Tpl_94 && (Tpl_77 == 0));
assign Tpl_97 = (Tpl_95 && (Tpl_77 == 0));
assign Tpl_98 = (Tpl_94 && (Tpl_77 == 4));
assign Tpl_99 = (Tpl_94 && (Tpl_77 == 8));
assign Tpl_100 = (Tpl_95 && (Tpl_77 == 8));
assign Tpl_101 = (Tpl_94 && (Tpl_77 == 12));
assign Tpl_102 = (Tpl_95 && (Tpl_77 == 12));
assign Tpl_103 = (Tpl_94 && (Tpl_77 == 16));

always @(*)
begin
if ((!Tpl_95))
begin
Tpl_113 = 1'b0;
end
else
begin
Tpl_113 = 1'b1;
end
end


always @(*)
begin
if ((!Tpl_94))
begin
Tpl_114 = 1'b0;
end
else
begin
Tpl_114 = 1'b1;
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_tx_write_data_75
if ((~Tpl_83))
begin
Tpl_84 <= 0;
end
else
if (Tpl_97)
begin
if (Tpl_76[0])
Tpl_84 <= Tpl_78[7:0];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_data_bit_num_78
if ((~Tpl_83))
begin
Tpl_86 <= 2'b00;
end
else
if (Tpl_100)
begin
if (Tpl_76[0])
Tpl_86 <= Tpl_78[1:0];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_stop_bit_num_81
if ((~Tpl_83))
begin
Tpl_87 <= 1'b0;
end
else
if (Tpl_100)
begin
if (Tpl_76[0])
Tpl_87 <= Tpl_78[2];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_parity_en_84
if ((~Tpl_83))
begin
Tpl_88 <= 1'b0;
end
else
if (Tpl_100)
begin
if (Tpl_76[0])
Tpl_88 <= Tpl_78[3];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_parity_type_87
if ((~Tpl_83))
begin
Tpl_89 <= 1'b0;
end
else
if (Tpl_100)
begin
if (Tpl_76[0])
Tpl_89 <= Tpl_78[4];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_start_tx_90
if ((~Tpl_83))
begin
Tpl_90 <= 0;
end
else
if (Tpl_102)
begin
if (Tpl_76[0])
Tpl_90 <= Tpl_78[0];
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_rx_data_93
if ((~Tpl_83))
begin
Tpl_107 <= 8'b00000000;
end
else
begin
Tpl_107 <= Tpl_85;
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_tx_done_96
if ((~Tpl_83))
begin
Tpl_104 <= 1'b1;
end
else
begin
Tpl_104 <= Tpl_91;
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_rx_done_99
if ((~Tpl_83))
begin
Tpl_105 <= 1'b0;
end
else
begin
Tpl_105 <= Tpl_92;
end
end


always @( posedge Tpl_82 or negedge Tpl_83 )
begin: proc_parity_error_102
if ((~Tpl_83))
begin
Tpl_106 <= 0;
end
else
begin
Tpl_106 <= Tpl_93;
end
end

assign Tpl_108[7:0] = Tpl_84;
assign Tpl_108[31:8] = Tpl_78[31:8];
assign Tpl_109[7:0] = Tpl_107;
assign Tpl_109[31:8] = Tpl_78[31:8];
assign Tpl_110[1:0] = Tpl_86;
assign Tpl_110[2] = Tpl_87;
assign Tpl_110[3] = Tpl_88;
assign Tpl_110[4] = Tpl_89;
assign Tpl_110[31:5] = Tpl_78[31:5];
assign Tpl_111[0] = Tpl_90;
assign Tpl_111[31:1] = Tpl_78[31:1];
assign Tpl_112[0] = Tpl_104;
assign Tpl_112[1] = Tpl_105;
assign Tpl_112[2] = Tpl_106;
assign Tpl_112[31:3] = Tpl_78[31:3];

always @(*)
begin
Tpl_81 = 0;
case (1)
Tpl_96: Tpl_81 = Tpl_108;
Tpl_98: Tpl_81 = Tpl_109;
Tpl_99: Tpl_81 = Tpl_110;
Tpl_101: Tpl_81 = Tpl_111;
Tpl_103: Tpl_81 = Tpl_112;
default: Tpl_81 = 0;
endcase
end


always @(*)
begin
if ((Tpl_79 && Tpl_75))
begin
if ((Tpl_77 == 0))
begin
Tpl_80 = 0;
end
else
if ((Tpl_77 == 4))
begin
Tpl_80 = 1;
end
else
if ((Tpl_77 == 8))
begin
Tpl_80 = 0;
end
else
if ((Tpl_77 == 12))
begin
Tpl_80 = 0;
end
else
if ((Tpl_77 == 16))
begin
Tpl_80 = 1;
end
else
Tpl_80 = 1;
end
else
Tpl_80 = 0;
end

assign Tpl_118 = (Tpl_119 == 0);
assign Tpl_117 = (Tpl_120 == 0);

always @( posedge Tpl_115 or negedge Tpl_116 )
begin
if ((~Tpl_116))
begin
Tpl_119 <= 0;
end
else
begin
if ((Tpl_119 == 27))
begin
Tpl_119 <= 0;
end
else
Tpl_119 <= (Tpl_119 + 1);
end
end


always @( posedge Tpl_115 or negedge Tpl_116 )
begin
if ((~Tpl_116))
begin
Tpl_120 <= 0;
end
else
begin
if ((Tpl_120 == 434))
begin
Tpl_120 <= 0;
end
else
Tpl_120 <= (Tpl_120 + 1);
end
end


endmodule