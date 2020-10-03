`timescale 1ns / 1ps

module bcd_to_sseg
(
	input logic [3:0] bcd,
	output logic [6:0] seven_seg
);
	always_comb begin
		case(bcd)
			4'h0: seven_seg = 7'b1000000;
			4'h1: seven_seg = 7'b1111001;
			4'h2: seven_seg = 7'b0100100;
			4'h3: seven_seg = 7'b0110000;
			4'h4: seven_seg = 7'b0011001;
			4'h5: seven_seg = 7'b0010010;
			4'h6: seven_seg = 7'b0000010;
			4'h7: seven_seg = 7'b1111000;
			4'h8: seven_seg = 7'b0000000;
			4'h9: seven_seg = 7'b0010000;
			4'hA: seven_seg = 7'b0001000;
			4'hB: seven_seg = 7'b0000011;
			4'hC: seven_seg = 7'b1000110;
			4'hD: seven_seg = 7'b0100001;
			4'hE: seven_seg = 7'b0000110;
			4'hF: seven_seg = 7'b0001110;
			default: seven_seg = 7'b1111111;
		endcase
	end
endmodule
