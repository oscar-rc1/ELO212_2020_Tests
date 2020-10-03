`timescale 1ns / 1ps

module mux_display_bcd
(
	input logic clk,
	input logic rst,
	input logic [15:0] number,

	output logic [3:0] bcd,
	output logic [7:0] leds
);
	logic [1:0] pos;

	always_ff @(posedge clk) begin
		if(rst) begin
			pos <= 2'd0;
		end else begin
			pos <= pos + 1;
		end
	end

	always_comb begin
		if(rst) begin
			bcd = 4'd0;
			leds = 8'b11111111;
		end else begin
			case(pos)
				2'd0: bcd = number[3:0];
				2'd1: bcd = number[7:4];
				2'd2: bcd = number[11:8];
				2'd3: bcd = number[15:12];
				default: bcd = 4'd0;
			endcase
			case(pos)
				2'd0: leds = 8'b11111110;
				2'd1: leds = 8'b11111101;
				2'd2: leds = 8'b11111011;
				2'd3: leds = 8'b11110111;
				default: leds = 8'b11111111;
			endcase
		end
	end
endmodule
