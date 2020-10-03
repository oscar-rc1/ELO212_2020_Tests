`timescale 1ns / 1ps

module counter_16bit
(
	input logic clk,
	input logic rst,
	output logic [15:0] number
);
	always_ff @(posedge clk) begin
		if(rst) begin
			number <= 'd0;
		end else begin
			number <= number + 'd1;
		end
	end
endmodule
