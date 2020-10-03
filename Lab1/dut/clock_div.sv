`timescale 1ns / 1ps

module clock_div #(parameter C_OUT_FREQ = 60, parameter C_IN_FREQ = 100000)
(
	input logic refclk,
	input logic rst,
	output logic outclk
);
	logic clk_next;
	logic [31:0] count;
	logic [31:0] count_next;

	always_ff @(posedge refclk) begin
		outclk <= clk_next;
		count <= count_next;
	end

	always_comb begin
		if(rst) begin
			clk_next = 0;
			count_next = 32'd0;
		end else begin
			if(count == C_IN_FREQ/(2*C_OUT_FREQ) - 1) begin
				clk_next = !outclk;
				count_next = 32'd0;
			end else begin
				clk_next = outclk;
				count_next = count + 1;
			end
		end
	end
endmodule
