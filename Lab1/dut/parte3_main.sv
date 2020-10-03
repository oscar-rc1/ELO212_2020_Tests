`timescale 1ns / 1ps

module top_module
(
	input logic clk,
	input logic rst,
	output logic [6:0] sseg,
	output logic [7:0] an,

	input logic a,
	input logic b,
	output logic c
);
	logic [3:0] curr_bcd;
	logic [15:0] curr_num;
	logic clk_4hz, clk_240hz;

	assign c = a & b;

	clock_div #(4, 10000) CLK1
	(
		.refclk(clk),
		.rst(rst),
		.outclk(clk_4hz)
	);

	clock_div #(240, 10000) CLK2
	(
		.refclk(clk),
		.rst(rst),
		.outclk(clk_240hz)
	);

	counter_16bit U0
	(
		.clk(clk_4hz),
		.rst(rst),
		.number(curr_num)
	);

	mux_display_bcd U1
	(
		.number(curr_num),
		.clk(clk_240hz),
		.rst(rst),
		.bcd(curr_bcd),
		.leds(an)
	);

	bcd_to_sseg U2
	(
		.bcd(curr_bcd),
		.seven_seg(sseg)
	);
endmodule

