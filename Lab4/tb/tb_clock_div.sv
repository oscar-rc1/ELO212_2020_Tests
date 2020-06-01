`timescale 1ns / 1ps

module tb_clock_div();
	bit clk = 1'b0;
	bit rst = 1'b1;

	always #5 clk = ~clk;
	always #10 @(posedge clk) rst <= 1'b0;

	//

	bit pass = 1'b1;
	logic clk_50M, clk_30M, clk_10M, clk_1M;

	assert property (@(posedge clk) disable iff (rst) $fell(rst) |-> ##1 ~$stable(clk_50M)) else begin
		pass = 1'b0;
		$error("clk_50M is not running");
	end

	assert property ( @(posedge clk) disable iff (rst) $rose(clk_50M) |=> $fell(clk_50M) ##1 $rose(clk_50M) ) else begin
		pass = 1'b0;
		$error("clk_50M doesn't match the expected frequency");
	end

	assert property (@(posedge clk) disable iff (rst) $fell(rst) |-> ##2 ~$stable(clk_30M)) else begin
		pass = 1'b0;
		$error("clk_30M is not running");
	end

	assert property ( @(posedge clk) disable iff (rst) $rose(clk_30M) |=> $stable(clk_30M) ##1 $fell(clk_30M) ##1 $stable(clk_30M) ##1 $rose(clk_30M) ) else begin
		pass = 1'b0;
		$error("clk_30M doesn't match the expected frequency");
	end

	assert property (@(posedge clk) disable iff (rst) $fell(rst) |-> ##5 ~$stable(clk_10M)) else begin
		pass = 1'b0;
		$error("clk_10M is not running");
	end

	assert property ( @(posedge clk) disable iff (rst) $rose(clk_10M) |=> $stable(clk_10M) [*4] ##1 $fell(clk_10M) ##1 $stable(clk_10M) [*4] ##1 $rose(clk_10M) ) else begin
		pass = 1'b0;
		$error("clk_10M doesn't match the expected frequency");
	end

	assert property (@(posedge clk) disable iff (rst) $fell(rst) |-> ##50 ~$stable(clk_1M)) else begin
		pass = 1'b0;
		$error("clk_1M is not running");
	end

	assert property ( @(posedge clk) disable iff (rst) $rose(clk_1M) |=> $stable(clk_1M) [*49] ##1 $fell(clk_1M) ##1 $stable(clk_1M) [*49] ##1 $rose(clk_1M) ) else begin
		pass = 1'b0;
		$error("clk_1M doesn't match the expected frequency");
	end

	initial begin
		#3505

		$display("------------------");

		if(pass) begin
			$display("       PASS       ");
		end else begin
			$display("       FAIL       ");
		end

		$display("------------------");
		$finish;
	end

	//

	S4_Actividad2 DUT
	(
		.clock_100M(clk),
		.reset(rst),

		.clock_out_50M(clk_50M),
		.clock_out_30M(clk_30M),
		.clock_out_10M(clk_10M),
		.clock_out_1M(clk_1M)
	);
endmodule
