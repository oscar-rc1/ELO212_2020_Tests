`timescale 1ns / 1ps

module tb_display_mux();
	bit clk = 1'b0;
	bit rst = 1'b1;

	always #1 clk = ~clk;
	always_ff @(posedge clk) rst <= 1'b0;

	//

	logic [31:0] in_num, out_num;
	logic [3:0] out_digits[0:7];
	logic [6:0] out_segs;
	logic [7:0] out_an;
	bit error = 1'b0;
	bit pass = 1'b1;

	initial begin
		in_num = 32'd0;
		out_num = 32'd0;

		repeat(1) @(posedge clk);

		repeat(100000) begin
			out_digits = {4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX};
			error = 1'b0;

			repeat(8) begin
				@(posedge clk);

				if(~$onehot0(~out_an)) begin
					$error($sformatf("More than 1 display enabled: %08b", out_an));
					error = 1'b1;
				end

				for(int i = 0; i < 8; ++i) begin
					if(out_an[i]) continue;

					case(out_segs)
						7'b0000001: out_digits[i] = 4'h0;
						7'b1001111: out_digits[i] = 4'h1;
						7'b0010010: out_digits[i] = 4'h2;
						7'b0000110: out_digits[i] = 4'h3;
						7'b1001100: out_digits[i] = 4'h4;
						7'b0100100: out_digits[i] = 4'h5;
						7'b0100000: out_digits[i] = 4'h6;
						7'b0001110: out_digits[i] = 4'h7;
						7'b0000000: out_digits[i] = 4'h8;
						7'b0000100: out_digits[i] = 4'h9;
						7'b0001000: out_digits[i] = 4'hA;
						7'b1100000: out_digits[i] = 4'hB;
						7'b0110001: out_digits[i] = 4'hC;
						7'b1000010: out_digits[i] = 4'hD;
						7'b0110000: out_digits[i] = 4'hE;
						7'b0111000: out_digits[i] = 4'hF;
					endcase
				end
			end

			out_num = {out_digits[7], out_digits[6], out_digits[5], out_digits[4],
			           out_digits[3], out_digits[2], out_digits[1], out_digits[0]};

			if(out_num !== in_num) begin
				$error($sformatf("Displaying %08X, but expected %08X", out_num, in_num));
				error = 1'b1;
			end

			if(error) pass = 1'b0;

			in_num = $urandom;
		end

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

	S4_Actividad1 DUT
	(
		.clock(clk),
		.reset(rst),

		.BCD_in(in_num),

		.segments(out_segs),
		.anodos(out_an)
	);
endmodule
