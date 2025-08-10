`timescale 1ns / 1ps

module top(
    input clk,
    input rstn,
    input logic i_valid,
    input logic signed [8:0] din_i[15:0],
    input logic signed [8:0] din_q[15:0],
    output logic signed [12:0] dout_i[15:0],
    output logic signed [12:0] dout_q[15:0],
    output logic o_valid
);
    // 중간 신호 선언
    logic signed [9:0]  buf0_out_i[15:0], buf0_out_q[15:0];
    logic               buf0_valid;
    logic signed [9:0]  tw1_out_i[15:0], tw1_out_q[15:0];
    logic               tw1_valid;
    logic signed [10:0] buf1_out_i[15:0], buf1_out_q[15:0];
    logic               buf1_valid;
    logic signed [19:0] tw2_out_i[15:0], tw2_out_q[15:0];
    logic               tw2_valid;
    logic signed [11:0] shift_out_i[15:0], shift_out_q[15:0];
    logic               shift_valid;
    logic signed [12:0] buf2_out_i[15:0], buf2_out_q[15:0];
    logic               buf2_valid;
    // 3단계 버퍼 출력 신호 선언
    logic tw3_in_valid;
    logic signed [22:0] tw3_out_i[15:0];
    logic signed [22:0] tw3_out_q[15:0];
    logic tw3_valid;

    // CBFP 모듈 출력 신호 선언
    wire signed [10:0] cbfp0_out_i [15:0];
    wire signed [10:0] cbfp0_out_q [15:0];
    wire cbfp_valid;


    logic signed [11:0] buf2_0_out_i[15:0], buf2_0_out_q[15:0];
    logic               buf2_0_valid;

    logic signed [11:0] tw1_0_out_i[15:0], tw1_0_out_q[15:0];
    logic               tw1_0_valid;

    logic signed [12:0] buf2_1_out_i[15:0], buf2_1_out_q[15:0];
    logic               buf2_1_valid;

    logic signed [22:0] tw1_1_out_i[15:0], tw1_1_out_q[15:0];
    logic               tw1_1_valid;

    logic signed [13:0] shift1_out_i[15:0], shift1_out_q[15:0];
    logic               shift1_valid;

    logic signed [14:0] buf2_2_out_i[15:0], buf2_2_out_q[15:0];
    logic               buf2_2_valid;

    logic signed [24:0] tw1_2_out_i[15:0], tw1_2_out_q[15:0];
    logic               tw1_2_valid;

    logic signed [11:0] cbfp1_out_i[15:0], cbfp1_out_q[15:0];
    logic               cbfp1_valid;

    logic signed [12:0] buf2_0_1_out_i[15:0], buf2_0_1_out_q[15:0];
    logic               buf2_0_1_valid;

    logic signed [12:0] tw2_0_1_out_i[15:0], tw2_0_1_out_q[15:0];
    logic               tw2_0_1_valid;

    logic signed [13:0] buf2_1_1_out_i[15:0], buf2_1_1_out_q[15:0];
    logic               buf2_1_1_valid;

    logic signed [22:0] tw2_1_1_out_i[15:0], tw2_1_1_out_q[15:0];
    logic               tw2_1_1_valid;

    logic signed [14:0] shift2_out_i[15:0], shift2_out_q[15:0];
    logic               shift2_valid;

    logic signed [15:0] buf2_2_1_out_i[15:0], buf2_2_1_out_q[15:0];
    logic               buf2_2_1_valid;

    logic signed [12:0] cbfp2_out_i[15:0], cbfp2_out_q[15:0];
    logic               cbfp2_valid;

    logic [4:0] w_applied_shift_out_1 [511:0];
    logic [4:0] w_applied_shift_out_2 [511:0];
    
    // final_cbfp_scaler용 16개 배열
    logic [4:0] final_shift_out_0 [15:0];
    logic [4:0] final_shift_out_1 [15:0];

    logic signed [12:0] reverse_out_i[15:0], reverse_out_q[15:0];
    logic               reverse_valid;


     logic [8:0] final_cycle_idx;
     
    always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) final_cycle_idx <= 0;
    else final_cycle_idx <= final_cycle_idx + 1;  // 매 클럭마다 증가 (테스트용)
    end

    // final_cbfp_scaler용 16개 배열 할당
    always_comb begin
        for (int i = 0; i < 16; i++) begin
            final_shift_out_0[i] = w_applied_shift_out_1[i];
            final_shift_out_1[i] = w_applied_shift_out_2[i];
        end
    end

       // 1단계 버퍼
    stage_buffer #(
        .IN_WIDTH(9), .OUT_WIDTH(10), .NUM_ELEMS(256), .BLK_SIZE(16), .PIPELINE_DEPTH(0), .VALID_DELAY(0)
    ) u_stage_0_0_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(din_i),
        .din_q(din_q),
        .i_valid(i_valid),
        .dout_i(buf0_out_i),
        .dout_q(buf0_out_q),
        .o_valid(buf0_valid)
    );

    // 1단계 트위들 팩터
    stage_0_0_2 u_twidle0_1(
        .clk(clk),
        .rstn(rstn),
        .i_valid(buf0_valid),
        .din_i(buf0_out_i),
        .din_q(buf0_out_q),
        .dout_i(tw1_out_i),
        .dout_q(tw1_out_q),
        .o_valid(tw1_valid)
    );

    // 2단계 버퍼
    stage_buffer #(
        .IN_WIDTH(10), .OUT_WIDTH(11), .NUM_ELEMS(128), .BLK_SIZE(16), .PIPELINE_DEPTH(2), .VALID_DELAY(0)
    ) u_stage_0_1_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(tw1_out_i),
        .din_q(tw1_out_q),
        .i_valid(tw1_valid),
        .dout_i(buf1_out_i),
        .dout_q(buf1_out_q),
        .o_valid(buf1_valid)
    );

    // 2단계 트위들 팩터
    stage_0_1_2 u_twidle0_2(
        .clk(clk),
        .rstn(rstn),
        .i_valid(buf1_valid),
        .din_i(buf1_out_i),
        .din_q(buf1_out_q),
        .dout_i(tw2_out_i),
        .dout_q(tw2_out_q),
        .o_valid(tw2_valid)
    );

    shift_processor #(
        .IN_WIDTH(20),
        .OUT_WIDTH(12)
    )u_shift1(
       .clk(clk),
       .rstn(rstn),
       .i_valid(tw2_valid),
       .din_i(tw2_out_i),  
       .din_q(tw2_out_q),  
       .dout_i(shift_out_i), 
       .dout_q(shift_out_q), 
       .o_valid(shift_valid)
    );

    // 3단계 버퍼
    stage_buffer #(
        .IN_WIDTH(12), .OUT_WIDTH(13), .NUM_ELEMS(64), .BLK_SIZE(16), .PIPELINE_DEPTH(0), .VALID_DELAY(1)
    ) u_stage_0_2_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(shift_out_i),
        .din_q(shift_out_q),
        .i_valid(shift_valid),
        .dout_i(buf2_out_i),
        .dout_q(buf2_out_q),
        .o_valid(buf2_valid)
    );
    

    twidle0_3 #(
        .IN_WIDTH(13),
        .OUT_WIDTH(23)
    )u_twidle0_3 (
        .clk(clk),
        .rstn(rstn),
        .i_valid(buf2_valid),
        .din_i(buf2_out_i),
        .din_q(buf2_out_q),
        .dout_i(tw3_out_i),
        .dout_q(tw3_out_q),
        .o_valid(tw3_valid)
    );


    ///cbfp
    fft_cbfp_module0 u_cbfp(
        .clk(clk),
        .rstn(rstn),
        .valid_in(tw3_valid),
        .pre_bfly02_real_in(tw3_out_i),
        .pre_bfly02_imag_in(tw3_out_q),
        .applied_shift_out(w_applied_shift_out_1),
        .valid_out(cbfp_valid),
        .bfly02_real_out(cbfp0_out_i),
        .bfly02_imag_out(cbfp0_out_q)
    );

    
    // 모듈 1
    stage_buffer #(
        .IN_WIDTH(11), .OUT_WIDTH(12), .NUM_ELEMS(32), .BLK_SIZE(16), .PIPELINE_DEPTH(0), .VALID_DELAY(1)
    ) u_stage_1_0_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(cbfp0_out_i),
        .din_q(cbfp0_out_q),
        .i_valid(cbfp_valid),
        .dout_i(buf2_0_out_i),
        .dout_q(buf2_0_out_q),
        .o_valid(buf2_0_valid)
    );

    stage_1_0_2 u_twiddle1_1 (
        .clk(clk),
        .rstn(rstn),
        .i_valid(buf2_0_valid),
        .din_i(buf2_0_out_i),
        .din_q(buf2_0_out_q),
        .dout_i(tw1_0_out_i),
        .dout_q(tw1_0_out_q),
        .o_valid(tw1_0_valid)
    );

    
    stage_buffer #(
        .IN_WIDTH(12), .OUT_WIDTH(13), .NUM_ELEMS(16), .BLK_SIZE(16),  .PIPELINE_DEPTH(0), .VALID_DELAY(1)
    ) u_stage_1_0_2(
        .clk(clk),
        .rstn(rstn),
        .din_i(tw1_0_out_i),
        .din_q(tw1_0_out_q),
        .i_valid(tw1_0_valid),
        .dout_i(buf2_1_out_i),
        .dout_q(buf2_1_out_q),
        .o_valid(buf2_1_valid)
    );

    stage_1_1_2 u_twiddle1_2(
     .clk(clk),
     .rstn(rstn),
     .i_valid(buf2_1_valid),
     .din_i(buf2_1_out_i),
     .din_q(buf2_1_out_q),
     .dout_i(tw1_1_out_i),
     .dout_q(tw1_1_out_q),
     .o_valid(tw1_1_valid)
    );

    shift_processor #(
        .IN_WIDTH(23),
        .OUT_WIDTH(14)
    )u_shift2(
       .clk(clk),
       .rstn(rstn),
       .i_valid(tw1_1_valid),
       .din_i(tw1_1_out_i),  
       .din_q(tw1_1_out_q),  
       .dout_i(shift1_out_i), 
       .dout_q(shift1_out_q), 
       .o_valid(shift1_valid)
    );


    stage_buffer_und16 #(
         .IN_WIDTH (14),
         .OUT_WIDTH (15),
         .BLK_SIZE(16)   
         ) u_stage1_1_0(
        .clk(clk),
        .rstn(rstn),
        .din_i(shift1_out_i),
        .din_q(shift1_out_q),
        .i_valid(shift1_valid),
        .dout_i(buf2_2_out_i),
        .dout_q(buf2_2_out_q),
        .o_valid(buf2_2_valid)
    );

     twidle1_3 #(
        .IN_WIDTH(15),
        .OUT_WIDTH(25)
    )u_twidle1_3 (
        .clk(clk),
        .rstn(rstn),
        .i_valid(buf2_2_valid),
        .din_i(buf2_2_out_i),
        .din_q(buf2_2_out_q),
        .dout_i(tw1_2_out_i),
        .dout_q(tw1_2_out_q),
        .o_valid(tw1_2_valid)
    );

    fft_cbfp_module1 u_cbfp2(
        .clk(clk),
        .rst_n(rstn),
        .valid_in(tw1_2_valid),
        .pre_bfly12_real_in(tw1_2_out_i),
        .pre_bfly12_imag_in(tw1_2_out_q),
        .applied_shift_out_2(w_applied_shift_out_2),
        .valid_out(cbfp1_valid),
        .bfly12_real_out(cbfp1_out_i),
        .bfly12_imag_out(cbfp1_out_q)
    );

    //모듈 2
    stage_buffer_und8 #(
        .IN_WIDTH(12),
        .OUT_WIDTH(13),
        .BLK_SIZE(16)  
    ) u_stage2_0_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(cbfp1_out_i),
        .din_q(cbfp1_out_q),
        .i_valid(cbfp1_valid),
        .dout_i(buf2_0_1_out_i),
        .dout_q(buf2_0_1_out_q),
        .o_valid(buf2_0_1_valid)
    );


    stage_2_0_2 u_stage2_0_2(
        .clk(clk),
        .rstn(rstn),
        .din_i(buf2_0_1_out_i),
        .din_q(buf2_0_1_out_q),
        .i_valid(buf2_0_1_valid),
        .dout_i(tw2_0_1_out_i),
        .dout_q(tw2_0_1_out_q),
        .o_valid(tw2_0_1_valid)
    );


    stage_buffer_und4 #(
        .IN_WIDTH(13),
        .OUT_WIDTH(14),
        .BLK_SIZE(16)  
    )u_stage2_1_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(tw2_0_1_out_i),
        .din_q(tw2_0_1_out_q),
        .i_valid(tw2_0_1_valid),
        .dout_i(buf2_1_1_out_i),
        .dout_q(buf2_1_1_out_q),
        .o_valid(buf2_1_1_valid)
    );


    stage_2_1_2 u_stage2_1_2(
        .clk(clk),
        .rstn(rstn),
        .din_i(buf2_1_1_out_i),
        .din_q(buf2_1_1_out_q),
        .i_valid(buf2_1_1_valid),
        .dout_i(tw2_1_1_out_i),
        .dout_q(tw2_1_1_out_q),
        .o_valid(tw2_1_1_valid)
    );

    shift_processor #(
        .IN_WIDTH(23),
        .OUT_WIDTH(15)
    )u_shift3(
       .clk(clk),
       .rstn(rstn),
       .i_valid(tw2_1_1_valid),
       .din_i(tw2_1_1_out_i),  
       .din_q(tw2_1_1_out_q),  
       .dout_i(shift2_out_i), 
       .dout_q(shift2_out_q), 
       .o_valid(shift2_valid)
    );

    stage_buffer_und2 #(
        .IN_WIDTH(15),
        .OUT_WIDTH(16),
        .BLK_SIZE(16)  
    )u_stage2_2_1(
        .clk(clk),
        .rstn(rstn),
        .din_i(shift2_out_i),
        .din_q(shift2_out_q),
        .i_valid(shift2_valid),
        .dout_i(buf2_2_1_out_i),
        .dout_q(buf2_2_1_out_q),
        .o_valid(buf2_2_1_valid)
    );

     final_cbfp_scaler #(
    .IN_WIDTH(16),
    .OUT_WIDTH(13),
    .SHIFT_WIDTH(5),
    .DATA_PER_CLK(16)
) u_final_cbfp_scaler (
    .clk(clk),
    .rstn(rstn),
    .valid_in(buf2_2_1_valid),
    .din_i(buf2_2_1_out_i),
    .din_q(buf2_2_1_out_q),
    .applied_shift_out_0(w_applied_shift_out_1),
    .applied_shift_out_1(w_applied_shift_out_2),
    .dout_i(cbfp2_out_i),
    .dout_q(cbfp2_out_q),
    .valid_out(cbfp2_valid)
);

    streaming_bit_reversal #(
    .DATA_WIDTH(13),
    .TOTAL_SIZE(512),
    .DATA_PER_CLK(16)
    )u_final_output(
       .clk(clk),
       .rstn(rstn),
       .valid_in(cbfp2_valid),
       .bfly22_i(cbfp2_out_i),
       .bfly22_q(cbfp2_out_q),
       .dout_i(reverse_out_i),
       .dout_q(reverse_out_q),
       .valid_out(reverse_valid)
);

        


        

    // 최종 출력 연결
    assign dout_i = reverse_out_i;
    assign dout_q = reverse_out_q;
    assign o_valid = reverse_valid;

endmodule














