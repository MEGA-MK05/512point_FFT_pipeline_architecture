`timescale 1ns / 10ps

module streaming_bit_reversal #(
    parameter DATA_WIDTH = 13,
    parameter TOTAL_SIZE = 512,
    parameter DATA_PER_CLK = 16
)(
    input logic clk,
    input logic rstn,
    input logic valid_in,
    input logic signed [DATA_WIDTH-1:0] bfly22_i [DATA_PER_CLK],
    input logic signed [DATA_WIDTH-1:0] bfly22_q [DATA_PER_CLK],
    output logic signed [DATA_WIDTH-1:0] dout_i [DATA_PER_CLK],
    output logic signed [DATA_WIDTH-1:0] dout_q [DATA_PER_CLK],
    output logic valid_out
);

    // 비트 리버???�수 (MATLAB�??�일)
    function automatic logic [8:0] bit_reverse;
        input logic [8:0] input_index;
        logic [8:0] reversed;
        begin
            // MATLAB: bitget(jj-1,9)*1 + bitget(jj-1,8)*2 + ... + bitget(jj-1,1)*256
            // SystemVerilog: input_index[8]*1 + input_index[7]*2 + ... + input_index[0]*256
            reversed = input_index[8]*9'd1 + input_index[7]*9'd2 + input_index[6]*9'd4 + 
                      input_index[5]*9'd8 + input_index[4]*9'd16 + input_index[3]*9'd32 + 
                      input_index[2]*9'd64 + input_index[1]*9'd128 + input_index[0]*9'd256;
            bit_reverse = reversed;
        end
    endfunction

    // ?��? ?�?�소 (512�??�이???�??
    logic signed [DATA_WIDTH-1:0] storage_i [TOTAL_SIZE-1:0];
    logic signed [DATA_WIDTH-1:0] storage_q [TOTAL_SIZE-1:0];
    
    // ?��? 카운?�들
    logic [8:0] internal_cycle_idx;  // 0~31 (32?�이??
    logic [5:0] output_counter;
    logic storage_complete;
    logic output_active;
    integer j, k;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            internal_cycle_idx <= 0;
            output_counter <= 0;
            storage_complete <= 1'b0;
            output_active <= 1'b0;
            valid_out <= 1'b0;
            // ?�?�소 초기??            for (k = 0; k < TOTAL_SIZE; k++) begin
                storage_i[k] <= {DATA_WIDTH{1'b0}};
                storage_q[k] <= {DATA_WIDTH{1'b0}};
            end
            // 출력 초기??            for (k = 0; k < DATA_PER_CLK; k++) begin
                dout_i[k] <= {DATA_WIDTH{1'b0}};
                dout_q[k] <= {DATA_WIDTH{1'b0}};
            end
        end else begin
            // valid_in???�어?�면 internal_cycle_idx 증�?
            if (valid_in) begin
                internal_cycle_idx <= internal_cycle_idx + 1;
            end
            
            // 512�??�이???�??(32?�럭) - 비트 리버???�치???�??            if (valid_in && !storage_complete) begin
                for (j = 0; j < DATA_PER_CLK; j++) begin
                    logic [12:0] original_idx;
                    logic [8:0] reversed_idx;
                    original_idx = (internal_cycle_idx << 4) + j;  // internal_cycle_idx * 16
                    reversed_idx = bit_reverse(original_idx[8:0]);  // 비트 리버???�치
                    
                    // ?�버�?출력
                    if (internal_cycle_idx < 2) begin  // 처음 �?개만 출력
                        $display("Time %t: original_idx=%d, reversed_idx=%d, bfly22_i[%d]=%d", 
                                $time, original_idx, reversed_idx, j, bfly22_i[j]);
                    end
                    
                    storage_i[reversed_idx] <= bfly22_i[j];
                    storage_q[reversed_idx] <= bfly22_q[j];
                end
                
                if (internal_cycle_idx >= 31) begin
                    storage_complete <= 1'b1;
                    output_active <= 1'b1;
                    output_counter <= 0;
                end
            end
            
            // ?�???�료 ???�차 출력 (?��? 비트 리버???�치???�?�됨)
            if (output_active) begin
                valid_out <= 1'b1;
                for (j = 0; j < DATA_PER_CLK; j++) begin
                    logic [8:0] output_idx;
                    output_idx = (output_counter << 4) + j;
                    dout_i[j] <= storage_i[output_idx];
                    dout_q[j] <= storage_q[output_idx];
                end

                output_counter <= output_counter + 1;

                if (output_counter >= 32) begin
                    output_active <= 1'b0;
                    valid_out <= 1'b0;
                end
            end else begin
                valid_out <= 1'b0;
            end
        end
    end

endmodule
`timescale 1ns/1ps

//
// ?�라미터?�된 FFT ?�테?��? 버퍼 모듈
module stage_buffer #(
    parameter IN_WIDTH = 9,
    parameter OUT_WIDTH = 10,
    parameter NUM_ELEMS = 256, // 버퍼 깊이 (ex: 256, 128, 64 ...)
    parameter BLK_SIZE = 16,   // ??번에 처리?�는 ?�이??개수
    parameter PIPELINE_DEPTH = 0, // ?�이?�라???�레???�럭 ??    parameter VALID_DELAY = 0  // o_valid 추�? 지???�럭 ??(0: 기본, 1: ???�럭 지??
) (
    input clk,
    input rstn,
    input logic signed [IN_WIDTH-1:0] din_i[0:BLK_SIZE-1],
    input logic signed [IN_WIDTH-1:0] din_q[0:BLK_SIZE-1],
    input i_valid,
    output logic signed [OUT_WIDTH-1:0] dout_i[BLK_SIZE-1:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[BLK_SIZE-1:0],
    output logic o_valid
);
    typedef enum logic [1:0] {INMODE = 0, OUTSUM = 1, OUTMINUS = 2} state_t;
    state_t state;

    // FIFO RAM for input buffer
    logic signed [IN_WIDTH-1:0] ram_i [0:NUM_ELEMS-1];
    logic signed [IN_WIDTH-1:0] ram_q [0:NUM_ELEMS-1];
    // Buffer for subtraction results
    logic signed [OUT_WIDTH-1:0] sub_buf_i [0:NUM_ELEMS-1];
    logic signed [OUT_WIDTH-1:0] sub_buf_q [0:NUM_ELEMS-1];

    logic signed [OUT_WIDTH-1:0] sreg_i2 [BLK_SIZE-1:0];
    logic signed [OUT_WIDTH-1:0] sreg_q2 [BLK_SIZE-1:0];

    integer i, d;
    reg [$clog2(NUM_ELEMS):0] wr_ptr; // write pointer
    reg [$clog2(NUM_ELEMS):0] rd_ptr; // read pointer
    reg [$clog2(NUM_ELEMS/BLK_SIZE):0] blk_cnt; // 블록 카운??    reg valid;
    reg [9:0] total_input; // ?�적 ?�력 개수 (최�? 512)
    reg last_outminus; // 마�?�?OUTMINUS ?�래�?    reg [5:0] valid_timer; // 32?�럭 ?�?�머 (0~63)
    reg valid_start; // valid ?�작 ?�래�?    // reg outsum_first; // ?�거

    // ?�이?�라???�레???��??�터
    logic signed [OUT_WIDTH-1:0] dout_i_pipe [0:PIPELINE_DEPTH][BLK_SIZE-1:0];
    logic signed [OUT_WIDTH-1:0] dout_q_pipe [0:PIPELINE_DEPTH][BLK_SIZE-1:0];
    logic o_valid_pipe [0:PIPELINE_DEPTH];
    
    // o_valid 추�? 지?�을 ?�한 ?��??�터 (VALID_DELAY > 0???�만 ?�용)
    logic o_valid_delay;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= INMODE;
            valid <= 0;
            wr_ptr <= 0;
            rd_ptr <= 0;
            blk_cnt <= 0;
            total_input <= 0;
            last_outminus <= 0;
            valid_timer <= 0;
            valid_start <= 0;
            // outsum_first <= 0; // ?�거
            for (i = 0; i < BLK_SIZE; i++) begin
                sreg_i2[i] <= 0;
                sreg_q2[i] <= 0;
            end
            for (d = 0; d <= PIPELINE_DEPTH; d++) begin
                for (i = 0; i < BLK_SIZE; i++) begin
                    dout_i_pipe[d][i] <= 0;
                    dout_q_pipe[d][i] <= 0;
                end
                o_valid_pipe[d] <= 0;
            end
            if (VALID_DELAY > 0) begin
                o_valid_delay <= 0;
            end
        end else begin
            case (state)
                INMODE: begin
                    if (i_valid && total_input < 512) begin
                        for (i = 0; i < BLK_SIZE; i++) begin
                            ram_i[wr_ptr + i] <= din_i[i];
                            ram_q[wr_ptr + i] <= din_q[i];
                        end
                        wr_ptr <= wr_ptr + BLK_SIZE;
                        blk_cnt <= blk_cnt + 1;
                        total_input <= total_input + BLK_SIZE;
                        if (blk_cnt == (NUM_ELEMS/BLK_SIZE)-1) begin
                            wr_ptr <= 0;
                            rd_ptr <= 0;
                            blk_cnt <= 0;
                            state <= OUTSUM;
                            valid <= 1; // OUTSUM 진입 ??valid=1�?복구
                            valid_start <= 1; // valid ?�작 ?�래�??�정
                            valid_timer <= 0; // ?�?�머 리셋
                            // outsum_first <= 1; // ?�거
                        end
                    end
                end
                OUTSUM: begin
                    if (i_valid && total_input < 512) begin
                        for (i = 0; i < BLK_SIZE; i++) begin
                            sreg_i2[i] <= ram_i[rd_ptr + i] + din_i[i];
                            sreg_q2[i] <= ram_q[rd_ptr + i] + din_q[i];
                            sub_buf_i[rd_ptr + i] <= ram_i[rd_ptr + i] - din_i[i];
                            sub_buf_q[rd_ptr + i] <= ram_q[rd_ptr + i] - din_q[i];
                        end
                        total_input <= total_input + BLK_SIZE;
                    end
                    // outsum_first 관??코드 ?�거
                    if (i_valid) begin
                        if (blk_cnt == (NUM_ELEMS/BLK_SIZE)-1) begin
                            rd_ptr <= 0;
                            blk_cnt <= 0;
                            if (total_input == 512) begin
                                last_outminus <= 1;
                            end
                            state <= OUTMINUS;
                        end else begin
                            rd_ptr <= rd_ptr + BLK_SIZE;
                            blk_cnt <= blk_cnt + 1;
                        end
                    end
                end
                OUTMINUS: begin
                    if (!last_outminus) begin
                        if (i_valid && total_input < 512) begin
                            for (i = 0; i < BLK_SIZE; i++) begin
                                ram_i[wr_ptr + i] <= din_i[i];
                                ram_q[wr_ptr + i] <= din_q[i];
                            end
                            wr_ptr <= wr_ptr + BLK_SIZE;
                            total_input <= total_input + BLK_SIZE;
                        end
                    end
                    for (i = 0; i < BLK_SIZE; i++) begin
                        sreg_i2[i] <= sub_buf_i[rd_ptr + i];
                        sreg_q2[i] <= sub_buf_q[rd_ptr + i];
                    end
                    if (blk_cnt == (NUM_ELEMS/BLK_SIZE)-1) begin
                        rd_ptr <= 0;
                        blk_cnt <= 0;
                        wr_ptr <= 0;
                        if (last_outminus) begin
                            state <= INMODE;
                            valid <= 0;
                            last_outminus <= 0;
                            total_input <= 0;
                            valid_start <= 0; // ?�?�머 ?��?
                            valid_timer <= 0; // ?�?�머 리셋
                        end else begin
                            state <= OUTSUM;
                        end
                    end else begin
                        rd_ptr <= rd_ptr + BLK_SIZE;
                        blk_cnt <= blk_cnt + 1;
                        if (!last_outminus) wr_ptr <= wr_ptr + BLK_SIZE;
                    end
                end
            endcase
            // 32?�럭 ?�?�머 로직
            if (valid_start) begin
                if (valid_timer < 32) begin
                    valid_timer <= valid_timer + 1;
                end else begin
                    valid <= 0; // 32?�럭 ??valid ?�동 ?�제
                    valid_start <= 0; // ?�?�머 ?��?
                end
            end
            
            // ?�이?�라???�레???�용
            dout_i_pipe[0] <= sreg_i2;
            dout_q_pipe[0] <= sreg_q2;
            o_valid_pipe[0] <= valid;
            for (d = 1; d <= PIPELINE_DEPTH; d++) begin
                dout_i_pipe[d] <= dout_i_pipe[d-1];
                dout_q_pipe[d] <= dout_q_pipe[d-1];
                o_valid_pipe[d] <= o_valid_pipe[d-1];
            end
            
            // o_valid 추�? 지??(VALID_DELAY > 0???�만)
            if (VALID_DELAY > 0) begin
                o_valid_delay <= o_valid_pipe[PIPELINE_DEPTH];
            end
        end
    end

    assign dout_i = dout_i_pipe[PIPELINE_DEPTH];
    assign dout_q = dout_q_pipe[PIPELINE_DEPTH];
    assign o_valid = (VALID_DELAY > 0) ? o_valid_delay : o_valid_pipe[PIPELINE_DEPTH];
endmodule



// 16�??�력??즉시 8개씩 ?�누???�셈/뺄셈?�는 모듈
module stage_buffer_und16 #(
    parameter IN_WIDTH = 9,
    parameter OUT_WIDTH = 10,
    parameter BLK_SIZE = 16   // ??번에 처리?�는 ?�이??개수
) (
    input clk,
    input rstn,
    input logic signed [IN_WIDTH-1:0] din_i[BLK_SIZE-1:0],
    input logic signed [IN_WIDTH-1:0] din_q[BLK_SIZE-1:0],
    input i_valid,
    output logic signed [OUT_WIDTH-1:0] dout_i[BLK_SIZE-1:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[BLK_SIZE-1:0],
    output logic o_valid
);
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < BLK_SIZE; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // ??8�? ?�셈 결과 (0~7)
                for (i = 0; i < 8; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+8];
                    dout_q[i] <= din_q[i] + din_q[i+8];
                end
                // ??8�? 뺄셈 결과 (8~15)
                for (i = 8; i < BLK_SIZE; i++) begin
                    dout_i[i] <= din_i[i-8] - din_i[i];
                    dout_q[i] <= din_q[i-8] - din_q[i];
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule



// 16�??�력??즉시 4개씩 ?�누???�셈/뺄셈?�는 모듈
module stage_buffer_und8 #(
    parameter IN_WIDTH = 9,
    parameter OUT_WIDTH = 10,
    parameter BLK_SIZE = 16   // ??번에 처리?�는 ?�이??개수
) (
    input clk,
    input rstn,
    input logic signed [IN_WIDTH-1:0] din_i[BLK_SIZE-1:0],
    input logic signed [IN_WIDTH-1:0] din_q[BLK_SIZE-1:0],
    input i_valid,
    output logic signed [OUT_WIDTH-1:0] dout_i[BLK_SIZE-1:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[BLK_SIZE-1:0],
    output logic o_valid
);
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < BLK_SIZE; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // MATLAB 로직: 8개씩 처리, 4개씩 2그룹?�로 ?�누???�셈/뺄셈
                // 1번째 4�? ?�셈 결과 (0~3)
                for (i = 0; i < 4; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+4];
                    dout_q[i] <= din_q[i] + din_q[i+4];
                end
                // 2번째 4�? 뺄셈 결과 (4~7)
                for (i = 4; i < 8; i++) begin
                    dout_i[i] <= din_i[i-4] - din_i[i];
                    dout_q[i] <= din_q[i-4] - din_q[i];
                end
                // 3번째 4�? ?�셈 결과 (8~11)
                for (i = 8; i < 12; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+4];
                    dout_q[i] <= din_q[i] + din_q[i+4];
                end
                // 4번째 4�? 뺄셈 결과 (12~15)
                for (i = 12; i < BLK_SIZE; i++) begin
                    dout_i[i] <= din_i[i-4] - din_i[i];
                    dout_q[i] <= din_q[i-4] - din_q[i];
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule



// 16�??�력??즉시 2개씩 ?�누???�셈/뺄셈?�는 모듈
module stage_buffer_und4 #(
    parameter IN_WIDTH = 9,
    parameter OUT_WIDTH = 10,
    parameter BLK_SIZE = 16   // ??번에 처리?�는 ?�이??개수
) (
    input clk,
    input rstn,
    input logic signed [IN_WIDTH-1:0] din_i[BLK_SIZE-1:0],
    input logic signed [IN_WIDTH-1:0] din_q[BLK_SIZE-1:0],
    input i_valid,
    output logic signed [OUT_WIDTH-1:0] dout_i[BLK_SIZE-1:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[BLK_SIZE-1:0],
    output logic o_valid
);
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < BLK_SIZE; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // 1번째 2�? ?�셈 결과 (0~1)
                for (i = 0; i < 2; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+2];
                    dout_q[i] <= din_q[i] + din_q[i+2];
                end
                // 2번째 2�? 뺄셈 결과 (2~3)
                for (i = 2; i < 4; i++) begin
                    dout_i[i] <= din_i[i-2] - din_i[i];
                    dout_q[i] <= din_q[i-2] - din_q[i];
                end
                // 3번째 2�? ?�셈 결과 (4~5)
                for (i = 4; i < 6; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+2];
                    dout_q[i] <= din_q[i] + din_q[i+2];
                end
                // 4번째 2�? 뺄셈 결과 (6~7)
                for (i = 6; i < 8; i++) begin
                    dout_i[i] <= din_i[i-2] - din_i[i];
                    dout_q[i] <= din_q[i-2] - din_q[i];
                end
                // 5번째 2�? ?�셈 결과 (8~9)
                for (i = 8; i < 10; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+2];
                    dout_q[i] <= din_q[i] + din_q[i+2];
                end
                // 6번째 2�? 뺄셈 결과 (10~11)
                for (i = 10; i < 12; i++) begin
                    dout_i[i] <= din_i[i-2] - din_i[i];
                    dout_q[i] <= din_q[i-2] - din_q[i];
                end
                // 7번째 2�? ?�셈 결과 (12~13)
                for (i = 12; i < 14; i++) begin
                    dout_i[i] <= din_i[i] + din_i[i+2];
                    dout_q[i] <= din_q[i] + din_q[i+2];
                end
                // 8번째 2�? 뺄셈 결과 (14~15)
                for (i = 14; i < BLK_SIZE; i++) begin
                    dout_i[i] <= din_i[i-2] - din_i[i];
                    dout_q[i] <= din_q[i-2] - din_q[i];
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule


module stage_buffer_und2 #(
    parameter IN_WIDTH = 15,
    parameter OUT_WIDTH = 16,
    parameter BLK_SIZE = 16
) (
    input clk,
    input rstn,
    input logic signed [IN_WIDTH-1:0] din_i[BLK_SIZE-1:0],
    input logic signed [IN_WIDTH-1:0] din_q[BLK_SIZE-1:0],
    input i_valid,
    output logic signed [OUT_WIDTH-1:0] dout_i[BLK_SIZE-1:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[BLK_SIZE-1:0],
    output logic o_valid
);
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < BLK_SIZE; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // 8�?그룹?�로 ?�누??2개씩 버터?�라??                for (i = 0; i < BLK_SIZE; i = i + 2) begin
                    // ?�셈
                    dout_i[i] <= din_i[i] + din_i[i+1];
                    dout_q[i] <= din_q[i] + din_q[i+1];
                    // 뺄셈
                    dout_i[i+1] <= din_i[i] - din_i[i+1];
                    dout_q[i+1] <= din_q[i] - din_q[i+1];
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule
`timescale 1ns / 1ps


// indexsum_re 계산???�한 조합?�리 모듈
module indexsum_calculator #(
    parameter SHIFT_WIDTH = 5,
    parameter TOTAL_SIZE = 512,
    parameter DATA_PER_CLK = 16
)(
    input logic [8:0] internal_cycle_idx,
    input logic [SHIFT_WIDTH-1:0] applied_shift_out_0 [TOTAL_SIZE],
    input logic [SHIFT_WIDTH-1:0] applied_shift_out_1 [TOTAL_SIZE],
    output logic [SHIFT_WIDTH:0] indexsum_re [DATA_PER_CLK-1:0],
    output logic [SHIFT_WIDTH:0] indexsum_im [DATA_PER_CLK-1:0]
);

    integer i;
    integer global_idx;
    logic [8:0] reverse_idx [DATA_PER_CLK-1:0];

    always_comb begin
        for (i = 0; i < DATA_PER_CLK; i++) begin
            global_idx = internal_cycle_idx * DATA_PER_CLK + i;
            // applied_shift_out ?�근 ?�덱?��? 511부??거꾸�?            reverse_idx[i] = TOTAL_SIZE - 1 - global_idx;  // 511부??0까�?

            indexsum_re[i] = applied_shift_out_0[reverse_idx[i]] + applied_shift_out_1[reverse_idx[i]];
            indexsum_im[i] = applied_shift_out_0[reverse_idx[i]] + applied_shift_out_1[reverse_idx[i]];
        end
    end

endmodule

module final_cbfp_scaler #(
    parameter IN_WIDTH      = 16,
    parameter OUT_WIDTH     = 13,
    parameter SHIFT_WIDTH   = 5,
    parameter DATA_PER_CLK  = 16,
    parameter TOTAL_SIZE    = 512
)(
    input  logic                      clk,
    input  logic                      rstn,
    input  logic                      valid_in,
    input  logic signed [IN_WIDTH-1:0]  din_i [DATA_PER_CLK],
    input  logic signed [IN_WIDTH-1:0]  din_q [DATA_PER_CLK],
    input  logic [SHIFT_WIDTH-1:0]      applied_shift_out_0 [TOTAL_SIZE],
    input  logic [SHIFT_WIDTH-1:0]      applied_shift_out_1 [TOTAL_SIZE],
    output logic signed [OUT_WIDTH-1:0] dout_i [DATA_PER_CLK],
    output logic signed [OUT_WIDTH-1:0] dout_q [DATA_PER_CLK],
    output logic                      valid_out
);

    // ?��? 카운??- valid_in???�어???�만 증�?
    logic [8:0] internal_cycle_idx;
    // valid_out ?�어�??�한 카운??    logic [5:0] valid_counter;
    logic valid_out_active;
    
    // indexsum 계산???�한 조합?�리 모듈 ?�스?�스
    logic [SHIFT_WIDTH:0] indexsum_re [DATA_PER_CLK-1:0], indexsum_im [DATA_PER_CLK-1:0];
    
    indexsum_calculator #(
        .SHIFT_WIDTH(SHIFT_WIDTH),
        .TOTAL_SIZE(TOTAL_SIZE),
        .DATA_PER_CLK(DATA_PER_CLK)
    ) indexsum_calc (
        .internal_cycle_idx(internal_cycle_idx),
        .applied_shift_out_0(applied_shift_out_0),
        .applied_shift_out_1(applied_shift_out_1),
        .indexsum_re(indexsum_re),
        .indexsum_im(indexsum_im)
    );
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            internal_cycle_idx <= 0;
            valid_counter <= 0;
            valid_out_active <= 1'b0;
        end else begin
            if (valid_in) begin
            internal_cycle_idx <= internal_cycle_idx + 1;
                // valid_in???�어?�면 valid_out_active ?�작
                if (!valid_out_active) begin
                    valid_out_active <= 1'b1;
                    valid_counter <= 0;
                end
            end
            
            // valid_out_active가 ?�성?�되�?카운??증�?
            if (valid_out_active) begin
                if (valid_counter < 32) begin
                    valid_counter <= valid_counter + 1;
                end else begin
                    valid_out_active <= 1'b0;  // 32?�럭 ??비활?�화
                end
            end
        end
    end

    always_ff @(posedge clk or negedge rstn) begin
        integer i;
        logic signed [6:0] shift_amt_re, shift_amt_im;
        if (!rstn) begin
            valid_out <= 1'b0;
            for (i = 0; i < DATA_PER_CLK; i++) begin
                dout_i[i] <= {OUT_WIDTH{1'b0}};
                dout_q[i] <= {OUT_WIDTH{1'b0}};
            end
        end else begin
            if (valid_in) begin
                // valid_in???�어?�면 ?�음 ?�럭??valid_out ?�성??                valid_out <= 1'b1;
                
                for (i = 0; i < DATA_PER_CLK; i++) begin
                    // Real Part (I) - din?� 15부??0까�?, indexsum?� 0부??15까�? 매칭
                    shift_amt_re = 7'd9 - indexsum_re[i];
                    if (indexsum_re[i] >= 23)
                        dout_i[i] <= {OUT_WIDTH{1'b0}};
                    else if (shift_amt_re[6])  // ?�수??경우 (MSB가 1)
                        dout_i[i] <= din_i[DATA_PER_CLK-1-i] >>> (-shift_amt_re);
                    else  // ?�수??경우
                        dout_i[i] <= din_i[DATA_PER_CLK-1-i] <<< shift_amt_re;

                    // Imaginary Part (Q) - din?� 15부??0까�?, indexsum?� 0부??15까�? 매칭
                    shift_amt_im = 7'd9 - indexsum_im[i];
                    if (indexsum_im[i] >= 23)
                        dout_q[i] <= {OUT_WIDTH{1'b0}};
                    else if (shift_amt_im[6])  // ?�수??경우 (MSB가 1)
                        dout_q[i] <= din_q[DATA_PER_CLK-1-i] >>> (-shift_amt_im);
                    else  // ?�수??경우
                        dout_q[i] <= din_q[DATA_PER_CLK-1-i] <<< shift_amt_im;
                end
            end else begin
                // 32?�럭 ?�에??무조�?valid_out 비활?�화
                if (valid_counter >= 32) begin
                    valid_out <= 1'b0;
                end else begin
                    valid_out <= valid_out;  // ?�전 �??��?
                end
            end
        end
    end

endmodule

module fft_cbfp_module1 (
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input  logic signed [24:0] pre_bfly12_real_in [15:0],  // 16개의 25bit ?�수부 ?�력
    input  logic signed [24:0] pre_bfly12_imag_in [15:0],  // 16개의 25bit ?�수부 ?�력
    output logic [4:0] applied_shift_out_2 [511:0],
    output logic valid_out,
    output logic signed [11:0] bfly12_real_out [15:0],     // 16개의 12bit ?�수부 출력
    output logic signed [11:0] bfly12_imag_out [15:0]      // 16개의 12bit ?�수부 출력
);

    // Parameters
    localparam int DATA_WIDTH = 25;
    localparam int OUTPUT_WIDTH = 12;
    localparam int SHIFT_WIDTH = 5;
    localparam int DATA_PER_CLK = 16;
    localparam int GROUP_SIZE = 8;              // �?블록??8�??�이??    localparam int NUM_8_GROUPS = 2;            // 16�??�이?��? 8개씩 2그룹?�로 처리
    localparam int TARGET_SHIFT = 13;           // ?��??�링 기�?�?    localparam int NUM_64_BLOCKS = 64;          // �?64�?블록

    // =============== ?�트리밍 처리??변?�들 ===============
    logic [8:0] data_counter;                  // ?�이??카운??(0~511)
    logic [5:0] valid_counter;                 // valid ?�어??카운??
    function automatic logic [4:0] magnitude_detector;
        input logic signed [24:0] input_data;
        logic [24:0] d;
        logic [4:0] count;
        logic s;
        begin
            d = input_data;
            s = d[24]; // sign bit

            // leading sign extension count
            count = (d[23] != s) ? 5'd0  :
                    (d[22] != s) ? 5'd1  :
                    (d[21] != s) ? 5'd2  :
                    (d[20] != s) ? 5'd3  :
                    (d[19] != s) ? 5'd4  :
                    (d[18] != s) ? 5'd5  :
                    (d[17] != s) ? 5'd6  :
                    (d[16] != s) ? 5'd7  :
                    (d[15] != s) ? 5'd8  :
                    (d[14] != s) ? 5'd9  :
                    (d[13] != s) ? 5'd10 :
                    (d[12] != s) ? 5'd11 :
                    (d[11] != s) ? 5'd12 :
                    (d[10] != s) ? 5'd13 :
                    (d[9]  != s) ? 5'd14 :
                    (d[8]  != s) ? 5'd15 :
                    (d[7]  != s) ? 5'd16 :
                    (d[6]  != s) ? 5'd17 :
                    (d[5]  != s) ? 5'd18 :
                    (d[4]  != s) ? 5'd19 :
                    (d[3]  != s) ? 5'd20 :
                    (d[2]  != s) ? 5'd21 :
                    (d[1]  != s) ? 5'd22 :
                    (d[0]  != s) ? 5'd23 :
                                   5'd24 ;  // all bits match sign
            magnitude_detector = count;
        end
    endfunction

    // =============== 8�?�?�?최솟�?찾기 (조합?�리) ===============
    function automatic logic [SHIFT_WIDTH-1:0] minimum_finder_8;
        input [SHIFT_WIDTH-1:0] input_array[7:0];
        logic [SHIFT_WIDTH-1:0] level1 [3:0];
        logic [SHIFT_WIDTH-1:0] level2 [1:0];
        logic [SHIFT_WIDTH-1:0] result;
        begin
            for (int i = 0; i < 4; i++) begin
                level1[i] = (input_array[i*2] < input_array[i*2+1]) ? input_array[i*2] : input_array[i*2+1];
            end
            for (int i = 0; i < 2; i++) begin
                level2[i] = (level1[i*2] < level1[i*2+1]) ? level1[i*2] : level1[i*2+1];
            end
            result = (level2[0] < level2[1]) ? level2[0] : level2[1];
            minimum_finder_8 = result;
        end
    endfunction

    // =============== Barrel Shifter (조합?�리) ===============
    function automatic logic [OUTPUT_WIDTH-1:0] barrel_shifter_normalize;
        input [DATA_WIDTH-1:0] input_data;
        input [SHIFT_WIDTH-1:0] shift_amount;
        logic signed [63:0] temp_result;
        begin
            temp_result = input_data;
            if (shift_amount > TARGET_SHIFT) begin
                // ?�효비트?��? ?�음 -> ?�쪽 ?�프?????�른�??�프??                temp_result = temp_result <<< (shift_amount - TARGET_SHIFT);
            end else begin
                // ?�른�??�프?�로 12비트 ?��??�링
                temp_result = temp_result >>> (TARGET_SHIFT - shift_amount);
            end
            barrel_shifter_normalize = temp_result[OUTPUT_WIDTH-1:0];
        end
    endfunction

    // =============== ?�트리밍 ?�력 처리 (블록 ?�위 최적???��?) ===============
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_counter <= 0;
            valid_counter <= 0;
            // applied_shift_out_2 초기??            for (int i = 0; i < 512; i++) begin
                applied_shift_out_2[i] <= 5'd25;
            end
        end else if (valid_in) begin
            // 16�??�이?��? 8개씩 2그룹?�로 ?�누??처리 (기존 로직 ?��?)
            logic [4:0] mag_real[15:0], mag_imag[15:0];
            logic [4:0] mag_real_grp0[7:0], mag_real_grp1[7:0];
            logic [4:0] mag_imag_grp0[7:0], mag_imag_grp1[7:0];
            logic [4:0] min_real_grp0, min_real_grp1;
            logic [4:0] min_imag_grp0, min_imag_grp1;
            logic [4:0] final_min_blk0, final_min_blk1;
            
            // ?�재 ?�력 ?�이?�의 magnitude 계산
            for (int i = 0; i < 16; i++) begin
                mag_real[i] = magnitude_detector(pre_bfly12_real_in[i]);
                mag_imag[i] = magnitude_detector(pre_bfly12_imag_in[i]);
            end

            // 그룹별로 분리 (0~7, 8~15)
            for (int i = 0; i < 8; i++) begin
                mag_real_grp0[i] = mag_real[i];      // 0~7
                mag_real_grp1[i] = mag_real[i+8];    // 8~15
                mag_imag_grp0[i] = mag_imag[i];      // 0~7
                mag_imag_grp1[i] = mag_imag[i+8];    // 8~15
            end

            // �?그룹�?최솟�?찾기
            min_real_grp0 = minimum_finder_8(mag_real_grp0);
            min_real_grp1 = minimum_finder_8(mag_real_grp1);
            min_imag_grp0 = minimum_finder_8(mag_imag_grp0);
            min_imag_grp1 = minimum_finder_8(mag_imag_grp1);

            // �?블록�?최종 최솟�?(?�수부?� ?�수부 �??��? �?
            final_min_blk0 = (min_real_grp0 < min_imag_grp0) ? min_real_grp0 : min_imag_grp0;
            final_min_blk1 = (min_real_grp1 < min_imag_grp1) ? min_real_grp1 : min_imag_grp1;
            
            // applied_shift_out_2??블록 ?�위 shift�??�??            for (int i = 0; i < 8; i++) begin
                applied_shift_out_2[data_counter + i] <= final_min_blk0;      // 0~7
                applied_shift_out_2[data_counter + i + 8] <= final_min_blk1;  // 8~15
            end
            
            // ?�이??카운???�데?�트
            data_counter <= data_counter + 16;
            
            // valid 카운???�데?�트 (32?�럭 ?�한)
            if (valid_counter < 32) begin
                valid_counter <= valid_counter + 1;
            end
        end
    end

    // =============== ?�트리밍 출력 처리 (블록 ?�위 최적???��?) ===============
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 0;
            // 출력 초기??            for (int i = 0; i < 16; i++) begin
                bfly12_real_out[i] <= 0;
                bfly12_imag_out[i] <= 0;
            end
        end else if (valid_in) begin
            // 16�??�이?��? 8개씩 2그룹?�로 ?�누??처리 (기존 로직 ?��?)
            logic [4:0] mag_real[15:0], mag_imag[15:0];
            logic [4:0] mag_real_grp0[7:0], mag_real_grp1[7:0];
            logic [4:0] mag_imag_grp0[7:0], mag_imag_grp1[7:0];
            logic [4:0] min_real_grp0, min_real_grp1;
            logic [4:0] min_imag_grp0, min_imag_grp1;
            logic [4:0] final_min_blk0, final_min_blk1;
            
            // ?�재 ?�력 ?�이?�의 magnitude 계산
            for (int i = 0; i < 16; i++) begin
                mag_real[i] = magnitude_detector(pre_bfly12_real_in[i]);
                mag_imag[i] = magnitude_detector(pre_bfly12_imag_in[i]);
            end

            // 그룹별로 분리 (0~7, 8~15)
            for (int i = 0; i < 8; i++) begin
                mag_real_grp0[i] = mag_real[i];      // 0~7
                mag_real_grp1[i] = mag_real[i+8];    // 8~15
                mag_imag_grp0[i] = mag_imag[i];      // 0~7
                mag_imag_grp1[i] = mag_imag[i+8];    // 8~15
            end

            // �?그룹�?최솟�?찾기
            min_real_grp0 = minimum_finder_8(mag_real_grp0);
            min_real_grp1 = minimum_finder_8(mag_real_grp1);
            min_imag_grp0 = minimum_finder_8(mag_imag_grp0);
            min_imag_grp1 = minimum_finder_8(mag_imag_grp1);

            // �?블록�?최종 최솟�?(?�수부?� ?�수부 �??��? �?
            final_min_blk0 = (min_real_grp0 < min_imag_grp0) ? min_real_grp0 : min_imag_grp0;
            final_min_blk1 = (min_real_grp1 < min_imag_grp1) ? min_real_grp1 : min_imag_grp1;
            
            // 블록 ?�위 shift값으�??�규?�하??출력
            for (int i = 0; i < 8; i++) begin
                // �?번째 블록 (0~7) - final_min_blk0 ?�용
                bfly12_real_out[i] <= barrel_shifter_normalize(pre_bfly12_real_in[i], final_min_blk0);
                bfly12_imag_out[i] <= barrel_shifter_normalize(pre_bfly12_imag_in[i], final_min_blk0);
                
                // ??번째 블록 (8~15) - final_min_blk1 ?�용
                bfly12_real_out[i + 8] <= barrel_shifter_normalize(pre_bfly12_real_in[i + 8], final_min_blk1);
                bfly12_imag_out[i + 8] <= barrel_shifter_normalize(pre_bfly12_imag_in[i + 8], final_min_blk1);
            end
            
            // valid_out ?�어 (32?�럭 ?�한)
            if (valid_counter < 32) begin
                valid_out <= 1;
            end else begin
                valid_out <= 0;
            end
        end else begin
            valid_out <= 0;
        end
    end



endmodule


module fft_cbfp_module0 (
    input logic clk,
    input logic rstn,
    input logic valid_in,
    input  logic signed [22:0] pre_bfly02_real_in [15:0],  // 16개의 23bit ?�수부 ?�력
    input  logic signed [22:0] pre_bfly02_imag_in [15:0],  // 16개의 23bit ?�수부 ?�력
    output logic [4:0] applied_shift_out [511:0],
    output logic valid_out,
    output logic signed [10:0] bfly02_real_out [15:0],     // 16개의 11bit ?�수부 출력
    output logic signed [10:0] bfly02_imag_out [15:0]      // 16개의 11bit ?�수부 출력
);

    // Parameters
    localparam int DATA_WIDTH = 23;
    localparam int OUTPUT_WIDTH = 11;
    localparam int SHIFT_WIDTH = 5;
    localparam int DATA_PER_CLK = 16;
    localparam int GROUP_SIZE = 64;
    localparam int NUM_16_GROUPS = 4;
    localparam int TARGET_SHIFT = 12;
    localparam int NUM_64_BLOCKS = 8;

    // =============== Block Storage 구조 (8�?블록) ===============
    logic signed[DATA_WIDTH-1:0] block_storage_real [NUM_64_BLOCKS-1:0][GROUP_SIZE-1:0];
    logic signed[DATA_WIDTH-1:0] block_storage_imag [NUM_64_BLOCKS-1:0][GROUP_SIZE-1:0];

    // ?�력 ?�어 변?�들
    logic [1:0] input_group_counter;  // ?�재 ?�력받는 그룹 (0~3)
    logic [2:0] input_block_counter;  // ?�재 ?�력받는 블록 (0~7)

    // =============== ?�이?�라??버퍼 ?��??�터??===============
    // Stage 1: ?�력 ?�이??버퍼 (조합?�리 처리 ?�한 1?�럭 지??
    logic signed[DATA_WIDTH-1:0] stage1_buffer_real[DATA_PER_CLK-1:0];
    logic signed [DATA_WIDTH-1:0] stage1_buffer_imag[DATA_PER_CLK-1:0];
    logic [1:0] stage1_group_counter;
    logic [2:0] stage1_block_counter;
    logic stage1_valid;

    // �?블록�?16�?그룹??min�??�??    logic signed [SHIFT_WIDTH-1:0] block_group_min_real [NUM_64_BLOCKS-1:0][NUM_16_GROUPS-1:0];
    logic signed [SHIFT_WIDTH-1:0] block_group_min_imag [NUM_64_BLOCKS-1:0][NUM_16_GROUPS-1:0];
    logic [NUM_64_BLOCKS-1:0][NUM_16_GROUPS-1:0] group_min_valid;

    // �?블록�?최종 shift�?    logic [SHIFT_WIDTH-1:0] block_shift_value[NUM_64_BLOCKS-1:0];
    logic [NUM_64_BLOCKS-1:0] block_shift_ready;//array vs bit -> compare

    // 출력 ?�어
    logic [2:0] output_block_counter;
    logic [1:0] output_group_counter;
    logic output_active;
    logic [5:0] pipeline_delay_counter;  // ?�이?�라??지??카운??    logic [5:0] output_counter;  // 출력 카운??(32?�럭 카운??

    function automatic logic [4:0] magnitude_detector;
        input logic signed [22:0] input_data;
        logic [22:0] d;
        logic [4:0] count;
        logic s;
        begin
            d = input_data;
            // sign bit
            s = d[22];

            // leading sign extension count
            count = (d[21] != s) ? 5'd0  :
                    (d[20] != s) ? 5'd1  :
                    (d[19] != s) ? 5'd2  :
                    (d[18] != s) ? 5'd3  :
                    (d[17] != s) ? 5'd4  :
                    (d[16] != s) ? 5'd5  :
                    (d[15] != s) ? 5'd6  :
                    (d[14] != s) ? 5'd7  :
                    (d[13] != s) ? 5'd8  :
                    (d[12] != s) ? 5'd9  :
                    (d[11] != s) ? 5'd10 :
                    (d[10] != s) ? 5'd11 :
                    (d[9]  != s) ? 5'd12 :
                    (d[8]  != s) ? 5'd13 :
                    (d[7]  != s) ? 5'd14 :
                    (d[6]  != s) ? 5'd15 :
                    (d[5]  != s) ? 5'd16 :
                    (d[4]  != s) ? 5'd17 :
                    (d[3]  != s) ? 5'd18 :
                    (d[2]  != s) ? 5'd19 :
                    (d[1]  != s) ? 5'd20 :
                    (d[0]  != s) ? 5'd21 :
                                   5'd22 ;  // all bits match sign
            magnitude_detector = count;
        end
    endfunction

    // =============== 16�?�?�?최솟�?찾기 (조합?�리) ===============
    function automatic logic [SHIFT_WIDTH-1:0] minimum_finder_16;
        input [SHIFT_WIDTH-1:0] input_array[15:0];

        logic [SHIFT_WIDTH-1:0] level1 [7:0];
        logic [SHIFT_WIDTH-1:0] level2 [3:0];
        logic [SHIFT_WIDTH-1:0] level3 [1:0];
        logic [SHIFT_WIDTH-1:0] result;

        begin
            for (int i = 0; i < 8; i++) begin
                level1[i] = (input_array[i*2] < input_array[i*2+1]) ? input_array[i*2] : input_array[i*2+1];
            end

            for (int i = 0; i < 4; i++) begin
                level2[i] = (level1[i*2] < level1[i*2+1]) ? level1[i*2] : level1[i*2+1];
            end

            for (int i = 0; i < 2; i++) begin
                level3[i] = (level2[i*2] < level2[i*2+1]) ? level2[i*2] : level2[i*2+1];
            end

            result = (level3[0] < level3[1]) ? level3[0] : level3[1];
            minimum_finder_16 = result;
        end
    endfunction

    // =============== 4�?�?�?최솟�?찾기 (조합?�리) ===============
    function automatic logic [SHIFT_WIDTH-1:0] minimum_finder_4;
        input [SHIFT_WIDTH-1:0] input_array[3:0];

        logic [SHIFT_WIDTH-1:0] level1 [1:0];
        logic [SHIFT_WIDTH-1:0] result;

        begin
            level1[0] = (input_array[0] < input_array[1]) ? input_array[0] : input_array[1];
            level1[1] = (input_array[2] < input_array[3]) ? input_array[2] : input_array[3];
            result = (level1[0] < level1[1]) ? level1[0] : level1[1];
            minimum_finder_4 = result;
        end
    endfunction

    // =============== Barrel Shifter (조합?�리) ===============
    function automatic logic [OUTPUT_WIDTH-1:0] barrel_shifter_normalize;
        input [DATA_WIDTH-1:0] input_data;
        input [SHIFT_WIDTH-1:0] shift_amount;

        logic signed [63:0] temp_result;
        begin
            temp_result = input_data;

            if (shift_amount > TARGET_SHIFT) begin
                // ?�효비트?��? ?�음 -> ?�쪽 ?�프?????�른�??�프??                temp_result = temp_result <<< (shift_amount - TARGET_SHIFT);
            end else begin
                // ?�른�??�프?�로 11비트 ?��??�링
                temp_result = temp_result >>> (TARGET_SHIFT - shift_amount);
            end

            barrel_shifter_normalize = temp_result[OUTPUT_WIDTH-1:0];
        end
    endfunction

    // =============== ?�력 �?Block Storage (�??�럭) ===============
    int i, j, b, k, l, m, n, d, c,i1;
    int storage_index;
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            input_group_counter <= 0;
            input_block_counter <= 0;
        end else if (valid_in) begin
            // Block Storage??512�?�??�??16?�럭?�안)
            for (i = 0; i < DATA_PER_CLK; i++) begin
                storage_index = input_group_counter * DATA_PER_CLK + i;
                block_storage_real[input_block_counter][storage_index] <= pre_bfly02_real_in[i];
                block_storage_imag[input_block_counter][storage_index] <= pre_bfly02_imag_in[i];
            end

       

            // 카운???�데?�트
            if (input_group_counter == 3) begin
                input_group_counter <= 0;
                if (input_block_counter == 7) begin
                    input_block_counter <= 0;
                end else begin
                    input_block_counter <= input_block_counter + 1;
                end
            end else begin
                input_group_counter <= input_group_counter + 1;
            end
        end
    end

    // =============== Stage 1: ?�이?�라??버퍼 ===============
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            stage1_valid <= 0;
            stage1_group_counter <= 0;
            stage1_block_counter <= 0;
        end else begin
            stage1_valid <= valid_in;
            stage1_group_counter <= input_group_counter;
            stage1_block_counter <= input_block_counter;

            if (valid_in) begin  //16개만 ?�로 ?�??                for (j = 0; j < DATA_PER_CLK; j++) begin
                    stage1_buffer_real[j] <= pre_bfly02_real_in[j];
                    stage1_buffer_imag[j] <= pre_bfly02_imag_in[j];
                end
      
            end
        end
    end

    // =============== Magnitude Detection & Min Finding (조합?�리 + ?��??�터) ===============
    // 조합?�리 처리
    logic [SHIFT_WIDTH-1:0] current_mag_real[DATA_PER_CLK-1:0];
    logic [SHIFT_WIDTH-1:0] current_mag_imag[DATA_PER_CLK-1:0];
    logic [SHIFT_WIDTH-1:0] current_min_real, current_min_imag;

    // Magnitude Detection (조합?�리)
    always_comb begin
        for (k = 0; k < DATA_PER_CLK; k++) begin
            current_mag_real[k] = magnitude_detector(stage1_buffer_real[k]);
            current_mag_imag[k] = magnitude_detector(stage1_buffer_imag[k]);
        end
    end

    // Min Finding (조합?�리)
    always_comb begin  //?�?�밍 ?�심??�?        current_min_real = minimum_finder_16(current_mag_real);
        current_min_imag = minimum_finder_16(current_mag_imag);
    end

    // 결과 ?�??(?��??�터)
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            
            //block_group_min_real <= '{default:5'd23};
            //block_group_min_imag <= '{default:5'd23};
            //group_min_valid <= '{default:0}'
            
            for (b = 0; b < NUM_64_BLOCKS; b++) begin
                for (int g = 0; g < NUM_16_GROUPS; g++) begin
                    block_group_min_real[b][g] <= 5'd23;
                    block_group_min_imag[b][g] <= 5'd23;
                    group_min_valid[b][g] <= 0;
                end
            end
        end else if (stage1_valid) begin
            // ?�당 블록???�당 그룹??min�??�??            block_group_min_real[stage1_block_counter][stage1_group_counter] <= current_min_real;
            block_group_min_imag[stage1_block_counter][stage1_group_counter] <= current_min_imag;
            group_min_valid[stage1_block_counter][stage1_group_counter] <= 1;
        end
    end

    // =============== 블록�?최종 Min�?결정 ===============
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            /*
            block_shift_value <= '{default: 5'd23};
            block_shift_ready <= '{default: 0};
            */
            for (l = 0; l < NUM_64_BLOCKS; l++) begin
                block_shift_value[l] <= 5'd23;
                block_shift_ready[l] <= 0;
            end
        end else begin
            // �?블록???�??4�?그룹??모두 ?�료?�었?��? ?�인
            for (m = 0; m < NUM_64_BLOCKS; m++) begin
                if (!block_shift_ready[m] && 
                    group_min_valid[m][0] && group_min_valid[m][1] && 
                    group_min_valid[m][2] && group_min_valid[m][3]) begin

                    // 4�?그룹??min값들 �?최솟�?찾기 (조합?�리)
                    logic [SHIFT_WIDTH-1:0] temp_real_array[3:0];
                    logic [SHIFT_WIDTH-1:0] temp_imag_array[3:0];
                    logic [SHIFT_WIDTH-1:0]
                        final_min_real, final_min_imag, final_min;

                    temp_real_array[0] = block_group_min_real[m][0];
                    temp_real_array[1] = block_group_min_real[m][1];
                    temp_real_array[2] = block_group_min_real[m][2];
                    temp_real_array[3] = block_group_min_real[m][3];

                    temp_imag_array[0] = block_group_min_imag[m][0];
                    temp_imag_array[1] = block_group_min_imag[m][1];
                    temp_imag_array[2] = block_group_min_imag[m][2];
                    temp_imag_array[3] = block_group_min_imag[m][3];

                    final_min_real = minimum_finder_4(temp_real_array);
                    final_min_imag = minimum_finder_4(temp_imag_array);

                    // ?�수부?� ?�수부 �????��? 값으�??�일
                    final_min = (final_min_real <= final_min_imag) ? final_min_real : final_min_imag;

                    block_shift_value[m] <= final_min;
                    block_shift_ready[m] <= 1;

        
                end
            end
        end
    end
    logic block_ready;
    assign block_ready = block_shift_ready[output_block_counter];

    // =============== Applied Shift Amount mapping 로직 ===============
    // �?블록�?shift amount(8�?�?512�??�이???�인??8*64)??매핑

    int block_idx_shift, data_idx_shift, global_index_shift, init_idx_shift;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            // 초기??            for (init_idx_shift = 0; init_idx_shift < 512; init_idx_shift++) begin
                applied_shift_out[init_idx_shift] <= 5'd23;  // 초기�? 최�? shift
            end
        end else begin
            // 블록 shift ready =1 -> ?�당 블록??64�??�이?�에 매핑
            for (block_idx_shift = 0; block_idx_shift < NUM_64_BLOCKS; block_idx_shift++) begin
                if (block_shift_ready[block_idx_shift]) begin
                    // �?블록??64�??�이???�인?�에 ?�일??shift amount ?�용
                    for (data_idx_shift = 0; data_idx_shift < GROUP_SIZE; data_idx_shift++) begin
                        global_index_shift = block_idx_shift * GROUP_SIZE + data_idx_shift;
                        applied_shift_out[global_index_shift] <= block_shift_value[block_idx_shift];
                    end
                end
            end
        end
    end
    
    // =============== 출력 ?�어 (?�속 출력) ===============
    int output_storage_index;
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            output_block_counter <= 0;
            output_group_counter <= 0;
            output_active <= 0;
            valid_out <= 0;
            output_counter <= 0;
            pipeline_delay_counter <= 0;
            // 출력 초기??            for (n = 0; n < DATA_PER_CLK; n++) begin
                bfly02_real_out[n] <= 11'b0;
                bfly02_imag_out[n] <= 11'b0;
            end
        end else begin
            // ?�이?�라??지????출력 ?�작 (?�로???�력???�어?�면 ?�시 ?�작)
            if (valid_in && pipeline_delay_counter < 6) begin
                pipeline_delay_counter <= pipeline_delay_counter + 1;
            end else if (pipeline_delay_counter == 6 && !output_active) begin
                output_active <= 1;
                pipeline_delay_counter <= 0;
                output_counter <= 0;  // ?�로???�력 ?�작 ??카운??리셋
            end 
        

            // ?�속 출력 (all enable ?�태)
            if (output_active && block_shift_ready[output_block_counter] && output_counter < 33) begin
                valid_out <= 1;
                output_counter <= output_counter + 1;  // 출력 카운??증�?

                // Barrel Shifter�??�규?�하??출력
                for (c = 0; c < DATA_PER_CLK; c++) begin
                    output_storage_index = output_group_counter * DATA_PER_CLK + c;

                    bfly02_real_out[c] <= barrel_shifter_normalize(
                        block_storage_real[output_block_counter][output_storage_index],
                        block_shift_value[output_block_counter]
                    );
                    bfly02_imag_out[c] <= barrel_shifter_normalize(
                        block_storage_imag[output_block_counter][output_storage_index],
                        block_shift_value[output_block_counter]
                    );
                end

                // ?�음 그룹?�로 진행
                if (output_group_counter == 3) begin
                    output_group_counter <= 0;
                                    if (output_block_counter == 7) begin
                    output_block_counter <= 0;
                    // output_active <= 0;  // ?�체 ?�료 ?�에??비활?�화?��? ?�음 - ?�음 ?�력 ?��?                        // valid_out?� output_counter�??�어?��?�??�기?�는 ?�정?��? ?�음       
                        // ?�속 처리�??�해 output_active???��?
                    end else begin
                        output_block_counter <= output_block_counter + 1;
                    end
                end else begin
                    output_group_counter <= output_group_counter + 1;
                end
            end else begin
                // 33?�럭 ??무조�?valid_out??0?�로 ?�정
                if (output_counter >= 33) begin
                    valid_out <= 0;
                    output_active <= 0;  // 33?�럭 ??output_active 비활?�화
                    // output_counter <= 0;  // 카운??리셋 ?�거 - ?�음 ?�력 ?��?                end else begin
                    valid_out <= 0;  // shift값이 준비되지 ?�았?�면 ?��?                end
                // 출력 ?�이?�는 ?�전 �??��?  
                for (d = 0; d < DATA_PER_CLK; d++) begin
                    bfly02_real_out[d] <= bfly02_real_out[d];  // ?�전 �??��?
                    bfly02_imag_out[d] <= bfly02_imag_out[d];  // ?�전 �??��?
                end
            end
        end
    end
  
endmodule
`timescale 1ns / 1ps

module tb_fft;

    // ?�라미터
    parameter N = 512;
    parameter BLK_SIZE = 16;
    parameter CLK_PERIOD = 10;

    // DUT ?�트
    reg clk, rstn;
    reg i_valid;
    reg signed [8:0] din_i [0:BLK_SIZE-1];
    reg signed [8:0] din_q [0:BLK_SIZE-1];
    wire signed [12:0] dout_i [0:15];
    wire signed [12:0] dout_q [0:15];
    wire o_valid;

    // ?�일 ?�들
    integer fp_real, fp_imag, fp_out_real, fp_out_imag, i, j;
    integer num_in, num_out;
    integer output_count;  // 출력 카운??변???�언
    reg signed [15:0] in_real [0:N-1];
    reg signed [15:0] in_imag [0:N-1];
    reg signed [10:0] out_real [0:N-1];
    reg signed [10:0] out_imag [0:N-1];
    
    // 비트 리버???�서�??�배?�된 ?�이??

    // DUT ?�스?�스 (?�트�?비트??맞게 ?�정)
    top dut (
        .clk(clk),
        .rstn(rstn),
        .i_valid(i_valid),
        .din_i(din_i),
        .din_q(din_q),
        .dout_i(dout_i),
        .dout_q(dout_q),
        .o_valid(o_valid)
    );

    // ?�럭 ?�성
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ?�력 벡터 ?�기 - ?�수부?� ?�수부�?별도 ?�일?�서 ?�기
    initial begin
        // ?�수부 ?�일 ?�기
        fp_real = $fopen("cos_fixed_real.txt", "r");
        if (fp_real == 0) begin
            $display("?�수부 ?�일 ?�기 ?�패!");
            $finish;
        end
        for (i = 0; i < N; i = i + 1) begin
            $fscanf(fp_real, "%d\n", in_real[i]);
        end
        $fclose(fp_real);
        
        // ?�수부 ?�일 ?�기
        fp_imag = $fopen("cos_fixed_imag.txt", "r");
        if (fp_imag == 0) begin
            $display("?�수부 ?�일 ?�기 ?�패!");
            $finish;
        end
        for (i = 0; i < N; i = i + 1) begin
            $fscanf(fp_imag, "%d\n", in_imag[i]);
        end
        $fclose(fp_imag);
    end

    // ?��??�이??
    initial begin
        // 출력 ?�일 ?�기
        fp_out_real = $fopen("fft_output_real.txt", "w");
        fp_out_imag = $fopen("fft_output_imag.txt", "w");
        if (fp_out_real == 0 || fp_out_imag == 0) begin
            $display("출력 ?�일 ?�기 ?�패!");
            $finish;
        end
        
        rstn = 0;
        i_valid = 0;
        # (CLK_PERIOD*5);
        rstn = 1;
        # (CLK_PERIOD*2);

        // ?�력 ?�용 (34?�럭 ?�안�?i_valid=1 ?��?)
        num_in = 0;
        num_out = 0;
        i_valid = 1;
        for (i = 0; i < 34; i = i + 1) begin  // ?�확??34?�럭�?
            if (i < N/BLK_SIZE) begin  // ?�이?��? ?�는 ?�안�??�이???�용
                for (j = 0; j < BLK_SIZE; j = j + 1) begin
                    //din_i[j] = in_real[i*BLK_SIZE + (BLK_SIZE-1-j)][8:0];
                    //din_q[j] = in_imag[i*BLK_SIZE + (BLK_SIZE-1-j)][8:0];
                    din_i[j] = in_real[i*BLK_SIZE + j][8:0];
                    din_q[j] = in_imag[i*BLK_SIZE + j][8:0];
                end
            end else begin  // ?�이?��? ?�는 ?�안?� 0?�로 ?�정
                for (j = 0; j < BLK_SIZE; j = j + 1) begin
                    din_i[j] = 0;
                    din_q[j] = 0;
                end
            end
            @(posedge clk);
        end
        i_valid = 0;

        // o_valid ?��???512�?출력 ?�료까�? ?��?
        wait(o_valid == 1);  // �?번째 출력 ?��?
        
        // ?�확??512�??�이?�만 카운?�하??출력
        output_count = 0;
        while (output_count < N) begin  // 512개까지�?
            if (o_valid) begin
                // 16�??�이?��? ?�일???�??(0~15 ?�서?��?
                for (j = 0; j < BLK_SIZE; j = j + 1) begin
                    $fdisplay(fp_out_real, "%d", dout_i[j]);
                    $fdisplay(fp_out_imag, "%d", dout_q[j]);
                end
                $display("Output %0d: dout_i[0]=%d, dout_q[0]=%d", output_count, dout_i[0], dout_q[0]);
                output_count = output_count + BLK_SIZE;  // 16개씩 증�?
            end
            @(posedge clk);
        end
        
        // ?�일 ?�기
        $fclose(fp_out_real);
        $fclose(fp_out_imag);
        
        $display("모든 512�??�이??출력 ?�료! ?�일???�?�됨.");
        
        // ?�럭??�?�????�작?�켜??마�?�??�강 ?��?까�? ?�료
        repeat(5) @(posedge clk);
        
        // $finish;  // ?��??�이??종료 - ?�럭 멈춤
        $stop;      // ?��??�이???�시?��? - ?�럭 계속 ?�작
    end

endmodule
`timescale 1ns / 1ps

// 144비트 ??9비트 × 16�?배열 매크�?(?�력?? - 비트 ?�서 ?�집�?
`define GET_DIN_I(idx) din_i[((15-(idx))+1)*9-1:(15-(idx))*9]
`define GET_DIN_Q(idx) din_q[((15-(idx))+1)*9-1:(15-(idx))*9]

// 208비트 ??13비트 × 16�?배열 매크�?(출력?? - 비트 ?�서 ?�집�?
`define GET_DOUT_I(idx) dout_i[((15-(idx))+1)*13-1:(15-(idx))*13]
`define GET_DOUT_Q(idx) dout_q[((15-(idx))+1)*13-1:(15-(idx))*13]

// ?�정??매크�?
`define SET_DIN_I(idx, val) din_i[((15-(idx))+1)*9-1:(15-(idx))*9] = val
`define SET_DIN_Q(idx, val) din_q[((15-(idx))+1)*9-1:(15-(idx))*9] = val

module tb_fft_synthesized;

    // ?�라미터
    parameter N = 512;
    parameter BLK_SIZE = 16;
    parameter CLK_PERIOD = 10;

    // DUT ?�트 (?�성??모듈??벡터 ?�트??맞춤)
    reg clk, rstn;
    reg i_valid;
    reg [143:0] din_i;  // 144비트 (9비트 × 16�?
    reg [143:0] din_q;  // 144비트 (9비트 × 16�?  
    wire [207:0] dout_i;
    wire [207:0] dout_q;
    wire o_valid;


    // ?�일 ?�들
    integer fp_real, fp_imag, fp_out_real, fp_out_imag, i, j;
    integer output_count;
    reg signed [15:0] in_real [0:N-1];
    reg signed [15:0] in_imag [0:N-1];
    
    // Verdi?�서 ?�형 보기??배열 (매크로로 ?�근)
    wire signed [8:0] din_i_array [15:0];   // 9비트 × 16�?
    wire signed [12:0] dout_i_array [15:0]; // 13비트 × 16�?
    wire signed [8:0] din_q_array [15:0];   // 9비트 × 16�?
    wire signed [12:0] dout_q_array [15:0]; // 13비트 × 16�?
    
    // 배열 ?�결
    genvar k;
    generate
        for (k = 0; k < 16; k = k + 1) begin : array_conn
            assign din_i_array[k] = `GET_DIN_I(k);
            assign din_q_array[k] = `GET_DIN_Q(k);
            assign dout_i_array[k] = `GET_DOUT_I(k);
            assign dout_q_array[k] = `GET_DOUT_Q(k);
        end
    endgenerate
     
    top dut (
        .clk(clk),
        .rstn(rstn),
        .i_valid(i_valid),
        .din_i(din_i),
        .din_q(din_q),
        .dout_i(dout_i),
        .dout_q(dout_q),
        .o_valid(o_valid)
    );

    // ?�럭 ?�성
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ?�력 벡터 ?�기
    initial begin
        // ?�수부 ?�일 ?�기
        fp_real = $fopen("cos_fixed_real.txt", "r");
        if (fp_real == 0) begin
            $display("?�수부 ?�일 ?�기 ?�패!");
            $finish;
        end
        for (i = 0; i < N; i = i + 1) begin
            $fscanf(fp_real, "%d\n", in_real[i]);
        end
        $fclose(fp_real);
        
        // ?�수부 ?�일 ?�기
        fp_imag = $fopen("cos_fixed_imag.txt", "r");
        if (fp_imag == 0) begin
            $display("?�수부 ?�일 ?�기 ?�패!");
            $finish;
        end
        for (i = 0; i < N; i = i + 1) begin
            $fscanf(fp_imag, "%d\n", in_imag[i]);
        end
        $fclose(fp_imag);
    end

    // ?��??�이??
    initial begin
        // 출력 ?�일 ?�기
        fp_out_real = $fopen("fft_synthesized_output_real.txt", "w");
        fp_out_imag = $fopen("fft_synthesized_output_imag.txt", "w");
        if (fp_out_real == 0 || fp_out_imag == 0) begin
            $display("출력 ?�일 ?�기 ?�패!");
            $finish;
        end
        
        // 모든 ?�력 ?�호 초기??
        rstn = 0;
        i_valid = 0;
        din_i = 0;
        din_q = 0;
        # (CLK_PERIOD*5);
        rstn = 1;
        # (CLK_PERIOD*2);

        // ?�력 ?�용 - 배열 ?�덱???�서?��??�??(0??5)
        i_valid = 1;
        for (i = 0; i < N/BLK_SIZE; i = i + 1) begin
            // 16�??�이?��? 144비트 벡터�??�당 (?�덱???�서?��?
            din_i = {in_real[i*BLK_SIZE + 0][8:0], in_real[i*BLK_SIZE + 1][8:0],
                     in_real[i*BLK_SIZE + 2][8:0], in_real[i*BLK_SIZE + 3][8:0],
                     in_real[i*BLK_SIZE + 4][8:0], in_real[i*BLK_SIZE + 5][8:0],
                     in_real[i*BLK_SIZE + 6][8:0], in_real[i*BLK_SIZE + 7][8:0],
                     in_real[i*BLK_SIZE + 8][8:0], in_real[i*BLK_SIZE + 9][8:0],
                     in_real[i*BLK_SIZE + 10][8:0], in_real[i*BLK_SIZE + 11][8:0],
                     in_real[i*BLK_SIZE + 12][8:0], in_real[i*BLK_SIZE + 13][8:0],
                     in_real[i*BLK_SIZE + 14][8:0], in_real[i*BLK_SIZE + 15][8:0]};
            din_q = {in_imag[i*BLK_SIZE + 0][8:0], in_imag[i*BLK_SIZE + 1][8:0],
                     in_imag[i*BLK_SIZE + 2][8:0], in_imag[i*BLK_SIZE + 3][8:0],
                     in_imag[i*BLK_SIZE + 4][8:0], in_imag[i*BLK_SIZE + 5][8:0],
                     in_imag[i*BLK_SIZE + 6][8:0], in_imag[i*BLK_SIZE + 7][8:0],
                     in_imag[i*BLK_SIZE + 8][8:0], in_imag[i*BLK_SIZE + 9][8:0],
                     in_imag[i*BLK_SIZE + 10][8:0], in_imag[i*BLK_SIZE + 11][8:0],
                     in_imag[i*BLK_SIZE + 12][8:0], in_imag[i*BLK_SIZE + 13][8:0],
                     in_imag[i*BLK_SIZE + 14][8:0], in_imag[i*BLK_SIZE + 15][8:0]};
            @(posedge clk);
        end
        // OUTSUM 구간 ?�안??i_valid=1 ?��?
        for (i = 0; i < N/BLK_SIZE; i = i + 1) begin
            @(posedge clk);
        end
        i_valid = 0;

        // o_valid ?��???512�?출력 ?�료까�? ?��?
        wait(o_valid == 1);
        
        // ?�확??512�??�이?�만 카운?�하??출력
        output_count = 0;
        while (output_count < N) begin
            if (o_valid) begin
                // case 문을 ?�용?�여 16개씩 출력 ?�이???�기
                for (j = 0; j < BLK_SIZE; j = j + 1) begin
                    // case 문으�?�??�덱?�별 비트 ?�라?�싱
                    case (j)
                        0: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[12:0]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[12:0]));
                            if (j < 4) begin
                                $display("dout_i[%d] = %d (0x%h)", j, $signed(dout_i[12:0]), dout_i[12:0]);
                                $display("dout_q[%d] = %d (0x%h)", j, $signed(dout_q[12:0]), dout_q[12:0]);
                            end
                        end
                        1: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[25:13]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[25:13]));
                            if (j < 4) begin
                                $display("dout_i[%d] = %d (0x%h)", j, $signed(dout_i[25:13]), dout_i[25:13]);
                                $display("dout_q[%d] = %d (0x%h)", j, $signed(dout_q[25:13]), dout_q[25:13]);
                            end
                        end
                        2: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[38:26]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[38:26]));
                            if (j < 4) begin
                                $display("dout_i[%d] = %d (0x%h)", j, $signed(dout_i[38:26]), dout_i[38:26]);
                                $display("dout_q[%d] = %d (0x%h)", j, $signed(dout_q[38:26]), dout_q[38:26]);
                            end
                        end
                        3: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[51:39]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[51:39]));
                            if (j < 4) begin
                                $display("dout_i[%d] = %d (0x%h)", j, $signed(dout_i[51:39]), dout_i[51:39]);
                                $display("dout_q[%d] = %d (0x%h)", j, $signed(dout_q[51:39]), dout_q[51:39]);
                            end
                        end
                        4: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[64:52]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[64:52]));
                        end
                        5: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[77:65]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[77:65]));
                        end
                        6: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[90:78]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[90:78]));
                        end
                        7: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[103:91]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[103:91]));
                        end
                        8: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[116:104]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[116:104]));
                        end
                        9: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[129:117]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[129:117]));
                        end
                        10: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[142:130]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[142:130]));
                        end
                        11: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[155:143]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[155:143]));
                        end
                        12: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[168:156]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[168:156]));
                        end
                        13: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[181:169]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[181:169]));
                        end
                        14: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[194:182]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[194:182]));
                        end
                        15: begin
                            $fdisplay(fp_out_real, "%d", $signed(dout_i[207:195]));
                            $fdisplay(fp_out_imag, "%d", $signed(dout_q[207:195]));
                        end
                    endcase
                end
                
                $display("Output block %0d: dout_i[0]=%d, dout_q[0]=%d", 
                        output_count/BLK_SIZE, $signed(dout_i[12:0]), $signed(dout_q[12:0]));
                output_count = output_count + BLK_SIZE;
            end
            @(posedge clk);
        end
        
        // ?�일 ?�기
        $fclose(fp_out_real);
        $fclose(fp_out_imag);
        
        $display("?�성??FFT 모듈 ?�스???�료! ?�일???�?�됨.");
        
        // ?�럭??�?�????�작?�켜??마�?�??�강 ?��?까�? ?�료
        repeat(5) @(posedge clk);
        
        $stop;
    end

endmodule
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
    // 중간 ?�호 ?�언
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
    logic signed [13:0] buf2_out_i[15:0], buf2_out_q[15:0];
    logic               buf2_valid;
    // 3?�계 버퍼 출력 ?�호 ?�언
    logic tw3_in_valid;
    logic signed [22:0] tw3_out_i[15:0];
    logic signed [22:0] tw3_out_q[15:0];
    logic tw3_valid;

    // CBFP 모듈 출력 ?�호 ?�언
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
    
    // final_cbfp_scaler??16�?배열
    logic [4:0] final_shift_out_0 [15:0];
    logic [4:0] final_shift_out_1 [15:0];

    logic signed [12:0] reverse_out_i[15:0], reverse_out_q[15:0];
    logic               reverse_valid;


     logic [8:0] final_cycle_idx;
     
    always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) final_cycle_idx <= 0;
    else final_cycle_idx <= final_cycle_idx + 1;  // �??�럭마다 증�? (?�스?�용)
    end

    // final_cbfp_scaler??16�?배열 ?�당
    always_comb begin
        for (int i = 0; i < 16; i++) begin
            final_shift_out_0[i] = w_applied_shift_out_1[i];
            final_shift_out_1[i] = w_applied_shift_out_2[i];
        end
    end

       // 1?�계 버퍼
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

    // 1?�계 ?�위???�터
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

    // 2?�계 버퍼
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

    // 2?�계 ?�위???�터
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

    // 3?�계 버퍼
    stage_buffer #(
        .IN_WIDTH(12), .OUT_WIDTH(14), .NUM_ELEMS(64), .BLK_SIZE(16), .PIPELINE_DEPTH(0), .VALID_DELAY(1)
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
        .IN_WIDTH(14),
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

        


        

    // 최종 출력 ?�결
    assign dout_i = reverse_out_i;
    assign dout_q = reverse_out_q;
    assign o_valid = reverse_valid;

endmodule














`timescale 1ns/1ps

module twidle1_3#(
    parameter IN_WIDTH = 14,
    parameter OUT_WIDTH = 23
)(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [IN_WIDTH-1:0] din_i[15:0],
    input logic signed [IN_WIDTH-1:0] din_q[15:0],
    output logic signed [OUT_WIDTH-1:0] dout_i[15:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[15:0],
    output logic o_valid
);

    wire signed [8:0] factor_re [0:63];
    wire signed [8:0] factor_im [0:63];

    // assign 초기??    assign factor_re[0] = 9'sd128;  assign factor_im[0] = 9'sd0;
    assign factor_re[1] = 9'sd128;  assign factor_im[1] = 9'sd0;
    assign factor_re[2] = 9'sd128;  assign factor_im[2] = 9'sd0;
    assign factor_re[3] = 9'sd128;  assign factor_im[3] = 9'sd0;
    assign factor_re[4] = 9'sd128;  assign factor_im[4] = 9'sd0;
    assign factor_re[5] = 9'sd128;  assign factor_im[5] = 9'sd0;
    assign factor_re[6] = 9'sd128;  assign factor_im[6] = 9'sd0;
    assign factor_re[7] = 9'sd128;  assign factor_im[7] = 9'sd0;
    assign factor_re[8] = 9'sd128;  assign factor_im[8] = 9'sd0;
    assign factor_re[9] = 9'sd118;  assign factor_im[9] = -9'sd49;
    assign factor_re[10] = 9'sd91;  assign factor_im[10] = -9'sd91;
    assign factor_re[11] = 9'sd49;  assign factor_im[11] = -9'sd118;
    assign factor_re[12] = 9'sd0;   assign factor_im[12] = -9'sd128;
    assign factor_re[13] = -9'sd49; assign factor_im[13] = -9'sd118;
    assign factor_re[14] = -9'sd91; assign factor_im[14] = -9'sd91;
    assign factor_re[15] = -9'sd118; assign factor_im[15] = -9'sd49;
    assign factor_re[16] = 9'sd128;  assign factor_im[16] = 9'sd0;
    assign factor_re[17] = 9'sd126;  assign factor_im[17] = -9'sd25;
    assign factor_re[18] = 9'sd118;  assign factor_im[18] = -9'sd49;
    assign factor_re[19] = 9'sd106;  assign factor_im[19] = -9'sd71;
    assign factor_re[20] = 9'sd91;   assign factor_im[20] = -9'sd91;
    assign factor_re[21] = 9'sd71;   assign factor_im[21] = -9'sd106;
    assign factor_re[22] = 9'sd49;   assign factor_im[22] = -9'sd118;
    assign factor_re[23] = 9'sd25;   assign factor_im[23] = -9'sd126;
    assign factor_re[24] = 9'sd128;  assign factor_im[24] = 9'sd0;
    assign factor_re[25] = 9'sd106;  assign factor_im[25] = -9'sd71;
    assign factor_re[26] = 9'sd49;   assign factor_im[26] = -9'sd118;
    assign factor_re[27] = -9'sd25;  assign factor_im[27] = -9'sd126;
    assign factor_re[28] = -9'sd91;  assign factor_im[28] = -9'sd91;
    assign factor_re[29] = -9'sd126; assign factor_im[29] = -9'sd25;
    assign factor_re[30] = -9'sd118; assign factor_im[30] = 9'sd49;
    assign factor_re[31] = -9'sd71;  assign factor_im[31] = 9'sd106;
    assign factor_re[32] = 9'sd128;  assign factor_im[32] = 9'sd0;
    assign factor_re[33] = 9'sd127;  assign factor_im[33] = -9'sd13;
    assign factor_re[34] = 9'sd126;  assign factor_im[34] = -9'sd25;
    assign factor_re[35] = 9'sd122;  assign factor_im[35] = -9'sd37;
    assign factor_re[36] = 9'sd118;  assign factor_im[36] = -9'sd49;
    assign factor_re[37] = 9'sd113;  assign factor_im[37] = -9'sd60;
    assign factor_re[38] = 9'sd106;  assign factor_im[38] = -9'sd71;
    assign factor_re[39] = 9'sd99;   assign factor_im[39] = -9'sd81;
    assign factor_re[40] = 9'sd128;  assign factor_im[40] = 9'sd0;
    assign factor_re[41] = 9'sd113;  assign factor_im[41] = -9'sd60;
    assign factor_re[42] = 9'sd71;   assign factor_im[42] = -9'sd106;
    assign factor_re[43] = 9'sd13;   assign factor_im[43] = -9'sd127;
    assign factor_re[44] = -9'sd49;  assign factor_im[44] = -9'sd118;
    assign factor_re[45] = -9'sd99;  assign factor_im[45] = -9'sd81;
    assign factor_re[46] = -9'sd126; assign factor_im[46] = -9'sd25;
    assign factor_re[47] = -9'sd122; assign factor_im[47] = 9'sd37;
    assign factor_re[48] = 9'sd128;  assign factor_im[48] = 9'sd0;
    assign factor_re[49] = 9'sd122;  assign factor_im[49] = -9'sd37;
    assign factor_re[50] = 9'sd106;  assign factor_im[50] = -9'sd71;
    assign factor_re[51] = 9'sd81;   assign factor_im[51] = -9'sd99;
    assign factor_re[52] = 9'sd49;   assign factor_im[52] = -9'sd118;
    assign factor_re[53] = 9'sd13;   assign factor_im[53] = -9'sd127;
    assign factor_re[54] = -9'sd25;  assign factor_im[54] = -9'sd126;
    assign factor_re[55] = -9'sd60;  assign factor_im[55] = -9'sd113;
    assign factor_re[56] = 9'sd128;  assign factor_im[56] = 9'sd0;
    assign factor_re[57] = 9'sd99;   assign factor_im[57] = -9'sd81;
    assign factor_re[58] = 9'sd25;   assign factor_im[58] = -9'sd126;
    assign factor_re[59] = -9'sd60;  assign factor_im[59] = -9'sd113;
    assign factor_re[60] = -9'sd118; assign factor_im[60] = -9'sd49;
    assign factor_re[61] = -9'sd122; assign factor_im[61] = 9'sd37;
    assign factor_re[62] = -9'sd71;  assign factor_im[62] = 9'sd106;
    assign factor_re[63] = 9'sd13;   assign factor_im[63] = 9'sd127;

    
    // ?��? 카운?? 0~511 (64개씩 ?�환)
    reg [8:0] data_idx;
    integer i;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            data_idx <= 0;
            for (i = 0; i < 16; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
            o_valid <= 0;
        end else begin
            if (i_valid) begin
                for (i = 0; i < 16; i++) begin
                    // 64개씩 ?�환?�는 ?�덱???�용
                    dout_i[i] <= din_i[i] * factor_re[(data_idx + i) % 64] - din_q[i] * factor_im[(data_idx + i) % 64];
                    dout_q[i] <= din_i[i] * factor_im[(data_idx + i) % 64] + din_q[i] * factor_re[(data_idx + i) % 64];
                end
                
                if (data_idx >= 512 - 16) begin  // 마�?�?블록 처리 ??                    data_idx <= 0;  // 리셋
                end else begin
                    data_idx <= data_idx + 16;
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule


module twidle0_3 #(
    parameter IN_WIDTH = 14,
    parameter OUT_WIDTH = 23
)(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [IN_WIDTH-1:0] din_i[15:0],
    input logic signed [IN_WIDTH-1:0] din_q[15:0],
    output logic signed [OUT_WIDTH-1:0] dout_i[15:0],
    output logic signed [OUT_WIDTH-1:0] dout_q[15:0],
    output logic o_valid
);

    wire signed [8:0] factor_re [0:511];
    wire signed [8:0] factor_im [0:511];

    
    assign factor_re[0] = 9'sd128; assign factor_im[0] = 9'sd0;
    assign factor_re[1] = 9'sd128; assign factor_im[1] = 9'sd0;
    assign factor_re[2] = 9'sd128; assign factor_im[2] = 9'sd0;
    assign factor_re[3] = 9'sd128; assign factor_im[3] = 9'sd0;
    assign factor_re[4] = 9'sd128; assign factor_im[4] = 9'sd0;
    assign factor_re[5] = 9'sd128; assign factor_im[5] = 9'sd0;
    assign factor_re[6] = 9'sd128; assign factor_im[6] = 9'sd0;
    assign factor_re[7] = 9'sd128; assign factor_im[7] = 9'sd0;
    assign factor_re[8] = 9'sd128; assign factor_im[8] = 9'sd0;
    assign factor_re[9] = 9'sd128; assign factor_im[9] = 9'sd0;
    assign factor_re[10] = 9'sd128; assign factor_im[10] = 9'sd0;
    assign factor_re[11] = 9'sd128; assign factor_im[11] = 9'sd0;
    assign factor_re[12] = 9'sd128; assign factor_im[12] = 9'sd0;
    assign factor_re[13] = 9'sd128; assign factor_im[13] = 9'sd0;
    assign factor_re[14] = 9'sd128; assign factor_im[14] = 9'sd0;
    assign factor_re[15] = 9'sd128; assign factor_im[15] = 9'sd0;
    assign factor_re[16] = 9'sd128; assign factor_im[16] = 9'sd0;
    assign factor_re[17] = 9'sd128; assign factor_im[17] = 9'sd0;
    assign factor_re[18] = 9'sd128; assign factor_im[18] = 9'sd0;
    assign factor_re[19] = 9'sd128; assign factor_im[19] = 9'sd0;
    assign factor_re[20] = 9'sd128; assign factor_im[20] = 9'sd0;
    assign factor_re[21] = 9'sd128; assign factor_im[21] = 9'sd0;
    assign factor_re[22] = 9'sd128; assign factor_im[22] = 9'sd0;
    assign factor_re[23] = 9'sd128; assign factor_im[23] = 9'sd0;
    assign factor_re[24] = 9'sd128; assign factor_im[24] = 9'sd0;
    assign factor_re[25] = 9'sd128; assign factor_im[25] = 9'sd0;
    assign factor_re[26] = 9'sd128; assign factor_im[26] = 9'sd0;
    assign factor_re[27] = 9'sd128; assign factor_im[27] = 9'sd0;
    assign factor_re[28] = 9'sd128; assign factor_im[28] = 9'sd0;
    assign factor_re[29] = 9'sd128; assign factor_im[29] = 9'sd0;
    assign factor_re[30] = 9'sd128; assign factor_im[30] = 9'sd0;
    assign factor_re[31] = 9'sd128; assign factor_im[31] = 9'sd0;
    assign factor_re[32] = 9'sd128; assign factor_im[32] = 9'sd0;
    assign factor_re[33] = 9'sd128; assign factor_im[33] = 9'sd0;
    assign factor_re[34] = 9'sd128; assign factor_im[34] = 9'sd0;
    assign factor_re[35] = 9'sd128; assign factor_im[35] = 9'sd0;
    assign factor_re[36] = 9'sd128; assign factor_im[36] = 9'sd0;
    assign factor_re[37] = 9'sd128; assign factor_im[37] = 9'sd0;
    assign factor_re[38] = 9'sd128; assign factor_im[38] = 9'sd0;
    assign factor_re[39] = 9'sd128; assign factor_im[39] = 9'sd0;
    assign factor_re[40] = 9'sd128; assign factor_im[40] = 9'sd0;
    assign factor_re[41] = 9'sd128; assign factor_im[41] = 9'sd0;
    assign factor_re[42] = 9'sd128; assign factor_im[42] = 9'sd0;
    assign factor_re[43] = 9'sd128; assign factor_im[43] = 9'sd0;
    assign factor_re[44] = 9'sd128; assign factor_im[44] = 9'sd0;
    assign factor_re[45] = 9'sd128; assign factor_im[45] = 9'sd0;
    assign factor_re[46] = 9'sd128; assign factor_im[46] = 9'sd0;
    assign factor_re[47] = 9'sd128; assign factor_im[47] = 9'sd0;
    assign factor_re[48] = 9'sd128; assign factor_im[48] = 9'sd0;
    assign factor_re[49] = 9'sd128; assign factor_im[49] = 9'sd0;
    assign factor_re[50] = 9'sd128; assign factor_im[50] = 9'sd0;
    assign factor_re[51] = 9'sd128; assign factor_im[51] = 9'sd0;
    assign factor_re[52] = 9'sd128; assign factor_im[52] = 9'sd0;
    assign factor_re[53] = 9'sd128; assign factor_im[53] = 9'sd0;
    assign factor_re[54] = 9'sd128; assign factor_im[54] = 9'sd0;
    assign factor_re[55] = 9'sd128; assign factor_im[55] = 9'sd0;
    assign factor_re[56] = 9'sd128; assign factor_im[56] = 9'sd0;
    assign factor_re[57] = 9'sd128; assign factor_im[57] = 9'sd0;
    assign factor_re[58] = 9'sd128; assign factor_im[58] = 9'sd0;
    assign factor_re[59] = 9'sd128; assign factor_im[59] = 9'sd0;
    assign factor_re[60] = 9'sd128; assign factor_im[60] = 9'sd0;
    assign factor_re[61] = 9'sd128; assign factor_im[61] = 9'sd0;
    assign factor_re[62] = 9'sd128; assign factor_im[62] = 9'sd0;
    assign factor_re[63] = 9'sd128; assign factor_im[63] = 9'sd0;
    assign factor_re[64] = 9'sd128; assign factor_im[64] = 9'sd0;
    assign factor_re[65] = 9'sd128; assign factor_im[65] = -9'sd6;
    assign factor_re[66] = 9'sd127; assign factor_im[66] = -9'sd13;
    assign factor_re[67] = 9'sd127; assign factor_im[67] = -9'sd19;
    assign factor_re[68] = 9'sd126; assign factor_im[68] = -9'sd25;
    assign factor_re[69] = 9'sd124; assign factor_im[69] = -9'sd31;
    assign factor_re[70] = 9'sd122; assign factor_im[70] = -9'sd37;
    assign factor_re[71] = 9'sd121; assign factor_im[71] = -9'sd43;
    assign factor_re[72] = 9'sd118; assign factor_im[72] = -9'sd49;
    assign factor_re[73] = 9'sd116; assign factor_im[73] = -9'sd55;
    assign factor_re[74] = 9'sd113; assign factor_im[74] = -9'sd60;
    assign factor_re[75] = 9'sd110; assign factor_im[75] = -9'sd66;
    assign factor_re[76] = 9'sd106; assign factor_im[76] = -9'sd71;
    assign factor_re[77] = 9'sd103; assign factor_im[77] = -9'sd76;
    assign factor_re[78] = 9'sd99; assign factor_im[78] = -9'sd81;
    assign factor_re[79] = 9'sd95; assign factor_im[79] = -9'sd86;
    assign factor_re[80] = 9'sd91; assign factor_im[80] = -9'sd91;
    assign factor_re[81] = 9'sd86; assign factor_im[81] = -9'sd95;
    assign factor_re[82] = 9'sd81; assign factor_im[82] = -9'sd99;
    assign factor_re[83] = 9'sd76; assign factor_im[83] = -9'sd103;
    assign factor_re[84] = 9'sd71; assign factor_im[84] = -9'sd106;
    assign factor_re[85] = 9'sd66; assign factor_im[85] = -9'sd110;
    assign factor_re[86] = 9'sd60; assign factor_im[86] = -9'sd113;
    assign factor_re[87] = 9'sd55; assign factor_im[87] = -9'sd116;
    assign factor_re[88] = 9'sd49; assign factor_im[88] = -9'sd118;
    assign factor_re[89] = 9'sd43; assign factor_im[89] = -9'sd121;
    assign factor_re[90] = 9'sd37; assign factor_im[90] = -9'sd122;
    assign factor_re[91] = 9'sd31; assign factor_im[91] = -9'sd124;
    assign factor_re[92] = 9'sd25; assign factor_im[92] = -9'sd126;
    assign factor_re[93] = 9'sd19; assign factor_im[93] = -9'sd127;
    assign factor_re[94] = 9'sd13; assign factor_im[94] = -9'sd127;
    assign factor_re[95] = 9'sd6; assign factor_im[95] = -9'sd128;
    assign factor_re[96] = 9'sd0; assign factor_im[96] = -9'sd128;
    assign factor_re[97] = -9'sd6; assign factor_im[97] = -9'sd128;
    assign factor_re[98] = -9'sd13; assign factor_im[98] = -9'sd127;
    assign factor_re[99] = -9'sd19; assign factor_im[99] = -9'sd127;
    assign factor_re[100] = -9'sd25; assign factor_im[100] = -9'sd126;
    assign factor_re[101] = -9'sd31; assign factor_im[101] = -9'sd124;
    assign factor_re[102] = -9'sd37; assign factor_im[102] = -9'sd122;
    assign factor_re[103] = -9'sd43; assign factor_im[103] = -9'sd121;
    assign factor_re[104] = -9'sd49; assign factor_im[104] = -9'sd118;
    assign factor_re[105] = -9'sd55; assign factor_im[105] = -9'sd116;
    assign factor_re[106] = -9'sd60; assign factor_im[106] = -9'sd113;
    assign factor_re[107] = -9'sd66; assign factor_im[107] = -9'sd110;
    assign factor_re[108] = -9'sd71; assign factor_im[108] = -9'sd106;
    assign factor_re[109] = -9'sd76; assign factor_im[109] = -9'sd103;
    assign factor_re[110] = -9'sd81; assign factor_im[110] = -9'sd99;
    assign factor_re[111] = -9'sd86; assign factor_im[111] = -9'sd95;
    assign factor_re[112] = -9'sd91; assign factor_im[112] = -9'sd91;
    assign factor_re[113] = -9'sd95; assign factor_im[113] = -9'sd86;
    assign factor_re[114] = -9'sd99; assign factor_im[114] = -9'sd81;
    assign factor_re[115] = -9'sd103; assign factor_im[115] = -9'sd76;
    assign factor_re[116] = -9'sd106; assign factor_im[116] = -9'sd71;
    assign factor_re[117] = -9'sd110; assign factor_im[117] = -9'sd66;
    assign factor_re[118] = -9'sd113; assign factor_im[118] = -9'sd60;
    assign factor_re[119] = -9'sd116; assign factor_im[119] = -9'sd55;
    assign factor_re[120] = -9'sd118; assign factor_im[120] = -9'sd49;
    assign factor_re[121] = -9'sd121; assign factor_im[121] = -9'sd43;
    assign factor_re[122] = -9'sd122; assign factor_im[122] = -9'sd37;
    assign factor_re[123] = -9'sd124; assign factor_im[123] = -9'sd31;
    assign factor_re[124] = -9'sd126; assign factor_im[124] = -9'sd25;
    assign factor_re[125] = -9'sd127; assign factor_im[125] = -9'sd19;
    assign factor_re[126] = -9'sd127; assign factor_im[126] = -9'sd13;
    assign factor_re[127] = -9'sd128; assign factor_im[127] = -9'sd6;
    assign factor_re[128] = 9'sd128; assign factor_im[128] = 9'sd0;
    assign factor_re[129] = 9'sd128; assign factor_im[129] = -9'sd3;
    assign factor_re[130] = 9'sd128; assign factor_im[130] = -9'sd6;
    assign factor_re[131] = 9'sd128; assign factor_im[131] = -9'sd9;
    assign factor_re[132] = 9'sd127; assign factor_im[132] = -9'sd13;
    assign factor_re[133] = 9'sd127; assign factor_im[133] = -9'sd16;
    assign factor_re[134] = 9'sd127; assign factor_im[134] = -9'sd19;
    assign factor_re[135] = 9'sd126; assign factor_im[135] = -9'sd22;
    assign factor_re[136] = 9'sd126; assign factor_im[136] = -9'sd25;
    assign factor_re[137] = 9'sd125; assign factor_im[137] = -9'sd28;
    assign factor_re[138] = 9'sd124; assign factor_im[138] = -9'sd31;
    assign factor_re[139] = 9'sd123; assign factor_im[139] = -9'sd34;
    assign factor_re[140] = 9'sd122; assign factor_im[140] = -9'sd37;
    assign factor_re[141] = 9'sd122; assign factor_im[141] = -9'sd40;
    assign factor_re[142] = 9'sd121; assign factor_im[142] = -9'sd43;
    assign factor_re[143] = 9'sd119; assign factor_im[143] = -9'sd46;
    assign factor_re[144] = 9'sd118; assign factor_im[144] = -9'sd49;
    assign factor_re[145] = 9'sd117; assign factor_im[145] = -9'sd52;
    assign factor_re[146] = 9'sd116; assign factor_im[146] = -9'sd55;
    assign factor_re[147] = 9'sd114; assign factor_im[147] = -9'sd58;
    assign factor_re[148] = 9'sd113; assign factor_im[148] = -9'sd60;
    assign factor_re[149] = 9'sd111; assign factor_im[149] = -9'sd63;
    assign factor_re[150] = 9'sd110; assign factor_im[150] = -9'sd66;
    assign factor_re[151] = 9'sd108; assign factor_im[151] = -9'sd68;
    assign factor_re[152] = 9'sd106; assign factor_im[152] = -9'sd71;
    assign factor_re[153] = 9'sd105; assign factor_im[153] = -9'sd74;
    assign factor_re[154] = 9'sd103; assign factor_im[154] = -9'sd76;
    assign factor_re[155] = 9'sd101; assign factor_im[155] = -9'sd79;
    assign factor_re[156] = 9'sd99; assign factor_im[156] = -9'sd81;
    assign factor_re[157] = 9'sd97; assign factor_im[157] = -9'sd84;
    assign factor_re[158] = 9'sd95; assign factor_im[158] = -9'sd86;
    assign factor_re[159] = 9'sd93; assign factor_im[159] = -9'sd88;
    assign factor_re[160] = 9'sd91; assign factor_im[160] = -9'sd91;
    assign factor_re[161] = 9'sd88; assign factor_im[161] = -9'sd93;
    assign factor_re[162] = 9'sd86; assign factor_im[162] = -9'sd95;
    assign factor_re[163] = 9'sd84; assign factor_im[163] = -9'sd97;
    assign factor_re[164] = 9'sd81; assign factor_im[164] = -9'sd99;
    assign factor_re[165] = 9'sd79; assign factor_im[165] = -9'sd101;
    assign factor_re[166] = 9'sd76; assign factor_im[166] = -9'sd103;
    assign factor_re[167] = 9'sd74; assign factor_im[167] = -9'sd105;
    assign factor_re[168] = 9'sd71; assign factor_im[168] = -9'sd106;
    assign factor_re[169] = 9'sd68; assign factor_im[169] = -9'sd108;
    assign factor_re[170] = 9'sd66; assign factor_im[170] = -9'sd110;
    assign factor_re[171] = 9'sd63; assign factor_im[171] = -9'sd111;
    assign factor_re[172] = 9'sd60; assign factor_im[172] = -9'sd113;
    assign factor_re[173] = 9'sd58; assign factor_im[173] = -9'sd114;
    assign factor_re[174] = 9'sd55; assign factor_im[174] = -9'sd116;
    assign factor_re[175] = 9'sd52; assign factor_im[175] = -9'sd117;
    assign factor_re[176] = 9'sd49; assign factor_im[176] = -9'sd118;
    assign factor_re[177] = 9'sd46; assign factor_im[177] = -9'sd119;
    assign factor_re[178] = 9'sd43; assign factor_im[178] = -9'sd121;
    assign factor_re[179] = 9'sd40; assign factor_im[179] = -9'sd122;
    assign factor_re[180] = 9'sd37; assign factor_im[180] = -9'sd122;
    assign factor_re[181] = 9'sd34; assign factor_im[181] = -9'sd123;
    assign factor_re[182] = 9'sd31; assign factor_im[182] = -9'sd124;
    assign factor_re[183] = 9'sd28; assign factor_im[183] = -9'sd125;
    assign factor_re[184] = 9'sd25; assign factor_im[184] = -9'sd126;
    assign factor_re[185] = 9'sd22; assign factor_im[185] = -9'sd126;
    assign factor_re[186] = 9'sd19; assign factor_im[186] = -9'sd127;
    assign factor_re[187] = 9'sd16; assign factor_im[187] = -9'sd127;
    assign factor_re[188] = 9'sd13; assign factor_im[188] = -9'sd127;
    assign factor_re[189] = 9'sd9; assign factor_im[189] = -9'sd128;
    assign factor_re[190] = 9'sd6; assign factor_im[190] = -9'sd128;
    assign factor_re[191] = 9'sd3; assign factor_im[191] = -9'sd128;
    assign factor_re[192] = 9'sd128; assign factor_im[192] = 9'sd0;
    assign factor_re[193] = 9'sd128; assign factor_im[193] = -9'sd9;
    assign factor_re[194] = 9'sd127; assign factor_im[194] = -9'sd19;
    assign factor_re[195] = 9'sd125; assign factor_im[195] = -9'sd28;
    assign factor_re[196] = 9'sd122; assign factor_im[196] = -9'sd37;
    assign factor_re[197] = 9'sd119; assign factor_im[197] = -9'sd46;
    assign factor_re[198] = 9'sd116; assign factor_im[198] = -9'sd55;
    assign factor_re[199] = 9'sd111; assign factor_im[199] = -9'sd63;
    assign factor_re[200] = 9'sd106; assign factor_im[200] = -9'sd71;
    assign factor_re[201] = 9'sd101; assign factor_im[201] = -9'sd79;
    assign factor_re[202] = 9'sd95; assign factor_im[202] = -9'sd86;
    assign factor_re[203] = 9'sd88; assign factor_im[203] = -9'sd93;
    assign factor_re[204] = 9'sd81; assign factor_im[204] = -9'sd99;
    assign factor_re[205] = 9'sd74; assign factor_im[205] = -9'sd105;
    assign factor_re[206] = 9'sd66; assign factor_im[206] = -9'sd110;
    assign factor_re[207] = 9'sd58; assign factor_im[207] = -9'sd114;
    assign factor_re[208] = 9'sd49; assign factor_im[208] = -9'sd118;
    assign factor_re[209] = 9'sd40; assign factor_im[209] = -9'sd122;
    assign factor_re[210] = 9'sd31; assign factor_im[210] = -9'sd124;
    assign factor_re[211] = 9'sd22; assign factor_im[211] = -9'sd126;
    assign factor_re[212] = 9'sd13; assign factor_im[212] = -9'sd127;
    assign factor_re[213] = 9'sd3; assign factor_im[213] = -9'sd128;
    assign factor_re[214] = -9'sd6; assign factor_im[214] = -9'sd128;
    assign factor_re[215] = -9'sd16; assign factor_im[215] = -9'sd127;
    assign factor_re[216] = -9'sd25; assign factor_im[216] = -9'sd126;
    assign factor_re[217] = -9'sd34; assign factor_im[217] = -9'sd123;
    assign factor_re[218] = -9'sd43; assign factor_im[218] = -9'sd121;
    assign factor_re[219] = -9'sd52; assign factor_im[219] = -9'sd117;
    assign factor_re[220] = -9'sd60; assign factor_im[220] = -9'sd113;
    assign factor_re[221] = -9'sd68; assign factor_im[221] = -9'sd108;
    assign factor_re[222] = -9'sd76; assign factor_im[222] = -9'sd103;
    assign factor_re[223] = -9'sd84; assign factor_im[223] = -9'sd97;
    assign factor_re[224] = -9'sd91; assign factor_im[224] = -9'sd91;
    assign factor_re[225] = -9'sd97; assign factor_im[225] = -9'sd84;
    assign factor_re[226] = -9'sd103; assign factor_im[226] = -9'sd76;
    assign factor_re[227] = -9'sd108; assign factor_im[227] = -9'sd68;
    assign factor_re[228] = -9'sd113; assign factor_im[228] = -9'sd60;
    assign factor_re[229] = -9'sd117; assign factor_im[229] = -9'sd52;
    assign factor_re[230] = -9'sd121; assign factor_im[230] = -9'sd43;
    assign factor_re[231] = -9'sd123; assign factor_im[231] = -9'sd34;
    assign factor_re[232] = -9'sd126; assign factor_im[232] = -9'sd25;
    assign factor_re[233] = -9'sd127; assign factor_im[233] = -9'sd16;
    assign factor_re[234] = -9'sd128; assign factor_im[234] = -9'sd6;
    assign factor_re[235] = -9'sd128; assign factor_im[235] = 9'sd3;
    assign factor_re[236] = -9'sd127; assign factor_im[236] = 9'sd13;
    assign factor_re[237] = -9'sd126; assign factor_im[237] = 9'sd22;
    assign factor_re[238] = -9'sd124; assign factor_im[238] = 9'sd31;
    assign factor_re[239] = -9'sd122; assign factor_im[239] = 9'sd40;
    assign factor_re[240] = -9'sd118; assign factor_im[240] = 9'sd49;
    assign factor_re[241] = -9'sd114; assign factor_im[241] = 9'sd58;
    assign factor_re[242] = -9'sd110; assign factor_im[242] = 9'sd66;
    assign factor_re[243] = -9'sd105; assign factor_im[243] = 9'sd74;
    assign factor_re[244] = -9'sd99; assign factor_im[244] = 9'sd81;
    assign factor_re[245] = -9'sd93; assign factor_im[245] = 9'sd88;
    assign factor_re[246] = -9'sd86; assign factor_im[246] = 9'sd95;
    assign factor_re[247] = -9'sd79; assign factor_im[247] = 9'sd101;
    assign factor_re[248] = -9'sd71; assign factor_im[248] = 9'sd106;
    assign factor_re[249] = -9'sd63; assign factor_im[249] = 9'sd111;
    assign factor_re[250] = -9'sd55; assign factor_im[250] = 9'sd116;
    assign factor_re[251] = -9'sd46; assign factor_im[251] = 9'sd119;
    assign factor_re[252] = -9'sd37; assign factor_im[252] = 9'sd122;
    assign factor_re[253] = -9'sd28; assign factor_im[253] = 9'sd125;
    assign factor_re[254] = -9'sd19; assign factor_im[254] = 9'sd127;
    assign factor_re[255] = -9'sd9; assign factor_im[255] = 9'sd128;
    assign factor_re[256] = 9'sd128; assign factor_im[256] = 9'sd0;
    assign factor_re[257] = 9'sd128; assign factor_im[257] = -9'sd2;
    assign factor_re[258] = 9'sd128; assign factor_im[258] = -9'sd3;
    assign factor_re[259] = 9'sd128; assign factor_im[259] = -9'sd5;
    assign factor_re[260] = 9'sd128; assign factor_im[260] = -9'sd6;
    assign factor_re[261] = 9'sd128; assign factor_im[261] = -9'sd8;
    assign factor_re[262] = 9'sd128; assign factor_im[262] = -9'sd9;
    assign factor_re[263] = 9'sd128; assign factor_im[263] = -9'sd11;
    assign factor_re[264] = 9'sd127; assign factor_im[264] = -9'sd13;
    assign factor_re[265] = 9'sd127; assign factor_im[265] = -9'sd14;
    assign factor_re[266] = 9'sd127; assign factor_im[266] = -9'sd16;
    assign factor_re[267] = 9'sd127; assign factor_im[267] = -9'sd17;
    assign factor_re[268] = 9'sd127; assign factor_im[268] = -9'sd19;
    assign factor_re[269] = 9'sd126; assign factor_im[269] = -9'sd20;
    assign factor_re[270] = 9'sd126; assign factor_im[270] = -9'sd22;
    assign factor_re[271] = 9'sd126; assign factor_im[271] = -9'sd23;
    assign factor_re[272] = 9'sd126; assign factor_im[272] = -9'sd25;
    assign factor_re[273] = 9'sd125; assign factor_im[273] = -9'sd27;
    assign factor_re[274] = 9'sd125; assign factor_im[274] = -9'sd28;
    assign factor_re[275] = 9'sd125; assign factor_im[275] = -9'sd30;
    assign factor_re[276] = 9'sd124; assign factor_im[276] = -9'sd31;
    assign factor_re[277] = 9'sd124; assign factor_im[277] = -9'sd33;
    assign factor_re[278] = 9'sd123; assign factor_im[278] = -9'sd34;
    assign factor_re[279] = 9'sd123; assign factor_im[279] = -9'sd36;
    assign factor_re[280] = 9'sd122; assign factor_im[280] = -9'sd37;
    assign factor_re[281] = 9'sd122; assign factor_im[281] = -9'sd39;
    assign factor_re[282] = 9'sd122; assign factor_im[282] = -9'sd40;
    assign factor_re[283] = 9'sd121; assign factor_im[283] = -9'sd42;
    assign factor_re[284] = 9'sd121; assign factor_im[284] = -9'sd43;
    assign factor_re[285] = 9'sd120; assign factor_im[285] = -9'sd45;
    assign factor_re[286] = 9'sd119; assign factor_im[286] = -9'sd46;
    assign factor_re[287] = 9'sd119; assign factor_im[287] = -9'sd48;
    assign factor_re[288] = 9'sd118; assign factor_im[288] = -9'sd49;
    assign factor_re[289] = 9'sd118; assign factor_im[289] = -9'sd50;
    assign factor_re[290] = 9'sd117; assign factor_im[290] = -9'sd52;
    assign factor_re[291] = 9'sd116; assign factor_im[291] = -9'sd53;
    assign factor_re[292] = 9'sd116; assign factor_im[292] = -9'sd55;
    assign factor_re[293] = 9'sd115; assign factor_im[293] = -9'sd56;
    assign factor_re[294] = 9'sd114; assign factor_im[294] = -9'sd58;
    assign factor_re[295] = 9'sd114; assign factor_im[295] = -9'sd59;
    assign factor_re[296] = 9'sd113; assign factor_im[296] = -9'sd60;
    assign factor_re[297] = 9'sd112; assign factor_im[297] = -9'sd62;
    assign factor_re[298] = 9'sd111; assign factor_im[298] = -9'sd63;
    assign factor_re[299] = 9'sd111; assign factor_im[299] = -9'sd64;
    assign factor_re[300] = 9'sd110; assign factor_im[300] = -9'sd66;
    assign factor_re[301] = 9'sd109; assign factor_im[301] = -9'sd67;
    assign factor_re[302] = 9'sd108; assign factor_im[302] = -9'sd68;
    assign factor_re[303] = 9'sd107; assign factor_im[303] = -9'sd70;
    assign factor_re[304] = 9'sd106; assign factor_im[304] = -9'sd71;
    assign factor_re[305] = 9'sd106; assign factor_im[305] = -9'sd72;
    assign factor_re[306] = 9'sd105; assign factor_im[306] = -9'sd74;
    assign factor_re[307] = 9'sd104; assign factor_im[307] = -9'sd75;
    assign factor_re[308] = 9'sd103; assign factor_im[308] = -9'sd76;
    assign factor_re[309] = 9'sd102; assign factor_im[309] = -9'sd78;
    assign factor_re[310] = 9'sd101; assign factor_im[310] = -9'sd79;
    assign factor_re[311] = 9'sd100; assign factor_im[311] = -9'sd80;
    assign factor_re[312] = 9'sd99; assign factor_im[312] = -9'sd81;
    assign factor_re[313] = 9'sd98; assign factor_im[313] = -9'sd82;
    assign factor_re[314] = 9'sd97; assign factor_im[314] = -9'sd84;
    assign factor_re[315] = 9'sd96; assign factor_im[315] = -9'sd85;
    assign factor_re[316] = 9'sd95; assign factor_im[316] = -9'sd86;
    assign factor_re[317] = 9'sd94; assign factor_im[317] = -9'sd87;
    assign factor_re[318] = 9'sd93; assign factor_im[318] = -9'sd88;
    assign factor_re[319] = 9'sd92; assign factor_im[319] = -9'sd89;
    assign factor_re[320] = 9'sd128; assign factor_im[320] = 9'sd0;
    assign factor_re[321] = 9'sd128; assign factor_im[321] = -9'sd8;
    assign factor_re[322] = 9'sd127; assign factor_im[322] = -9'sd16;
    assign factor_re[323] = 9'sd126; assign factor_im[323] = -9'sd23;
    assign factor_re[324] = 9'sd124; assign factor_im[324] = -9'sd31;
    assign factor_re[325] = 9'sd122; assign factor_im[325] = -9'sd39;
    assign factor_re[326] = 9'sd119; assign factor_im[326] = -9'sd46;
    assign factor_re[327] = 9'sd116; assign factor_im[327] = -9'sd53;
    assign factor_re[328] = 9'sd113; assign factor_im[328] = -9'sd60;
    assign factor_re[329] = 9'sd109; assign factor_im[329] = -9'sd67;
    assign factor_re[330] = 9'sd105; assign factor_im[330] = -9'sd74;
    assign factor_re[331] = 9'sd100; assign factor_im[331] = -9'sd80;
    assign factor_re[332] = 9'sd95; assign factor_im[332] = -9'sd86;
    assign factor_re[333] = 9'sd89; assign factor_im[333] = -9'sd92;
    assign factor_re[334] = 9'sd84; assign factor_im[334] = -9'sd97;
    assign factor_re[335] = 9'sd78; assign factor_im[335] = -9'sd102;
    assign factor_re[336] = 9'sd71; assign factor_im[336] = -9'sd106;
    assign factor_re[337] = 9'sd64; assign factor_im[337] = -9'sd111;
    assign factor_re[338] = 9'sd58; assign factor_im[338] = -9'sd114;
    assign factor_re[339] = 9'sd50; assign factor_im[339] = -9'sd118;
    assign factor_re[340] = 9'sd43; assign factor_im[340] = -9'sd121;
    assign factor_re[341] = 9'sd36; assign factor_im[341] = -9'sd123;
    assign factor_re[342] = 9'sd28; assign factor_im[342] = -9'sd125;
    assign factor_re[343] = 9'sd20; assign factor_im[343] = -9'sd126;
    assign factor_re[344] = 9'sd13; assign factor_im[344] = -9'sd127;
    assign factor_re[345] = 9'sd5; assign factor_im[345] = -9'sd128;
    assign factor_re[346] = -9'sd3; assign factor_im[346] = -9'sd128;
    assign factor_re[347] = -9'sd11; assign factor_im[347] = -9'sd128;
    assign factor_re[348] = -9'sd19; assign factor_im[348] = -9'sd127;
    assign factor_re[349] = -9'sd27; assign factor_im[349] = -9'sd125;
    assign factor_re[350] = -9'sd34; assign factor_im[350] = -9'sd123;
    assign factor_re[351] = -9'sd42; assign factor_im[351] = -9'sd121;
    assign factor_re[352] = -9'sd49; assign factor_im[352] = -9'sd118;
    assign factor_re[353] = -9'sd56; assign factor_im[353] = -9'sd115;
    assign factor_re[354] = -9'sd63; assign factor_im[354] = -9'sd111;
    assign factor_re[355] = -9'sd70; assign factor_im[355] = -9'sd107;
    assign factor_re[356] = -9'sd76; assign factor_im[356] = -9'sd103;
    assign factor_re[357] = -9'sd82; assign factor_im[357] = -9'sd98;
    assign factor_re[358] = -9'sd88; assign factor_im[358] = -9'sd93;
    assign factor_re[359] = -9'sd94; assign factor_im[359] = -9'sd87;
    assign factor_re[360] = -9'sd99; assign factor_im[360] = -9'sd81;
    assign factor_re[361] = -9'sd104; assign factor_im[361] = -9'sd75;
    assign factor_re[362] = -9'sd108; assign factor_im[362] = -9'sd68;
    assign factor_re[363] = -9'sd112; assign factor_im[363] = -9'sd62;
    assign factor_re[364] = -9'sd116; assign factor_im[364] = -9'sd55;
    assign factor_re[365] = -9'sd119; assign factor_im[365] = -9'sd48;
    assign factor_re[366] = -9'sd122; assign factor_im[366] = -9'sd40;
    assign factor_re[367] = -9'sd124; assign factor_im[367] = -9'sd33;
    assign factor_re[368] = -9'sd126; assign factor_im[368] = -9'sd25;
    assign factor_re[369] = -9'sd127; assign factor_im[369] = -9'sd17;
    assign factor_re[370] = -9'sd128; assign factor_im[370] = -9'sd9;
    assign factor_re[371] = -9'sd128; assign factor_im[371] = -9'sd2;
    assign factor_re[372] = -9'sd128; assign factor_im[372] = 9'sd6;
    assign factor_re[373] = -9'sd127; assign factor_im[373] = 9'sd14;
    assign factor_re[374] = -9'sd126; assign factor_im[374] = 9'sd22;
    assign factor_re[375] = -9'sd125; assign factor_im[375] = 9'sd30;
    assign factor_re[376] = -9'sd122; assign factor_im[376] = 9'sd37;
    assign factor_re[377] = -9'sd120; assign factor_im[377] = 9'sd45;
    assign factor_re[378] = -9'sd117; assign factor_im[378] = 9'sd52;
    assign factor_re[379] = -9'sd114; assign factor_im[379] = 9'sd59;
    assign factor_re[380] = -9'sd110; assign factor_im[380] = 9'sd66;
    assign factor_re[381] = -9'sd106; assign factor_im[381] = 9'sd72;
    assign factor_re[382] = -9'sd101; assign factor_im[382] = 9'sd79;
    assign factor_re[383] = -9'sd96; assign factor_im[383] = 9'sd85;
    assign factor_re[384] = 9'sd128; assign factor_im[384] = 9'sd0;
    assign factor_re[385] = 9'sd128; assign factor_im[385] = -9'sd5;
    assign factor_re[386] = 9'sd128; assign factor_im[386] = -9'sd9;
    assign factor_re[387] = 9'sd127; assign factor_im[387] = -9'sd14;
    assign factor_re[388] = 9'sd127; assign factor_im[388] = -9'sd19;
    assign factor_re[389] = 9'sd126; assign factor_im[389] = -9'sd23;
    assign factor_re[390] = 9'sd125; assign factor_im[390] = -9'sd28;
    assign factor_re[391] = 9'sd124; assign factor_im[391] = -9'sd33;
    assign factor_re[392] = 9'sd122; assign factor_im[392] = -9'sd37;
    assign factor_re[393] = 9'sd121; assign factor_im[393] = -9'sd42;
    assign factor_re[394] = 9'sd119; assign factor_im[394] = -9'sd46;
    assign factor_re[395] = 9'sd118; assign factor_im[395] = -9'sd50;
    assign factor_re[396] = 9'sd116; assign factor_im[396] = -9'sd55;
    assign factor_re[397] = 9'sd114; assign factor_im[397] = -9'sd59;
    assign factor_re[398] = 9'sd111; assign factor_im[398] = -9'sd63;
    assign factor_re[399] = 9'sd109; assign factor_im[399] = -9'sd67;
    assign factor_re[400] = 9'sd106; assign factor_im[400] = -9'sd71;
    assign factor_re[401] = 9'sd104; assign factor_im[401] = -9'sd75;
    assign factor_re[402] = 9'sd101; assign factor_im[402] = -9'sd79;
    assign factor_re[403] = 9'sd98; assign factor_im[403] = -9'sd82;
    assign factor_re[404] = 9'sd95; assign factor_im[404] = -9'sd86;
    assign factor_re[405] = 9'sd92; assign factor_im[405] = -9'sd89;
    assign factor_re[406] = 9'sd88; assign factor_im[406] = -9'sd93;
    assign factor_re[407] = 9'sd85; assign factor_im[407] = -9'sd96;
    assign factor_re[408] = 9'sd81; assign factor_im[408] = -9'sd99;
    assign factor_re[409] = 9'sd78; assign factor_im[409] = -9'sd102;
    assign factor_re[410] = 9'sd74; assign factor_im[410] = -9'sd105;
    assign factor_re[411] = 9'sd70; assign factor_im[411] = -9'sd107;
    assign factor_re[412] = 9'sd66; assign factor_im[412] = -9'sd110;
    assign factor_re[413] = 9'sd62; assign factor_im[413] = -9'sd112;
    assign factor_re[414] = 9'sd58; assign factor_im[414] = -9'sd114;
    assign factor_re[415] = 9'sd53; assign factor_im[415] = -9'sd116;
    assign factor_re[416] = 9'sd49; assign factor_im[416] = -9'sd118;
    assign factor_re[417] = 9'sd45; assign factor_im[417] = -9'sd120;
    assign factor_re[418] = 9'sd40; assign factor_im[418] = -9'sd122;
    assign factor_re[419] = 9'sd36; assign factor_im[419] = -9'sd123;
    assign factor_re[420] = 9'sd31; assign factor_im[420] = -9'sd124;
    assign factor_re[421] = 9'sd27; assign factor_im[421] = -9'sd125;
    assign factor_re[422] = 9'sd22; assign factor_im[422] = -9'sd126;
    assign factor_re[423] = 9'sd17; assign factor_im[423] = -9'sd127;
    assign factor_re[424] = 9'sd13; assign factor_im[424] = -9'sd127;
    assign factor_re[425] = 9'sd8; assign factor_im[425] = -9'sd128;
    assign factor_re[426] = 9'sd3; assign factor_im[426] = -9'sd128;
    assign factor_re[427] = -9'sd2; assign factor_im[427] = -9'sd128;
    assign factor_re[428] = -9'sd6; assign factor_im[428] = -9'sd128;
    assign factor_re[429] = -9'sd11; assign factor_im[429] = -9'sd128;
    assign factor_re[430] = -9'sd16; assign factor_im[430] = -9'sd127;
    assign factor_re[431] = -9'sd20; assign factor_im[431] = -9'sd126;
    assign factor_re[432] = -9'sd25; assign factor_im[432] = -9'sd126;
    assign factor_re[433] = -9'sd30; assign factor_im[433] = -9'sd125;
    assign factor_re[434] = -9'sd34; assign factor_im[434] = -9'sd123;
    assign factor_re[435] = -9'sd39; assign factor_im[435] = -9'sd122;
    assign factor_re[436] = -9'sd43; assign factor_im[436] = -9'sd121;
    assign factor_re[437] = -9'sd48; assign factor_im[437] = -9'sd119;
    assign factor_re[438] = -9'sd52; assign factor_im[438] = -9'sd117;
    assign factor_re[439] = -9'sd56; assign factor_im[439] = -9'sd115;
    assign factor_re[440] = -9'sd60; assign factor_im[440] = -9'sd113;
    assign factor_re[441] = -9'sd64; assign factor_im[441] = -9'sd111;
    assign factor_re[442] = -9'sd68; assign factor_im[442] = -9'sd108;
    assign factor_re[443] = -9'sd72; assign factor_im[443] = -9'sd106;
    assign factor_re[444] = -9'sd76; assign factor_im[444] = -9'sd103;
    assign factor_re[445] = -9'sd80; assign factor_im[445] = -9'sd100;
    assign factor_re[446] = -9'sd84; assign factor_im[446] = -9'sd97;
    assign factor_re[447] = -9'sd87; assign factor_im[447] = -9'sd94;
    assign factor_re[448] = 9'sd128; assign factor_im[448] = 9'sd0;
    assign factor_re[449] = 9'sd128; assign factor_im[449] = -9'sd11;
    assign factor_re[450] = 9'sd126; assign factor_im[450] = -9'sd22;
    assign factor_re[451] = 9'sd124; assign factor_im[451] = -9'sd33;
    assign factor_re[452] = 9'sd121; assign factor_im[452] = -9'sd43;
    assign factor_re[453] = 9'sd116; assign factor_im[453] = -9'sd53;
    assign factor_re[454] = 9'sd111; assign factor_im[454] = -9'sd63;
    assign factor_re[455] = 9'sd106; assign factor_im[455] = -9'sd72;
    assign factor_re[456] = 9'sd99; assign factor_im[456] = -9'sd81;
    assign factor_re[457] = 9'sd92; assign factor_im[457] = -9'sd89;
    assign factor_re[458] = 9'sd84; assign factor_im[458] = -9'sd97;
    assign factor_re[459] = 9'sd75; assign factor_im[459] = -9'sd104;
    assign factor_re[460] = 9'sd66; assign factor_im[460] = -9'sd110;
    assign factor_re[461] = 9'sd56; assign factor_im[461] = -9'sd115;
    assign factor_re[462] = 9'sd46; assign factor_im[462] = -9'sd119;
    assign factor_re[463] = 9'sd36; assign factor_im[463] = -9'sd123;
    assign factor_re[464] = 9'sd25; assign factor_im[464] = -9'sd126;
    assign factor_re[465] = 9'sd14; assign factor_im[465] = -9'sd127;
    assign factor_re[466] = 9'sd3; assign factor_im[466] = -9'sd128;
    assign factor_re[467] = -9'sd8; assign factor_im[467] = -9'sd128;
    assign factor_re[468] = -9'sd19; assign factor_im[468] = -9'sd127;
    assign factor_re[469] = -9'sd30; assign factor_im[469] = -9'sd125;
    assign factor_re[470] = -9'sd40; assign factor_im[470] = -9'sd122;
    assign factor_re[471] = -9'sd50; assign factor_im[471] = -9'sd118;
    assign factor_re[472] = -9'sd60; assign factor_im[472] = -9'sd113;
    assign factor_re[473] = -9'sd70; assign factor_im[473] = -9'sd107;
    assign factor_re[474] = -9'sd79; assign factor_im[474] = -9'sd101;
    assign factor_re[475] = -9'sd87; assign factor_im[475] = -9'sd94;
    assign factor_re[476] = -9'sd95; assign factor_im[476] = -9'sd86;
    assign factor_re[477] = -9'sd102; assign factor_im[477] = -9'sd78;
    assign factor_re[478] = -9'sd108; assign factor_im[478] = -9'sd68;
    assign factor_re[479] = -9'sd114; assign factor_im[479] = -9'sd59;
    assign factor_re[480] = -9'sd118; assign factor_im[480] = -9'sd49;
    assign factor_re[481] = -9'sd122; assign factor_im[481] = -9'sd39;
    assign factor_re[482] = -9'sd125; assign factor_im[482] = -9'sd28;
    assign factor_re[483] = -9'sd127; assign factor_im[483] = -9'sd17;
    assign factor_re[484] = -9'sd128; assign factor_im[484] = -9'sd6;
    assign factor_re[485] = -9'sd128; assign factor_im[485] = 9'sd5;
    assign factor_re[486] = -9'sd127; assign factor_im[486] = 9'sd16;
    assign factor_re[487] = -9'sd125; assign factor_im[487] = 9'sd27;
    assign factor_re[488] = -9'sd122; assign factor_im[488] = 9'sd37;
    assign factor_re[489] = -9'sd119; assign factor_im[489] = 9'sd48;
    assign factor_re[490] = -9'sd114; assign factor_im[490] = 9'sd58;
    assign factor_re[491] = -9'sd109; assign factor_im[491] = 9'sd67;
    assign factor_re[492] = -9'sd103; assign factor_im[492] = 9'sd76;
    assign factor_re[493] = -9'sd96; assign factor_im[493] = 9'sd85;
    assign factor_re[494] = -9'sd88; assign factor_im[494] = 9'sd93;
    assign factor_re[495] = -9'sd80; assign factor_im[495] = 9'sd100;
    assign factor_re[496] = -9'sd71; assign factor_im[496] = 9'sd106;
    assign factor_re[497] = -9'sd62; assign factor_im[497] = 9'sd112;
    assign factor_re[498] = -9'sd52; assign factor_im[498] = 9'sd117;
    assign factor_re[499] = -9'sd42; assign factor_im[499] = 9'sd121;
    assign factor_re[500] = -9'sd31; assign factor_im[500] = 9'sd124;
    assign factor_re[501] = -9'sd20; assign factor_im[501] = 9'sd126;
    assign factor_re[502] = -9'sd9; assign factor_im[502] = 9'sd128;
    assign factor_re[503] = 9'sd2; assign factor_im[503] = 9'sd128;
    assign factor_re[504] = 9'sd13; assign factor_im[504] = 9'sd127;
    assign factor_re[505] = 9'sd23; assign factor_im[505] = 9'sd126;
    assign factor_re[506] = 9'sd34; assign factor_im[506] = 9'sd123;
    assign factor_re[507] = 9'sd45; assign factor_im[507] = 9'sd120;
    assign factor_re[508] = 9'sd55; assign factor_im[508] = 9'sd116;
    assign factor_re[509] = 9'sd64; assign factor_im[509] = 9'sd111;
    assign factor_re[510] = 9'sd74; assign factor_im[510] = 9'sd105;
    assign factor_re[511] = 9'sd82; assign factor_im[511] = 9'sd98;
    
    // ?��? 카운?? 0~511
    reg [8:0] data_idx;
    integer i;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            data_idx <= 0;
            for (i = 0; i < 16; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
            o_valid <= 0;
        end else begin
            if (i_valid) begin
                for (i = 0; i < 16; i++) begin
                    dout_i[i] <= din_i[i] * factor_re[data_idx + i] - din_q[i] * factor_im[data_idx + i];
                    dout_q[i] <= din_i[i] * factor_im[data_idx + i] + din_q[i] * factor_re[data_idx + i];
                end
                
                if (data_idx >= 512 - 16) begin  
                    data_idx <= 0;  
                end else begin
                    data_idx <= data_idx + 16;
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule





module shift_processor #(
    parameter IN_WIDTH = 20,
    parameter OUT_WIDTH = 12
)(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [IN_WIDTH-1:0] din_i[15:0],  // 곱셈 결과
    input logic signed [IN_WIDTH-1:0] din_q[15:0],  // 곱셈 결과
    output logic signed [OUT_WIDTH-1:0] dout_i[15:0], // ?�프????결과
    output logic signed [OUT_WIDTH-1:0] dout_q[15:0], // ?�프????결과
    output logic o_valid
);
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < 16; i++) begin
                dout_i[i] <= 0;
                dout_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // 256?�로 ?�누�? >>8 (고정?�수??1.8)
                for (i = 0; i < 16; i++) begin
                    dout_i[i] <= (din_i[i] + 8'd128) >>> 8;
                    dout_q[i] <= (din_q[i] + 8'd128) >>> 8;
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end
endmodule




module stage_2_1_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [13:0] din_i[15:0],
    input logic signed [13:0] din_q[15:0],
    output logic signed [22:0] dout_i[15:0],
    output logic signed [22:0] dout_q[15:0],
    output logic o_valid
);
    // fac8_1: 8�?고정?�수??1.8) ?�위???�터 (?�수/?�수)
    wire signed [9:0] fac8_1_re[0:7];
    wire signed [9:0] fac8_1_im[0:7];

    assign fac8_1_re[0] = 256; assign fac8_1_im[0] = 0;
    assign fac8_1_re[1] = 256; assign fac8_1_im[1] = 0;
    assign fac8_1_re[2] = 256; assign fac8_1_im[2] = 0;
    assign fac8_1_re[3] = 0;   assign fac8_1_im[3] = -256;
    assign fac8_1_re[4] = 256; assign fac8_1_im[4] = 0;
    assign fac8_1_re[5] = 181; assign fac8_1_im[5] = -181;
    assign fac8_1_re[6] = 256; assign fac8_1_im[6] = 0;
    assign fac8_1_re[7] = -181; assign fac8_1_im[7] = -181;

    logic signed [22:0] fac_reg_i[15:0];
    logic signed [22:0] fac_reg_q[15:0];
    integer i;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin
                // ?�환 구조: 0~7, 8~15??각각 fac8_1[0]~fac8_1[7] ?�서?��??�용
                // 0~7: fac8_1[0]~fac8_1[7] ?�서?��?                for (i = 0; i < 8; i++) begin
                    fac_reg_i[i] <= din_i[i] * fac8_1_re[i] - din_q[i] * fac8_1_im[i];
                    fac_reg_q[i] <= din_i[i] * fac8_1_im[i] + din_q[i] * fac8_1_re[i];
                end
                // 8~15: fac8_1[0]~fac8_1[7] ?�시 ?�서?��?                for (i = 8; i < 16; i++) begin
                    fac_reg_i[i] <= din_i[i] * fac8_1_re[i-8] - din_q[i] * fac8_1_im[i-8];
                    fac_reg_q[i] <= din_i[i] * fac8_1_im[i-8] + din_q[i] * fac8_1_re[i-8];
                end
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end

    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule



module stage_0_1_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [10:0] din_i[15:0],
    input logic signed [10:0] din_q[15:0],
    output logic signed [19:0] dout_i[15:0],
    output logic signed [19:0] dout_q[15:0],
    output logic o_valid
);
    // fac8_1: 8�?고정?�수??1.8) ?�위???�터 (?�수/?�수)
    wire signed [9:0] fac8_1_re[0:7];
    wire signed [9:0] fac8_1_im[0:7];

    assign fac8_1_re[0] = 256; assign fac8_1_im[0] = 0;
    assign fac8_1_re[1] = 256; assign fac8_1_im[1] = 0;
    assign fac8_1_re[2] = 256; assign fac8_1_im[2] = 0;
    assign fac8_1_re[3] = 0;   assign fac8_1_im[3] = -256;
    assign fac8_1_re[4] = 256; assign fac8_1_im[4] = 0;
    assign fac8_1_re[5] = 181; assign fac8_1_im[5] = -181;
    assign fac8_1_re[6] = 256; assign fac8_1_im[6] = 0;
    assign fac8_1_re[7] = -181; assign fac8_1_im[7] = -181;

    logic signed [19:0] fac_reg_i[15:0];
    logic signed [19:0] fac_reg_q[15:0];

    reg [2:0] fac_idx; // 0~7, ?�위???�터 ?�덱??    reg [2:0] fac_idx_next; // fac_idx + 1???�한 별도 변??    reg [6:0] blk_cnt; // 0~31, 32블록(16개씩)
    reg valid;
    integer i;
    
    // i_valid_d1, i_valid_d2 ??��

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            fac_idx <= 0;
            fac_idx_next <= 1;  // fac_idx + 1 초기??            blk_cnt <= 0;
            valid <= 0;
            for (i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin // i_valid가 1?�면 곱셈 ?�산 ?�작
                // 4?�럭마다 ?�위???�터 ?�덱??증�? (64/16=4)
                if (blk_cnt != 0 && blk_cnt % 4 == 0)
                    fac_idx <= fac_idx + 1;

                for (i = 0; i < 16; i++) begin
                    fac_reg_i[i] <= din_i[i] * fac8_1_re[fac_idx] - din_q[i] * fac8_1_im[fac_idx];
                    fac_reg_q[i] <= din_i[i] * fac8_1_im[fac_idx] + din_q[i] * fac8_1_re[fac_idx];
                end
                valid <= 1; // ?�래?��?복원
                
                if (blk_cnt == 32) begin
                    blk_cnt <= 0;
                    fac_idx <= 0;
                    // valid?????�럭 ???��? (32번째 블록 결과 ?�달???�해)
                end else begin
                    blk_cnt <= blk_cnt + 1;
                end
            end else begin
                // 32번째 블록 처리 ?�에??valid�??��?
                if (blk_cnt == 32) begin
                    valid <= 1; // 마�?�?블록 결과 ?�달???�해 ?��?
                end else begin
                    valid <= 0;
                end
            end
        end
    end

    // o_valid�????�럭 ??�� 출력
    reg valid_d;
    
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            valid_d <= 0;
        end else begin
            valid_d <= valid; // valid�????�럭 지??        end
    end

    assign o_valid = valid_d;
    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule

module stage_2_0_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [12:0] din_i[15:0],
    input logic signed [12:0] din_q[15:0],
    output logic signed [12:0] dout_i[15:0],
    output logic signed [12:0] dout_q[15:0],
    output logic o_valid
);
    logic signed [12:0] fac_reg_i [15:0];
    logic signed [12:0] fac_reg_q [15:0];

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            o_valid <= 0;
            for (int i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin

                for (int i = 0; i < 6; i++) begin
                    fac_reg_i[i] <= din_i[i];
                    fac_reg_q[i] <= din_q[i];
                end
                fac_reg_i[6] <= din_q[6];
                fac_reg_q[6] <= -din_i[6];
                fac_reg_i[7] <= din_q[7];
                fac_reg_q[7] <= -din_i[7];
                
                for (int i = 8; i < 14; i++) begin
                    fac_reg_i[i] <= din_i[i];
                    fac_reg_q[i] <= din_q[i];
                end
                fac_reg_i[14] <= din_q[14];
                fac_reg_q[14] <= -din_i[14];
                fac_reg_i[15] <= din_q[15];
                fac_reg_q[15] <= -din_i[15];
                o_valid <= 1;
            end else begin
                o_valid <= 0;
            end
        end
    end

    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule



module stage_1_0_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [11:0] din_i[15:0],
    input logic signed [11:0] din_q[15:0],
    output logic signed [11:0] dout_i[15:0],
    output logic signed [11:0] dout_q[15:0],
    output logic o_valid
);
     typedef enum logic [1:0] {FAC_0 = 0, FAC_1 = 1, FAC_2 = 2, FAC_3 = 3} state_t;
    state_t state;

    logic signed [11:0] fac_reg_i [15:0];
    logic signed [11:0] fac_reg_q [15:0];

    reg valid;
    reg [3:0] cycle_counter; 

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= FAC_0;
            valid <= 0;
            cycle_counter <= 0;
            for (int i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            case (state)
                FAC_0: begin
                    if (i_valid) begin
                        for (int i = 0; i < 16; i++) begin
                            fac_reg_i[i] <= din_i[i];
                            fac_reg_q[i] <= din_q[i];
                        end
                        valid <= 1;
                        state <= FAC_1;
                    if (cycle_counter == 8) begin
                        valid <= 0;  // 8�??�료 ??바로 valid ?�림
                        cycle_counter <= 0;
                        state <= FAC_0;
                    end 
                    end
                end
                FAC_1, FAC_2: begin
                    for (int i = 0; i < 16; i++) begin
                        fac_reg_i[i] <= din_i[i];
                        fac_reg_q[i] <= din_q[i];
                    end
                    valid <= 1;
                    state <= state_t'(state + 1);
                end
                FAC_3: begin
                    for (int i = 0; i < 16; i++) begin
                        fac_reg_i[i] <= din_q[i];
                        fac_reg_q[i] <= -din_i[i];
                    end
                    valid <= 1;
                    
                    cycle_counter <= cycle_counter + 1;
                    state <= FAC_0;
                    
                end
            endcase
        end
    end

    assign o_valid = valid;
    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule



module stage_1_1_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [12:0] din_i[15:0],
    input logic signed [12:0] din_q[15:0],
    output logic signed [22:0] dout_i[15:0],
    output logic signed [22:0] dout_q[15:0],
    output logic o_valid
);
    // fac8_1: 8�?고정?�수??1.8) ?�위???�터 (?�수/?�수)
    wire signed [9:0] fac8_1_re[0:7];
    wire signed [9:0] fac8_1_im[0:7];

    assign fac8_1_re[0] = 256; assign fac8_1_im[0] = 0;
    assign fac8_1_re[1] = 256; assign fac8_1_im[1] = 0;
    assign fac8_1_re[2] = 256; assign fac8_1_im[2] = 0;
    assign fac8_1_re[3] = 0;   assign fac8_1_im[3] = -256;
    assign fac8_1_re[4] = 256; assign fac8_1_im[4] = 0;
    assign fac8_1_re[5] = 181; assign fac8_1_im[5] = -181;
    assign fac8_1_re[6] = 256; assign fac8_1_im[6] = 0;
    assign fac8_1_re[7] = -181; assign fac8_1_im[7] = -181;
    

    logic signed [22:0] fac_reg_i[15:0];
    logic signed [22:0] fac_reg_q[15:0];

    reg [2:0] fac_idx; // 0~7, ?�위???�터 ?�덱??    reg [2:0] fac_idx_next; // fac_idx + 1???�한 별도 변??    reg [5:0] blk_cnt; // 0~31, 32블록(16개씩)
    reg valid;
    integer i;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            fac_idx <= 0;
            fac_idx_next <= 1;  // fac_idx + 1 초기??            blk_cnt <= 0;
            valid <= 0;
            for (i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            if (i_valid) begin // i_valid가 1?�면 곱셈 ?�산 ?�작
                // 1?�계: fac_idx 증�? (?�산 ??
                if (blk_cnt >= 0) begin
                    if (fac_idx >= 6) begin
                        fac_idx <= 0;  // 6->0?�로�??�환
                        fac_idx_next <= 1;  // 0+1
                    end else begin
                        fac_idx <= fac_idx + 2;  // 0->2, 2->4, 4->6
                        fac_idx_next <= fac_idx + 3;  // 2+1, 4+1, 6+1
                    end
                end

                // ??8�? fac_idx ?�용
                for (i = 0; i < 8; i++) begin
                    fac_reg_i[i] <= din_i[i] * fac8_1_re[fac_idx] - din_q[i] * fac8_1_im[fac_idx];
                    fac_reg_q[i] <= din_i[i] * fac8_1_im[fac_idx] + din_q[i] * fac8_1_re[fac_idx];
                end
                
                // ??8�? fac_idx_next ?�용 (???�전??방식)
                for (i = 8; i < 16; i++) begin
                    fac_reg_i[i] <= din_i[i] * fac8_1_re[fac_idx_next] - din_q[i] * fac8_1_im[fac_idx_next];
                    fac_reg_q[i] <= din_i[i] * fac8_1_im[fac_idx_next] + din_q[i] * fac8_1_re[fac_idx_next];
                end
                
                valid <= 1;
            end else begin
                valid <= 0;
            end
            
            // valid가 1???�만 blk_cnt 증�?
            if (valid) begin
                if (blk_cnt == 31) begin
                    valid <= 0;  // 31????valid ?�림
                    blk_cnt <= blk_cnt + 1;
                end else if (blk_cnt == 32) begin
                    blk_cnt <= 0;
                    fac_idx <= 0;
                    fac_idx_next <= 1;  // 리셋 ?�에??초기??                end else begin
                    blk_cnt <= blk_cnt + 1;
                end
            end
        end
    end
    

    assign o_valid = valid;
    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule



module stage_0_0_2(
    input clk,
    input rstn,
    input i_valid,
    input logic signed [9:0] din_i[15:0],
    input logic signed [9:0] din_q[15:0],
    output logic signed [9:0] dout_i[15:0],
    output logic signed [9:0] dout_q[15:0],
    output logic o_valid
);
    typedef enum logic [1:0] {FAC_0 = 0, FAC_1 = 1, FAC_2 = 2, FAC_3 = 3} state_t;
    state_t state;

    logic signed [9:0] fac_reg_i [15:0];
    logic signed [9:0] fac_reg_q [15:0];

    reg [2:0] cnt; // 0~7, 8�?반복
    reg [2:0] total_cnt; // 0~7, 8?�럭 카운?�로 변�?    reg valid;
    reg i_valid_d; // i_valid ?�레?�용
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            i_valid_d <= 0;
        end else begin
            i_valid_d <= i_valid;
        end
    end

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            cnt <= 0;
            total_cnt <= 0;
            state <= FAC_0;
            valid <= 0;
            for (int i = 0; i < 16; i++) begin
                fac_reg_i[i] <= 0;
                fac_reg_q[i] <= 0;
            end
        end else begin
            case (state)
                FAC_0: begin
                    if (i_valid_d) begin // ???�럭 ?�레?�된 ?�호�??�산
                        for (int i = 0; i < 16; i++) begin
                            fac_reg_i[i] <= din_i[i];
                            fac_reg_q[i] <= din_q[i];
                        end
                        valid <= 1;
                        if (total_cnt == 7) begin
                            total_cnt <= 0;
                            cnt <= 0;
                            state <= FAC_1;
                        end else begin
                            total_cnt <= total_cnt + 1;
                        end
                    end else begin
                        valid <= 0;
                    end
                end
                FAC_1, FAC_2: begin
                    for (int i = 0; i < 16; i++) begin
                        fac_reg_i[i] <= din_i[i];
                        fac_reg_q[i] <= din_q[i];
                    end
                    valid <= 1;
                    if (total_cnt == 7) begin
                        total_cnt <= 0;
                        cnt <= 0;
                        state <= state_t'(state + 1);
                    end else begin
                        total_cnt <= total_cnt + 1;
                    end
                end
                FAC_3: begin
                    for (int i = 0; i < 16; i++) begin
                        fac_reg_i[i] <= din_q[i];
                        fac_reg_q[i] <= -din_i[i];
                    end
                    valid <= 1;
                    if (total_cnt == 7) begin
                        total_cnt <= 0;
                        cnt <= 0;
                        state <= FAC_0;
                    end else begin
                        total_cnt <= total_cnt + 1;
                    end
                end
            endcase
        end
    end

    assign o_valid = valid;
    assign dout_i = fac_reg_i;
    assign dout_q = fac_reg_q;
endmodule


