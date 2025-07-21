% Added on 2025/07/01 by jihan 
% Memory Bank FFT with Fixed-Point Support
function [fft_out, memory_info] = fft_memory_bank_fixed(fft_mode, fft_in, varargin)

    % 기본값 설정
    SIM_FIX = 0; % 0: float, 1: fixed
    
    % 추가 파라미터 처리
    if nargin >= 3
        SIM_FIX = varargin{1};
    end
    
    % 입력 데이터 처리
    if (fft_mode==1) % fft
        din = fft_in;
    else % ifft
        din = conj(fft_in);
    end
    
    % 고정소수점 변환 (입력은 3.6 포맷, 중간 연산은 점진적 확장)
    scale_factor = 1.0;  % 기본값
    if SIM_FIX == 1
        % 입력 데이터를 3.6 포맷 범위에 맞게 스케일링 (더 보수적으로)
        max_input = max(max(abs(real(din))), max(abs(imag(din))));
        if max_input > 0
            scale_factor = min(3.0 / max_input, 1.0);  % 더 보수적인 스케일링
            din = din * scale_factor;
        end
        % 양자화 적용 (반올림)
        din = round(real(din) * 64) / 64 + 1j * round(imag(din) * 64) / 64;
        din = saturate_3_6(din);  % 3.6 포맷으로 변환
    end
    
    % 상수 정의
    fac8_0 = [1, 1, 1, -j];
    fac8_1 = [1, 1, 1, -j, 1, 0.7071-0.7071j, 1, -0.7071-0.7071j];
    
    % 고정소수점 상수 변환 (2.7 포맷)
    if SIM_FIX == 1
        % 2.7 포맷으로 양자화: 2^7 = 128 스케일링
        fac8_0 = round(fac8_0 * 128) / 128;
        fac8_1 = round(fac8_1 * 128) / 128;
        fac8_0 = saturate_2_7(fac8_0);
        fac8_1 = saturate_2_7(fac8_1);
    end
    
    % 메모리 정보 초기화
    memory_info.bank_access = [];
    memory_info.clocks = [];
    
    % 입력 데이터를 뱅크에 분산 저장 (FFT 원리에 맞게)
    for i = 1:256
        mem_bank_a(i) = din(2*i-1);  % 홀수 인덱스 (1, 3, 5, ...)
        mem_bank_b(i) = din(2*i);    % 짝수 인덱스 (2, 4, 6, ...)
    end
    
    %-----------------------------------------------------------------------------
    % Module 0 (기존 fft_float.m과 동일한 구조)
    %-----------------------------------------------------------------------------
    
    % step0_0: 기존 fft_float.m과 동일한 수학적 연산
    % 메모리 뱅크는 하드웨어 최적화용이므로 수학적 결과는 동일해야 함
    bfly00_out0 = din(1:256) + din(257:512);  % 기존과 동일
    bfly00_out1 = din(1:256) - din(257:512);  % 기존과 동일
    
    if SIM_FIX == 1
        bfly00_out0 = saturate_3_6(bfly00_out0);  % 첫 번째는 3.6 포맷 유지
        bfly00_out1 = saturate_3_6(bfly00_out1);  % 첫 번째는 3.6 포맷 유지
    end
    
    bfly00_tmp = [bfly00_out0, bfly00_out1];
    
    % 트위들 팩터 곱셈 (기존과 동일)
    for nn=1:512
        bfly00(nn) = bfly00_tmp(nn)*fac8_0(ceil(nn/128));
    end
    
    if SIM_FIX == 1
        bfly00 = saturate_4_5(bfly00);  % 두 번째부터 4.5 포맷으로 확장
    end
    
    % step0_1: 뱅크별로 처리
    for kk=1:2
        for nn=1:128
            bfly01_tmp((kk-1)*256+nn) = bfly00((kk-1)*256+nn) + bfly00((kk-1)*256+128+nn);
            bfly01_tmp((kk-1)*256+128+nn) = bfly00((kk-1)*256+nn) - bfly00((kk-1)*256+128+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly01_tmp = saturate_4_5(bfly01_tmp);  % 4.5 포맷으로 확장
    end
    
    for nn=1:512
        bfly01(nn) = bfly01_tmp(nn)*fac8_1(ceil(nn/64));
    end
    
    if SIM_FIX == 1
        bfly01 = saturate_4_5(bfly01);  % 4.5 포맷으로 확장
    end
    
    % step0_2: 뱅크별로 처리
    for kk=1:4
        for nn=1:64
            bfly02_tmp((kk-1)*128+nn) = bfly01((kk-1)*128+nn) + bfly01((kk-1)*128+64+nn);
            bfly02_tmp((kk-1)*128+64+nn) = bfly01((kk-1)*128+nn) - bfly01((kk-1)*128+64+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly02_tmp = saturate_4_5(bfly02_tmp);  % 4.5 포맷으로 확장
    end
    
    % 트위들 팩터 계산 (기존과 동일, 부동소수점 유지)
    K3 = [0, 4, 2, 6, 1, 5, 3, 7];
    for kk=1:8
        for nn=1:64
            twf_m0((kk-1)*64+nn) = exp(-j*2*pi*(nn-1)*(K3(kk))/512);
        end
    end
    
    % 트위들 팩터 고정소수점 변환 (2.7 포맷)
    if SIM_FIX == 1
        % 2.7 포맷으로 양자화: 2^7 = 128 스케일링
        twf_m0 = round(real(twf_m0) * 128) / 128 + 1j * round(imag(twf_m0) * 128) / 128;
        twf_m0 = saturate_2_7(twf_m0);
    end
    
    for nn=1:512
        bfly02(nn) = bfly02_tmp(nn)*twf_m0(nn);
    end
    
    if SIM_FIX == 1
        bfly02 = saturate_4_5(bfly02);  % 4.5 포맷으로 확장
    end
    
    %-----------------------------------------------------------------------------
    % Module 1 (기존 fft_float.m과 동일한 구조)
    %-----------------------------------------------------------------------------
    
    % step1_0
    for kk=1:8
        for nn=1:32
            bfly10_tmp((kk-1)*64+nn) = bfly02((kk-1)*64+nn) + bfly02((kk-1)*64+32+nn);
            bfly10_tmp((kk-1)*64+32+nn) = bfly02((kk-1)*64+nn) - bfly02((kk-1)*64+32+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly10_tmp = saturate_5_4(bfly10_tmp);  % Module 1: 5.4 포맷으로 확장
    end
    
    for kk=1:8
        for nn=1:64
            bfly10((kk-1)*64+nn) = bfly10_tmp((kk-1)*64+nn)*fac8_0(ceil(nn/16));
        end
    end
    
    if SIM_FIX == 1
        bfly10 = saturate_5_4(bfly10);  % Module 1: 5.4 포맷으로 확장
    end
    
    % step1_1
    for kk=1:16
        for nn=1:16
            bfly11_tmp((kk-1)*32+nn) = bfly10((kk-1)*32+nn) + bfly10((kk-1)*32+16+nn);
            bfly11_tmp((kk-1)*32+16+nn) = bfly10((kk-1)*32+nn) - bfly10((kk-1)*32+16+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly11_tmp = saturate_5_4(bfly11_tmp);  % Module 1: 5.4 포맷으로 확장
    end
    
    for kk=1:8
        for nn=1:64
            bfly11((kk-1)*64+nn) = bfly11_tmp((kk-1)*64+nn)*fac8_1(ceil(nn/8));
        end
    end
    
    if SIM_FIX == 1
        bfly11 = saturate_5_4(bfly11);  % Module 1: 5.4 포맷으로 확장
    end
    
    % step1_2
    for kk=1:32
        for nn=1:8
            bfly12_tmp((kk-1)*16+nn) = bfly11((kk-1)*16+nn) + bfly11((kk-1)*16+8+nn);
            bfly12_tmp((kk-1)*16+8+nn) = bfly11((kk-1)*16+nn) - bfly11((kk-1)*16+8+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly12_tmp = saturate_5_4(bfly12_tmp);  % Module 1: 5.4 포맷으로 확장
    end
    
    % 트위들 팩터 계산 (기존과 동일, 2.7 포맷)
    K2 = [0, 4, 2, 6, 1, 5, 3, 7];
    for kk=1:8
        for nn=1:8
            twf_m1((kk-1)*8+nn) = exp(-j*2*pi*(nn-1)*(K2(kk))/64);
        end
    end
    
    % 트위들 팩터 고정소수점 변환 (2.7 포맷)
    if SIM_FIX == 1
        % 2.7 포맷으로 양자화: 2^7 = 128 스케일링
        twf_m1 = round(real(twf_m1) * 128) / 128 + 1j * round(imag(twf_m1) * 128) / 128;
        twf_m1 = saturate_2_7(twf_m1);
    end
    
    for kk=1:8
        for nn=1:64
            bfly12((kk-1)*64+nn) = bfly12_tmp((kk-1)*64+nn)*twf_m1(nn);
        end
    end
    
    if SIM_FIX == 1
        bfly12 = saturate_5_4(bfly12);  % Module 1: 5.4 포맷으로 확장
    end
    
    %-----------------------------------------------------------------------------
    % Module 2 (기존 fft_float.m과 동일한 구조)
    %-----------------------------------------------------------------------------
    
    % step2_0
    for kk=1:64
        for nn=1:4
            bfly20_tmp((kk-1)*8+nn) = bfly12((kk-1)*8+nn) + bfly12((kk-1)*8+4+nn);
            bfly20_tmp((kk-1)*8+4+nn) = bfly12((kk-1)*8+nn) - bfly12((kk-1)*8+4+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly20_tmp = saturate_8_1(bfly20_tmp);  % Module 2: 8.1 포맷으로 최종 확장
    end
    
    for kk=1:64
        for nn=1:8
            bfly20((kk-1)*8+nn) = bfly20_tmp((kk-1)*8+nn)*fac8_0(ceil(nn/2));
        end
    end
    
    if SIM_FIX == 1
        bfly20 = saturate_8_1(bfly20);  % Module 2: 8.1 포맷으로 최종 확장
    end
    
    % step2_1
    for kk=1:128
        for nn=1:2
            bfly21_tmp((kk-1)*4+nn) = bfly20((kk-1)*4+nn) + bfly20((kk-1)*4+2+nn);
            bfly21_tmp((kk-1)*4+2+nn) = bfly20((kk-1)*4+nn) - bfly20((kk-1)*4+2+nn);
        end
    end
    
    if SIM_FIX == 1
        bfly21_tmp = saturate_8_1(bfly21_tmp);  % Module 2: 8.1 포맷으로 최종 확장
    end
    
    for kk=1:64
        for nn=1:8
            bfly21((kk-1)*8+nn) = bfly21_tmp((kk-1)*8+nn)*fac8_1(nn);
        end
    end
    
    if SIM_FIX == 1
        bfly21 = saturate_8_1(bfly21);  % Module 2: 8.1 포맷으로 최종 확장
    end
    
    % step2_2
    for kk=1:256
        bfly22_tmp((kk-1)*2+1) = bfly21((kk-1)*2+1) + bfly21((kk-1)*2+2);
        bfly22_tmp((kk-1)*2+2) = bfly21((kk-1)*2+1) - bfly21((kk-1)*2+2);
    end
    
    if SIM_FIX == 1
        bfly22_tmp = saturate_8_1(bfly22_tmp);  % Module 2: 8.1 포맷으로 최종 확장
    end
    
    bfly22 = bfly22_tmp;
    
    %-----------------------------------------------------------------------------
    % 비트 리버설 (기존 fft_float.m과 동일)
    %-----------------------------------------------------------------------------
    fp=fopen('memory_bank_fixed_index.txt','w');
    for jj=1:512
        kk = bitget(jj-1,9)*1 + bitget(jj-1,8)*2 + bitget(jj-1,7)*4 + bitget(jj-1,6)*8 + bitget(jj-1,5)*16 + bitget(jj-1,4)*32 + bitget(jj-1,3)*64 + bitget(jj-1,2)*128 + bitget(jj-1,1)*256;
        dout(kk+1) = bfly22(jj);
        fprintf(fp, 'jj=%d, kk=%d, dout(%d)=%f+j%f\n',jj, kk,(kk+1),real(dout(kk+1)),imag(dout(kk+1)));
    end
    fclose(fp);
    
    % 최종 출력을 9.4 포맷으로 변환
    if SIM_FIX == 1
        dout = saturate_9_4(dout);
        % 스케일링 팩터 복원
        dout = dout / scale_factor;
    end
    
    if (fft_mode==1) % fft
        fft_out = dout;
    else % ifft
        fft_out = conj(dout)/512;
    end

end

% Saturation 함수들

% 3.6 포맷 (입력 데이터용)
function result = saturate_3_6(input)
    max_val = 7.984375;  % 2^3 - 2^(-6)
    min_val = -8.0;      % -2^3
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 4.5 포맷 (중간 연산용 - Module 0)
function result = saturate_4_5(input)
    max_val = 15.96875;  % 2^4 - 2^(-5)
    min_val = -16.0;     % -2^4
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 5.4 포맷 (중간 연산용 - Module 1)
function result = saturate_5_4(input)
    max_val = 31.9375;   % 2^5 - 2^(-4)
    min_val = -32.0;     % -2^5
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 6.3 포맷 (중간 연산용 - Module 2)
function result = saturate_6_3(input)
    max_val = 63.875;    % 2^6 - 2^(-3)
    min_val = -64.0;     % -2^6
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 7.2 포맷 (중간 연산용 - Module 2 확장)
function result = saturate_7_2(input)
    max_val = 127.75;    % 2^7 - 2^(-2)
    min_val = -128.0;    % -2^7
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 8.1 포맷 (중간 연산용 - Module 2 최종 확장)
function result = saturate_8_1(input)
    max_val = 255.5;     % 2^8 - 2^(-1)
    min_val = -256.0;    % -2^8
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 2.7 포맷 (트위들 팩터용)
function result = saturate_2_7(input)
    max_val = 3.9921875;  % 2^2 - 2^(-7)
    min_val = -4.0;       % -2^2
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end

% 9.4 포맷 (최종 출력용)
function result = saturate_9_4(input)
    max_val = 511.9375;  % 2^9 - 2^(-4)
    min_val = -512.0;    % -2^9
    
    real_part = real(input);
    imag_part = imag(input);
    
    real_part(real_part > max_val) = max_val;
    real_part(real_part < min_val) = min_val;
    imag_part(imag_part > max_val) = max_val;
    imag_part(imag_part < min_val) = min_val;
    
    result = real_part + 1j*imag_part;
end 