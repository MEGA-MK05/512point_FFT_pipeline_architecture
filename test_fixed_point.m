% 고정소수점 양자화 오류 테스트
clear; clc;

fprintf('=== 고정소수점 양자화 오류 테스트 ===\n');

% 1. 코사인 신호 생성
N = 512;
[cos_float, cos_fixed] = cos_in_gen(1, N);  % FFT 모드로 코사인 신호 생성

fprintf('1. 코사인 신호 생성 완료 (512 포인트)\n');

% 2. 부동소수점 vs 고정소수점 비교
fprintf('\n2. 부동소수점 vs 고정소수점 비교...\n');

% 부동소수점 FFT
fprintf('   - 부동소수점 FFT 실행 중...\n');
[fft_float, ~] = fft_memory_bank_fixed(1, cos_float, 0);  % SIM_FIX = 0

% 고정소수점 FFT
fprintf('   - 고정소수점 FFT 실행 중...\n');
[fft_fixed, ~] = fft_memory_bank_fixed(1, cos_float, 1);  % SIM_FIX = 1

% MATLAB 내장 FFT
fprintf('   - MATLAB 내장 FFT 실행 중...\n');
matlab_fft = fft(cos_float);

fprintf('   모든 FFT 완료!\n');

% 3. 결과 분석
fprintf('\n3. 결과 분석...\n');

% 주요 피크 찾기
[~, matlab_peaks] = sort(abs(matlab_fft), 'descend');
[~, float_peaks] = sort(abs(fft_float), 'descend');
[~, fixed_peaks] = sort(abs(fft_fixed), 'descend');

fprintf('   MATLAB FFT 주요 피크: k=%d, %d, %d, %d, %d\n', matlab_peaks(1:5));
fprintf('   부동소수점 FFT 주요 피크: k=%d, %d, %d, %d, %d\n', float_peaks(1:5));
fprintf('   고정소수점 FFT 주요 피크: k=%d, %d, %d, %d, %d\n', fixed_peaks(1:5));

% 4. 오차 분석
fprintf('\n4. 오차 분석...\n');

% 크기 스펙트럼
matlab_magnitude = abs(matlab_fft);
float_magnitude = abs(fft_float);
fixed_magnitude = abs(fft_fixed);

% 오차 계산
error_float = abs(float_magnitude - matlab_magnitude);
error_fixed = abs(fixed_magnitude - matlab_magnitude);

% 최대 오차 지점 찾기
[max_error_float_idx] = find(error_float == max(error_float), 1);
[max_error_fixed_idx] = find(error_fixed == max(error_fixed), 1);

fprintf('   부동소수점 FFT 오차:\n');
fprintf('     - RMS 오차: %.6f\n', sqrt(mean(error_float.^2)));
fprintf('     - 최대 절대 오차: %.6f (k=%d)\n', max(error_float), max_error_float_idx);

fprintf('   고정소수점 FFT 오차:\n');
fprintf('     - RMS 오차: %.6f\n', sqrt(mean(error_fixed.^2)));
fprintf('     - 최대 절대 오차: %.6f (k=%d)\n', max(error_fixed), max_error_fixed_idx);

% 최대 오차 지점 상세 분석
fprintf('\n   최대 오차 지점 상세 분석:\n');
fprintf('   고정소수점 최대 오차 지점 (k=%d):\n', max_error_fixed_idx);
fprintf('     - MATLAB FFT: %.6f + j%.6f (크기: %.6f)\n', ...
    real(matlab_fft(max_error_fixed_idx)), imag(matlab_fft(max_error_fixed_idx)), matlab_magnitude(max_error_fixed_idx));
fprintf('     - 고정소수점 FFT: %.6f + j%.6f (크기: %.6f)\n', ...
    real(fft_fixed(max_error_fixed_idx)), imag(fft_fixed(max_error_fixed_idx)), fixed_magnitude(max_error_fixed_idx));
fprintf('     - 절대 오차: %.6f\n', error_fixed(max_error_fixed_idx));
fprintf('     - 상대 오차: %.2f%%\n', error_fixed(max_error_fixed_idx)/matlab_magnitude(max_error_fixed_idx)*100);

% 상위 5개 오차 지점 찾기
[sorted_errors, sorted_indices] = sort(error_fixed, 'descend');
fprintf('\n   고정소수점 상위 5개 오차 지점:\n');
for i = 1:5
    k = sorted_indices(i);
    fprintf('     %d위: k=%d, 오차=%.6f, MATLAB=%.6f, 고정소수점=%.6f\n', ...
        i, k, error_fixed(k), matlab_magnitude(k), fixed_magnitude(k));
end

% SQNR 계산 (Signal-to-Quantization Noise Ratio)
signal_power = mean(matlab_magnitude.^2);
quantization_noise_power_float = mean(error_float.^2);
quantization_noise_power_fixed = mean(error_fixed.^2);

sqnr_float = 10*log10(signal_power / (quantization_noise_power_float + eps));
sqnr_fixed = 10*log10(signal_power / (quantization_noise_power_fixed + eps));

fprintf('   SQNR:\n');
fprintf('     - 부동소수점 SQNR: %.2f dB\n', sqnr_float);
fprintf('     - 고정소수점 SQNR: %.2f dB\n', sqnr_fixed);

% 5. 시각화
fprintf('\n5. 시각화...\n');

figure('Position', [100, 100, 1200, 400]);

% MATLAB FFT
subplot(1,3,1);
plot(1:N, matlab_magnitude, 'b-', 'LineWidth', 1.5);
title('MATLAB FFT 크기 스펙트럼');
xlabel('주파수');
ylabel('크기');
grid on;

% 부동소수점 FFT
subplot(1,3,2);
plot(1:N, float_magnitude, 'r-', 'LineWidth', 1.5);
title('부동소수점 FFT 크기 스펙트럼');
xlabel('주파수');
ylabel('크기');
grid on;

% 고정소수점 FFT
subplot(1,3,3);
plot(1:N, fixed_magnitude, 'g-', 'LineWidth', 1.5);
title('고정소수점 FFT 크기 스펙트럼');
xlabel('주파수');
ylabel('크기');
grid on;

sgtitle('FFT 크기 스펙트럼 비교');

fprintf('\n=== 고정소수점 양자화 오류 테스트 완료 ===\n'); 