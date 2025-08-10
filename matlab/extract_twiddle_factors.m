function extract_twiddle_factors()

    % Fixed-point scaling factor for twiddle factors (as in original code)
    % twf_m0/m1 : <2.7> means 2 integer bits, 7 fractional bits
    % So, scale by 2^7 = 128
    scaling_factor = 128;

    % K3 and K2 arrays from the original FFT code
    K3 = [0, 4, 2, 6, 1, 5, 3, 7]; % Used for twf_m0 (Module 0)
    K2 = [0, 4, 2, 6, 1, 5, 3, 7]; % Used for twf_m1 (Module 1)

    %% --- Extracting twf_m0 ---
    % Loop structure as in original fft_fixed_stu.m for twf_m0
    % for kk=1:8, for nn=1:64
    % flo_twf_m0((kk-1)*64+nn) = exp(-j*2*pi*(nn-1)*(K3(kk))/512);
    % twf_m0((kk-1)*64+nn) = round(flo_twf_m0((kk-1)*64+nn)*128);

    % Preallocate array for efficiency
    flo_twf_m0 = zeros(1, 512);
    twf_m0 = zeros(1, 512);

    for kk = 1:8
        for nn = 1:64
            idx = (kk-1)*64 + nn;
            flo_twf_m0(idx) = exp(-j*2*pi*(nn-1)*(K3(kk))/512);
            twf_m0(idx) = round(flo_twf_m0(idx) * scaling_factor);
        end
    end

    % Save twf_m0 to a text file
    filepath_twf_m0 = 'twf_m0.txt';
    fid_m0 = fopen(filepath_twf_m0, 'w');
    if fid_m0 == -1
        error('Error opening twf_m0.txt for writing.');
    end
    fprintf(fid_m0, '%% Real_Part, Imag_Part (Fixed-point <2.7>)\n');
    for i = 1:512
        % Print real and imaginary parts as integers
        fprintf(fid_m0, '%d, %d\n', real(twf_m0(i)), imag(twf_m0(i)));
    end
    fclose(fid_m0);
    fprintf('Successfully extracted twf_m0 to %s\n', filepath_twf_m0);

    %% --- Extracting twf_m1 ---
    % Loop structure as in original fft_fixed_stu.m for twf_m1
    % for kk=1:8, for nn=1:8
    % flo_twf_m1((kk-1)*8+nn) = exp(-j*2*pi*(nn-1)*(K2(kk))/64);
    % twf_m1((kk-1)*8+nn) = round(flo_twf_m1((kk-1)*8+nn)*128);

    % Preallocate array for efficiency
    flo_twf_m1 = zeros(1, 64); % Note: K2 loop range is 1:8, nn is 1:8, so total 8*8=64
    twf_m1 = zeros(1, 64);

    for kk = 1:8
        for nn = 1:8
            idx = (kk-1)*8 + nn;
            flo_twf_m1(idx) = exp(-j*2*pi*(nn-1)*(K2(kk))/64);
            twf_m1(idx) = round(flo_twf_m1(idx) * scaling_factor);
        end
    end

    % Save twf_m1 to a text file
    filepath_twf_m1 = 'twf_m1.txt';
    fid_m1 = fopen(filepath_twf_m1, 'w');
    if fid_m1 == -1
        error('Error opening twf_m1.txt for writing.');
    end
    fprintf(fid_m1, '%% Real_Part, Imag_Part (Fixed-point <2.7>)\n');
    for i = 1:64
        % Print real and imaginary parts as integers
        fprintf(fid_m1, '%d, %d\n', real(twf_m1(i)), imag(twf_m1(i)));
    end
    fclose(fid_m1);
    fprintf('Successfully extracted twf_m1 to %s\n', filepath_twf_m1);

end