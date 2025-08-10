% Added on 2025/07/02 by jihan 
function [data_float, data_fixed] = ran_in_gen_stu(fft_mode, num)
 N = num;
 M1 = 259200;
 IA1 = 7141;
 IC1 = 54773; 
 RM1 = 1.0/259200;
 M2 = 134456;
 IA2 = 8121;
 IC2 = 28441; 
 RM2 = 1.0/134456;
 M3 = 243000;
 IA3 = 4561;
 IC3 = 51349; 

 for i=1:512
	data_float_re(i) = rand(1);
	data_float_im(i) = rand;
	data_float(i) = data_float_re(i) + j*data_float_im(i);
 end

 for i=1:N
  if (data_float_re(i)==1.0)
	%data_fixed_re(i) = 127; % <2.7>
	data_fixed_re(i) = 63; % <3.6> % Modified on 2025/07/02 by jihan
  else	
	%data_fixed_re(i) = round(data_float_re(i)*128); % <2.7>
	data_fixed_re(i) = round(data_float_re(i)*64); % <3.6> % Modified on 2025/07/02 by jihan
  end

  if (data_float_im(i)==1.0)
	%data_fixed_im(i) = 127; % <2.7>
	data_fixed_im(i) = 63; % <3.6> % Modified on 2025/07/02 by jihan
  else	
	%data_fixed_im(i) = round(data_float_im(i)*128); % <2.7>
	data_fixed_im(i) = round(data_float_im(i)*64); % <3.6> % Modified on 2025/07/02 by jihan
  end

	data_fixed(i) = data_fixed_re(i) + j*data_fixed_im(i);
 end

end
