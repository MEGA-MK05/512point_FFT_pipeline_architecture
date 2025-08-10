% Added on 2024/01/29 by jihan 
function [out_dat] = sat(in_dat, num) % 11 <= num <= 16

  if (num==11) 
   if (in_dat>=1024)
	out_dat = 1023;
   elseif(in_dat<=-1024)	
	out_dat = -1024;
   else	
	out_dat = in_dat;
   end
  elseif (num==12)	
   if (in_dat>=2048)
	out_dat = 2047;
   elseif(in_dat<=-2048)	
	out_dat = -2048;
   else	
	out_dat = in_dat;
   end
  elseif (num==13)	
   if (in_dat>=4096)
	out_dat = 4095;
   elseif(in_dat<=-4096)	
	out_dat = -4096;
   else	
	out_dat = in_dat;
   end
  elseif (num==14)	
   if (in_dat>=8192)
	out_dat = 8191;
   elseif(in_dat<=-8192)	
	out_dat = -8192;
   else	
	out_dat = in_dat;
   end
  elseif (num==15)	
   if (in_dat>=16384)
	out_dat = 16383;
   elseif(in_dat<=-16384)	
	out_dat = -16384;
   else	
	out_dat = in_dat;
   end
  elseif (num==16)	
   if (in_dat>=32768)
	out_dat = 32767;
   elseif(in_dat<=-32768)	
	out_dat = -32768;
   else	
	out_dat = in_dat;
   end
  end



end
