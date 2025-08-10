% Added on 2024/01/29 by jihan 
function [cnt] = mag_detect(in_dat, num) 

  n=0;

  out_dat=dec_to_bin(in_dat, num);

  if (out_dat(num)==0) 
   for i=1:num-1
    if (out_dat(num-i)==0) 
	n=n+1;
    else
	break
    end	
   end
  else
   for i=1:num-1
    if (out_dat(num-i)==1) 
	n=n+1;
    else
	break
    end
   end
  end

  cnt=n;

end
