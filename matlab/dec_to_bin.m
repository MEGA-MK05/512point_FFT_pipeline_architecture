% Added on 2024/01/29 by jihan 
function [out_dat] = dec_to_bin(in_dat, num) 

  if (in_dat>=0) 
   for i=1:num
	out_dat(i)=mod(in_dat,2);
	in_dat=floor(in_dat/2);
   end
  else
	in_dat=(-in_dat)-1;
   for i=1:num
	out_dat(i)=mod(in_dat,2);
	out_dat(i)=xor(out_dat(i),1);
	in_dat=floor(in_dat/2);
   end
  end

end
