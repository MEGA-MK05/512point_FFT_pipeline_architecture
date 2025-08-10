% Added on 2024/01/29 by jihan 
function [min_val] = min_detect(index, cnt, temp) 

  if (index==1)
	min_val=cnt;
  else
    if (temp>cnt) 
	min_val=cnt;
    else
	min_val=temp;	
    end
  end

end
