(* COMPTEUR *)

let _fresh_num = ref 0 

let next_num = function () -> 
      _fresh_num:=!_fresh_num+1 
    
let fresh_num_geq = function i -> 
      if (i >= !_fresh_num) then i else !_fresh_num  


let _hyp_num = ref 0
let new_hyp() = 
  begin
    _hyp_num:= !_hyp_num + 1;
    !_hyp_num
  end


let _prop_num = ref 0 
let new_prop_num() = 
  begin 
    _prop_num:= !_prop_num+1;
    !_prop_num
  end


