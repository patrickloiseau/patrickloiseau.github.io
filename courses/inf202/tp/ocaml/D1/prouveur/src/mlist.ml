let (return: 'a -> 'b list) = fun t -> [t] ;;

let (fail: 'a -> 'b list) = fun t -> [] ;;

let (lifted: ('a -> 'b) -> ('a -> 'b list)) = fun f a -> return (f a) ;;

let rec (for_each_in: 'x list-> ('x -> 'y list) -> 'y list) = fun xs f ->
      match xs with
      |	[] -> []
      |	x::xs -> (f x) @ (for_each_in xs f)
;;

let bind = for_each_in ;;
 
let (filter: 'a list -> ('a -> bool) -> 'a list) = fun l p -> 
      for_each_in l (fun a -> if p a then [a] else [])
;;

let filter l p = List.filter p l ;;

let (map_on: 'x list -> ('x -> 'y) -> 'y list) = fun xs f -> List.map f xs ;;

let (forall_in: 'x list -> ('x -> bool) -> bool) = fun p xs -> List.for_all xs p ;;


let (last: 't list -> 't) = 
  let rec (last_rec: 't -> 't list -> 't) = fun acc ->
	function
	  | [] -> acc
	  | t::ts -> last_rec t ts
  in
    fun l -> last_rec (List.hd l) (List.tl l) 
;;


let rec make = fun d f ->
      if d>f then []
      else d :: (make (d+1) f)
;;

let rec (zip: 'x list * 'y list -> ('x * 'y) list) = 
  function
    | [],[] -> []
    | x::xs, y::ys -> (x,y)::(zip (xs,ys))

let (apply: ('t -> 'b) list -> 't list -> 'b list) = 
  fun fs ts -> 
	List.map (fun (f,t) -> f t) (zip (fs,ts))
;;

(* UNUSED 
let rec (select: int list * 't list -> 't list) = 
  function
    | ([]   , _) -> []
    | (n::ns, l) -> (List.nth l n) :: (select (ns,l))
;;
  
*)

let (ajac: 't -> ('t list) list -> ('t list) list) = fun t tss -> map_on tss (fun ts -> t::ts) ;;

let rec (product: ('t list) list -> ('t list) list) = 
      function
	| [] -> [ [] ]
	| ts::others -> for_each_in ts (fun t -> ajac t (product others))
;;


let rec (member_with: ('elt -> 'elt -> bool) -> 'elt -> 'elt list -> bool) = fun equal elt ->
      function
	| [] -> false
	| x::xs when (equal elt x) -> true
	| _::xs -> member_with equal elt xs
;;
