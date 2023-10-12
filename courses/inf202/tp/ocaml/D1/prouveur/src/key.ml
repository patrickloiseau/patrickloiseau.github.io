
type key = string ;;

type t = key ;;

(* make *)  

let (make: string -> int -> key) = fun s n -> s ^ (string_of_int n) ;;

(* nil, null *)

let nil = "" ;;

let (is_null: key -> bool) = fun k -> k=nil ;;


(* fresh keys *)

let _counters = ref [] ;;

let (fresh: string -> key) = fun s ->
      let counter = 
	(match List.partition (fun (id,_) -> id=s) !_counters with
	| ([(s,c)],others) -> 
		begin _counters:= (s,c+1)::others ; c+1 end
		  
	| ([],others) -> 
		begin _counters:= (s,1)::others ; 1 end
	)
      in make s counter
;;

let (reset: unit -> unit) = fun () -> _counters:= [] ;;


(* parse *)

 
let (parse: string -> string * int) = fun str ->
      let rec (horner: int list -> int) = 
	function
	  | [] -> 0
	  | u::cs -> u + 10 * (horner cs)
      and (split: char list * char list -> char list -> (char list * char list)) = fun (digits,letters) ->
	    function
	      | [] -> (digits,letters)
	      | c::cs when Mstring.is_digit c -> split (c::digits,letters) cs
	      | c::cs -> split (digits,c::letters) cs
      in
	let (stigid,srettel) = split ([],[]) (List.rev (Mstring.string_to_list str))
	in (Mstring.list_to_string (List.rev srettel) , horner (List.map Mstring.int_of_digit stigid) )
;;

let (record: key -> unit) = fun k ->
      let (s,c) = parse k 
      in
	match List.partition (fun (id,_) -> id=s) !_counters with
	| ([(s,c')],others) -> _counters:= (s,max c c')::others 
	| ([]      ,others) -> _counters:= (s,c)::others
;;



(* pretty *)

let (pretty: key -> string) = 
  function
    | "" -> "?"
    | str -> str 
;;

(* latex *)

let (latex: key -> Latex.t) = fun key ->
      let (s,n) = parse key in 
	if n > 0 
	then String.concat "" [ s ;  "_{" ; string_of_int n ; "}" ]
	else s
;;




