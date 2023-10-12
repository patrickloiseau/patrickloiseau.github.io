type 't var_object = 
    < copy_value: 't Option.some -> unit
    ; make_clone: 't var_object
    ; free_clone: unit
    ; clone: 't var_object

    ; set_value: 't -> unit
    ; pretty: string
    > 
;;

type expr =
  | Nil
  | I of int
  | V of string
  | O of string * expr list
  | U of expr var_object

let rec pretty = function
  | U v -> v#pretty
  | Nil -> "< >"
  | I n -> string_of_int n
  | V s -> s
  | O(s,es) -> s ^ "(" ^ (String.concat "," (List.map pretty es) ) ^ ")"


let (copy: 't -> 't) = 
  let vars = ref [] 
  in
    let rec (copy_rec: 't -> 't) = 
      function
	| U v -> begin vars:=v::!vars ; U (v#clone) end
	| O(s,es) -> O(s, List.map copy_rec es)
	| t -> t
    in 
      function t -> 
	    let c = copy_rec t in 
	      begin 
		List.iter (fun v -> v#free_clone) !vars ;
		c 
	      end
;;

let rec (reset_clone: 't -> unit) =
  function 
    | U v -> v#free_clone
    | O(s,es) -> List.iter reset_clone es
    | t -> ()
;;

(* compteur *)

let _id = ref 0 

let fresh_id = function () -> begin _id:=!_id+1 ; !_id end
    

(* assignable + clonable variable *)

class var ( (pretty_value: expr -> string) ) = 
  object(this)
    val mutable _value = Option.None ; 

  (* begin - clonable *)
    val mutable _id = fresh_id () ;
    val mutable _clone = Option.None ;
    method copy_value = fun v -> _value <- v ;
    method make_clone = let c = new var pretty_value in begin c#copy_value _value ; _clone <- Option.Some c ; c end
    method clone = 
      match _clone with 
      | Option.Some c -> c
      | Option.None -> this#make_clone 
    method free_clone = _clone <- Option.None ;
   (* end - clonable *)

    method set_value = fun x -> _value <- Option.Some x ;

    method pretty = 
      match _value with
      |	Option.None -> "?" ^ (string_of_int _id) 
      |	Option.Some v -> pretty_value v ;
  end 


let v = new var (pretty) ;;


v == v#clone ;;
v = v#clone ;;

let x = v#clone;;
let y = v#clone;;

v#pretty ;;
x#pretty ;;
y#pretty ;;


let e1 = O("test", [U v ; U x ; U y ]) ;;
pretty e1 ;;

reset_clone e1 ;;

let e2 = copy e1 ;;
pretty e2 ;;

let e3 = copy e2 ;;
pretty e3 ;;

v#pretty ;;
x#pretty ;;
y#pretty ;;

v#set_value (V "v") ;;
pretty e1 ;;
pretty e2 ;;
pretty e3 ;;
v#pretty ;;
x#pretty ;;
y#pretty ;;

x#set_value (V "x") ;;
pretty e1 ;;
pretty e2 ;;
pretty e3 ;;
v#pretty ;;
x#pretty ;;
y#pretty ;;


pretty e1 ;;
pretty e2 ;;
pretty e3 ;;
