
(* DEBUGING *)

let _debug_level = 0 ;; (* set to 0 for no debbug info *)

let (debug: int -> string list -> unit) = fun i strings ->
      if i < _debug_level
      then print_string (String.concat " " (["\n" ; String.make i ' ' ] @ strings))
      else ()
;;

(* We use three type of variables:

 - variables provided by unknown() are of the form U(o) where o = (new unknown "") is a free variable, meaning unifiable, printed as ?_num

   They are used for instance in =>_e and \/_e to represent unknown proposition to prove. For example, =>_e creates ?_1 and two subgoals:

       ?_1 => C      ?_1
      --------------------- =>_e
                 C
 
 - variables provided by var(name) only differ from the previous one on their identifier ; unification is allowed.


 - variables provided by quantified_var(name) are of the form U(o) with name as id, BUT unification is forbidden
   They are used in quantified properties: Qq(x,...) and Ex(x,...)


 - variables of the form S(name) are symbols that can only unify with the same symbol EXCEPT in laxist_unification
   They are used in the rule Qq_intro in order to form a subgoals with a fresh, non-unifiable goal

              p (S x0)
          --------------- Qq_intro
             Qq(x, p x)
 
   In order to detect a possible application of =_e, the prover use a laxist_unification that answers positively to the question
   does p(e) and p(S x0) can unify. Laxist unification is just a test, it does not assign variable, neither propagates unification.


      p(e)     e = (S x0)
    -----------------------  =_e 
           p(S x0)
    
*)

open Option

(* TERM *)

(* Term include boolean expressions called formulae and arithmetic expressions *)

type 't container = 
    < id: Key.t
    ; undefined: bool 
    ; defined: bool
    ; unifiable: bool
    ; set_unifiable: bool -> unit
    ; set: 't -> unit
    ; get: 't
    ; clear: unit
    ; pretty_with: ('t -> string) -> string
   (* clonable *)
    ; copy_data: 't Option.some -> unit
    ; make_clone: 't container
    ; free_clone: unit
    ; clone: 't container
    > 


type name = string
      
type term = 
  | Error of string
  (* unifiable variable *)	
  | U of term container
 (* proposition *)
  | P of string 
 (* symbols = symbolic constants *)
  | S of string 
 (* variable *)
  | V of string
 (* constants *)
  | True | False | Absurde
  | I of int
 (* logical connectors *) 
  | Impl of formule * formule
  | Et of formule * formule
  | Ou of formule * formule
  | Conj of formule list
  | Disj of formule list
  | Qq of var * formule
  | Qr of var * domain * formule
  | Ex of var * formule
  | Neg of formule
 (* predicate *)
  | Pred of name * expr list
 (* operator *)
  | Op of name * expr list
 (* anonymous function and application *)
  | Fun of (term list -> term)
  | Apply of fonction * expr list

and formule  = term
and expr     = term
and var      = term (* U of *)
and symbol   = term (* S of *)
and domain   = term (* S of *)
and fonction = term

type t = term


(* hypotheses *)

type hypotheses = formule list


(* identifier *)

let _id = ref 0 
let fresh_id = function () -> begin _id:=!_id+1 ; !_id end

   
(* unifiable variable *)

class variable ( (vid:Key.t) , (unifiable:bool) ) = 
  object(this)
    val mutable _value = Option.None ; 
    val mutable _id = Key.latex (if vid ="" then Key.fresh "?" else vid) ;
    val mutable _unifiable = unifiable ;

    method id = 
	  if _debug_level>1 && not(_unifiable)
	  then "%"^_id 
	  else _id

    method undefined = _value = Option.None ;

    method defined = not(this#undefined) ;

    method unifiable = _unifiable ;

    method set_unifiable = fun b -> _unifiable <- b ;

    method set = fun x -> _value <- Option.Some x ;

    method get = match _value with
    | Option.Some t -> (t:term) 
    | Option.None   -> S(this#id)

    method clear = _value <- Option.None ;

    method pretty_with = fun pretty -> 
	  match _value with
	  | Option.None   -> this#id
	  | Option.Some t -> 
		  if _debug_level > 0
		  then String.concat "" [ this#id ; ":=" ; pretty t ] 
		  else pretty t
    ;

  (* begin - clonable *)

    val mutable _clone = Option.None ;

    method copy_data = fun d -> _value <- d 

    method make_clone = let clone = new variable ( (if _debug_level>0 then "*"^vid else vid), unifiable) in begin clone#copy_data (_value) ; _clone <- Option.Some clone ; clone end

    method clone = 
      match _clone with 
      | Option.Some clone -> clone
      | Option.None -> this#make_clone 

    method free_clone = _clone <- Option.None 

   (* end - clonable *)

  end 


(* SIDE EFFECT *)

let rec (follow_then_set:term -> term -> unit) = fun u e ->
      match u with
      |	U(o) when o#undefined-> o#set e
      |	U(o) -> follow_then_set (o#get) e
      |	_    -> ()
;;


(* CONSTRUCTEURS *)

(* skolem constant *)

let (fresh: string -> term)  = fun x -> S (Key.fresh (String.capitalize x))

(* variables *)

let (unknown: unit -> term) = fun () -> U (new variable ("",true)) ;;

let (var: string -> term) = fun x -> U (new variable (x,true)) ;;

let (quantified_var: string -> term) = fun x -> U (new variable (x,false (* FIXME*))) ;;

(* operator *)

let (eq: expr -> expr -> formule) = fun lhs rhs -> Pred("=",[lhs;rhs]) ;;

let (infeq: expr -> expr -> formule) = fun lhs rhs -> Pred("<=",[lhs;rhs]) ;;

(* error *)

let (error: string list -> formule) = fun strings -> Error (String.concat " " strings)


(* MAP *)

let rec (map: (term -> term) -> term -> term) = fun f -> 
      function
	| Impl(t1,t2) -> Impl(map f t1, map f t2)
	| Et(t1,t2)   -> Et(map f t1, map f t2)
	| Ou(t1,t2)   -> Ou(map f t1, map f t2)
	| Conj(ts)    -> Conj(List.map (map f) ts)
	| Disj(ts)    -> Disj(List.map (map f) ts)
	| Qq(t1,t2)   -> Qq(map f t1, map f t2)
	| Ex(t1,t2)   -> Ex(map f t1, map f t2)
	| Neg(t)      -> Neg(map f t)
	| Pred(p,ts)  -> Pred(p, List.map (map f) ts)
	| Op(p,ts)    -> Op(p, List.map (map f) ts)
	| t -> f t
;;


(* CLONE *)

let (clone: term -> term) = fun term ->
      let vars = ref [] 
      in let clone = 
	map
	  (function 
	    | U(v) -> begin vars:=v::!vars ; U(v#clone) end
	    | t -> t
	  )
	  term
      in
	begin
	  List.iter (fun v -> v#free_clone) !vars ;
	  clone
	end 
;;	
  

(* GROUND *)

let rec (ground: term -> term) = fun term ->
      map
	(function 
	  | U(o) when o#undefined -> U(o)
	  | U(o) -> ground (o#get)
	  | t -> t
	) 
	term
;;


(* EQUAL *)

let rec (equal: term -> term -> bool) = fun t1 t2 -> (ground t1) = (ground t2) ;;


(* GENERALIZE *)  

let rec (generalize: term -> term -> (term -> term)) = 

  let rec (apply: (term -> term) list -> term -> term list) = fun fs x ->
	match fs with
	| [] -> []
	| f::fs -> (f x) :: (apply fs x)
 
  and (generalize_rec:  term -> term -> (term -> term)) = fun e term ->
	if e = term 
	then (fun x -> x)
	else
	  match term with
	  | Impl(t1,t2) -> 
		  let g1 = generalize_rec e t1 
		  and g2 = generalize_rec e t2 
		  in ( fun x -> Impl(g1 x, g2 x) )
		      
	  | Et(t1,t2) -> 
		  let g1 = generalize_rec e t1 
		  and g2 = generalize_rec e t2 
		  in ( fun x -> Et(g1 x, g2 x) )
		      
	  | Ou(t1,t2) -> 
		  let g1 = generalize_rec e t1 
		  and g2 = generalize_rec e t2 
		  in ( fun x -> Ou(g1 x, g2 x) )
		      
	  | Qq(u, p_u) when not(equal e u) -> 
		  let g = generalize_rec e p_u 
		  in ( fun x -> Qq(u, g x) )

	  | Ex(u, p_u) when not(equal e u) -> 
		  let g = generalize_rec e p_u 
		  in ( fun x -> Ex(u, g x) )
		      
	  | Neg(t) -> 
		  let g = generalize_rec e t
		  in ( fun x -> Neg(g x) )
		      
	  | Pred(p,ts) -> 
		  let gs = List.map (generalize_rec e) ts
		  in ( fun x -> Pred(p, apply gs x) )
		      
	  | Op(op,ts) -> 
		  let gs = List.map (generalize_rec e) ts
		  in ( fun x -> Op(op, apply gs x) )
		      
	  | t -> (fun x -> t)
  in 
    fun subterm term -> generalize_rec (ground subterm) (ground term) 
;;


(* PRETTY PRINTING / OUTPUT *)

(* output in ascii *)

let par str = "(" ^ str ^ ")"

let rec (pretty_tuple: string list -> string) = 
  function
    | []      -> ""
    | [ch]    -> ch
    | ch::chs -> ch ^ "," ^ (pretty_tuple chs)
			      
let rec (pretty: formule -> string) = 
  function
    | Error msg -> "(*" ^ msg ^ "*)"
    | U(o) -> (o#pretty_with pretty)
    | P(s) -> if _debug_level>1 then "P_" ^ s else s 
    | S(s) -> if _debug_level>1 then "S_" ^ s else s 
    | V(s) -> if _debug_level>1 then "V_" ^ s else s
    | True -> "true" 
    | False 
    | Absurde -> "_|_"
    | I n -> string_of_int n
    | Impl(p,c) -> par ( (pretty p) ^ " ==> " ^ (pretty c) )
    | Et(f1,f2) -> par( String.concat " /\\ " [ pretty f1 ; pretty f2])
    | Ou(f1,f2) -> par( String.concat " \\/ " [ pretty f1 ; pretty f2])
    | Conj forms -> String.concat "&" (List.map pretty forms)
    | Disj forms -> String.concat "|" (List.map pretty forms)
    | Qq(v,f)    -> par (String.concat "" ["QQ " ; pretty v ; ", " ; pretty f])
    | Qr(v,d,f)  -> par (String.concat "" ["QQ " ; pretty v ; ":" ; pretty d ; ", " ; pretty f])
    | Ex(v,f)    -> par (String.concat "" ["EX " ; pretty  v ; ", " ; pretty f])
    | Neg(p)     -> "!" ^ (pretty p)
    | Pred(p,[e1;e2]) ->
 	    let p = if (String.length p)=1 then p else (" "^p^" ")
	    in par (String.concat p [ pretty e1 ; pretty e2])
    | Pred(p,exprs) -> p ^ (par (pretty_tuple (List.map pretty exprs)))
    | Op(op, exprs) -> 
	    let op = if (String.length op)=1 then op else (" "^op^" ")
	    in par (String.concat op (List.map pretty exprs))

let (print: formule -> unit) = function f -> print_string (String.concat "" [ pretty f ; "\n" ])

let (prettys: term list -> string) = fun terms ->
      String.concat ", " (List.map pretty terms)
;;

let (pretty_fun: (term -> term) -> string) = fun f ->
      par (String.concat " " [ "fun #" ; "->" ; pretty (f (S "#")) ])


(* output in latex *)

let (par:string -> string) = fun str -> "(" ^ str ^ ")" ;;

let (latex_op: string -> Latex.t) = 
  function
    | "!=" -> "\\neq"
    | "<=" -> "\\leq"
    | ">=" -> "\\geq"
    | op -> op

let (latex_domain: string -> Latex.t) = fun string -> Latex.macro "mathbbm" [ string ] 


let (latex: formule -> Latex.t) = fun formule ->

  let rec (latex_with_depth: int -> formule -> Latex.t) = 
    fun depth ->
	  let smart_par = fun str -> if depth=0 then str else "\\parenthesis{" ^ str ^ "}" in 
	    fun formule ->
		  let latex = latex_with_depth (depth+1) in
		    match formule with
		    | Error msg -> Latex.macro "textcolor{red}" [ msg ]
		    | U(o) -> o#pretty_with (latex_with_depth depth)
		    | P(s) -> s 
		    | S(s) -> Key.latex (String.capitalize s)
		    | V(s) -> s
		    | True ->  Latex.macro "textit" [ "true" ]
		    | False 
		    | Absurde -> "\\bot "
		    | I n -> string_of_int n
		    | Impl(p,c) -> smart_par ( (latex p) ^ " \\impl " ^ (latex c) )
		    | Et(f1,f2) -> smart_par ( String.concat "\\andl " [ latex f1 ; latex f2])
		    | Ou(f1,f2)  -> smart_par ( String.concat "\\vee " [ latex f1 ; latex f2])
		    | Conj [] -> "\\bigwedge_{\\emptyset}"
		    | Conj forms -> String.concat "\\andl " (List.map latex forms)
		    | Disj [] -> "\\bigvee_{\\emptyset}"
		    | Disj forms -> "\\bigvee" ^ (Latex.macro "Set" [ String.concat ",~" (List.map latex forms)])
		    | Qq(v,f)   -> smart_par (String.concat "" ["\\forall " ; latex v ; ", " ; latex_with_depth 0 f])
		    | Qr(v,d,f) -> smart_par (String.concat "" ["\\forall " ; latex v ; "\\in" ; latex_domain (pretty d) ; ", " ; latex f])
		    | Ex(v,f)   -> smart_par (String.concat "" ["\\exists " ; latex v ; ", " ; latex f])
		    | Neg(p)    -> Latex.macro "neg" [ latex p ]
		    | Pred(p,[e1;e2]) -> smart_par (String.concat "~" [ latex e1 ; latex_op p ; latex e2])
		    | Pred(p,exprs)   -> (latex_op p) ^ (par (pretty_tuple (List.map (latex_with_depth 0) exprs)))
		    | Op(op,[e])      -> (latex_op op) ^ (par (latex_with_depth 0 e))
		    | Op(op,[e1;e2]) -> smart_par (String.concat "~" [ latex e1 ; latex_op op ; latex e2])
		    | Op(op, exprs)  -> par (String.concat ("~"^(latex_op op)^"~") (List.map latex exprs))
  in
    latex_with_depth 0 formule 
;;



(* ACCESSEURS *)

let (premisse: formule -> formule) = function f ->
      match f with
      | Impl(p,_) -> p
      | _ -> error [ "premisse appliquée à " ; pretty f ]
;;

let (conclusion: formule -> formule) = fun f ->
      let rec (conclusion_rec: formule -> formule) = 
	function 
	  | Impl(_,c) -> c
	  | U(o) when o#defined -> conclusion_rec (ground (U o))
	  | _ -> unknown()
      in
	let c = conclusion_rec f in 
	  begin
	    (* DEBUG 
	       print_string (String.concat "" [ "\n*\n*\n* Term.conclusion: " ; pretty f ; " returns " ; pretty c ; "\n*\n*\n"]) ;
	     *)
	    c
	  end
;;

let (subterm: int -> formule -> formule) = fun i ->
      function
	| Et(f1,f2) when i=1 -> f1
	| Et(f1,f2) when i=2 -> f2
	| Ou(f1,f2) when i=1 -> f1
	| Ou(f1,f2) when i=2 -> f2
	| Conj(ts) 
	| Disj(ts) 
	| Pred(_,ts) 
	| Op(_,ts) -> List.nth ts (i-1)
	| t -> error [ "term.subterm: " ; pretty t ]
;;

let ( left: term -> term) = subterm 1 ;;
let (right: term -> term) = subterm 2 ;;

let (id: term -> string) = 
  function
    | U(o) -> o#id
    | t    -> "«" ^ (pretty t) ^ "»"
;;



(* UNIFICATION with side-effects *)

(* association, substitution *)

type association = term * term 

type substitution = (association list) option


(* substitution as side-effects *)

(* UNUSED
 let (subst_apply: substitution -> unit) = function
  | Succ assocs -> List.iter (fun (o,t) -> o#set t) assocs
  | Fail _ -> ()
;;
*)

let (pretty_assocs: association list -> string) = 
  function
    | [] -> "no assignment"
    | assocs -> String.concat ", " (List.map (fun (t1,t2) -> String.concat ":=" [ id t1 ; pretty t2 ]) assocs)

let (pretty_substitution: substitution -> string) = 
  function
    | Fail msg -> msg
    | Succ assocs -> pretty_assocs assocs

let (reset: term -> unit) = fun _ -> () (* FIXME: function U(o) -> o#clear | _ -> () *) ;;

let (unifiable: term -> bool) = function U(o) -> o#unifiable | _ -> false ;;

let (clear_assocs: association list -> unit) = List.iter (fun (t1,t2) -> reset t1) ;;

let (assoc: var -> association list -> term) = fun var assocs ->
      try List.assoc var assocs 
      with Not_found -> unknown()
;;

let (disj_substitutions: substitution -> substitution -> substitution) = fun s1 s2 ->
	match (s1,s2) with
	| Succ a1  , Succ a2 -> Succ (a1@a2)
	| Succ a   , Fail _
	| Fail _   , Succ a -> Succ a
	| Fail msg1, Fail msg2 -> Fail (String.concat " & " [msg1 ; msg2])
;;

let (<||>) = disj_substitutions ;;

let (conj_substitutions: substitution -> substitution -> substitution) = fun s1 s2 ->
	match (s1,s2) with
	| Succ a1  , Succ a2 -> Succ (a1@a2)
	| Succ _   , Fail msg 
	| Fail msg , Succ _   -> Fail msg 
	| Fail msg1, Fail msg2 -> Fail (String.concat " & " [msg1 ; msg2])
;;

let (<&&>) = conj_substitutions ;;

  

(* refers_to detects self reference in unification *)

let (deeply_refers_to: term -> term container -> bool) = fun term container ->

      let rec (deep_reference: int -> term -> bool) = fun level term ->
	    match term with
	    | U(o) when o == container -> (level>0)
		      
	    | U(o) when o#undefined -> false
		      
	    | U(o) -> deep_reference level o#get 
		      
	    | Impl(e1,e2) 
	    | Et(e1,e2)
	    | Ou(e1,e2) 
	    | Qq(e1,e2)
	    | Ex(e1,e2) -> (deep_reference 1 e1) || (deep_reference 1 e2)
		
	    | Pred(_,args)
	    | Op(_,args) -> List.exists (deep_reference 1) args
		      
	    | Neg(e) -> deep_reference 1 e
		      
	    | _ -> false
      in
	deep_reference 0 term 
;;


(* unification with automatic clear in case of failure *)

let rec (unify_pair: int -> term * term -> substitution) = 
  fun depth (term1,term2) ->
	debug depth ["Term.unify_pair:" ; pretty term1 ; " ~?~ " ; pretty term2 ] ;
	let unify_pair = unify_pair (depth+1) 
	in
	  match term1,term2 with
	  | t1, t2 when t1=t2 -> Succ []
		    
	  | U(o1), U(o2) when o1#undefined && o2#undefined && o1 == o2 -> Succ []

	  | U(o1), U(o2) when o1#defined && o2#defined -> unify_pair (o1#get,o2#get)

	  | U(o1), U(o2) when o1#defined && o2#undefined -> unify_pair (o1#get, U o2)

	  | U(o1), U(o2) when o1#undefined && o2#defined -> unify_pair (U o1, o2#get)
		    
	  | U(o), t when o#undefined && o#unifiable ->
		  if (deeply_refers_to t o) 
		  then Fail (String.concat "" ["Term.unify: self-reference in unification" ;  pretty (U o) ; " ~/~ " ; pretty t ])
		  else begin o#set t ; Succ [ (U o,t) ] end
		      
	  | t, U(o) when o#undefined && o#unifiable ->
		  if (deeply_refers_to t o) 
		  then Fail (String.concat "" ["Term.unify: self-reference in unification" ;  pretty t ; " ~/~ " ; pretty (U o) ])
		  else begin o#set t ; Succ [ (U o, t) ] end

	  | U(o), t -> unify_pair (o#get,t)
	  | t, U(o) -> unify_pair (t,o#get)
		    
	  | V(n1), V(n2) when n1=n2 -> Succ [] 
	  | S(n1), S(n2) when n1=n2 -> Succ [] 
	  | P(n1), P(n2) when n1=n2 -> Succ [] 
		    
	  | Qq(x1,t1), Qq(x2,t2) 
	  | Ex(x1,t1), Ex(x2,t2) 
	    -> unify_pairs (depth+1) [(x1,x2) ; (t1,t2)]

	  | Neg(t1), Neg(t2) -> unify_pair (t1,t2)

	  | Impl(g1,d1), Impl(g2,d2)  
	  | Et(g1,d1), Et(g2,d2) 
	  | Ou(g1,d1), Ou(g2,d2) 
	    -> unify_pairs (depth+1) [ (g1,g2) ; (d1,d2) ]
	      
	  | Pred(op1,args1) , Pred(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
	    -> unify_pairs (depth+1) (Mlist.zip (args1,args2))
		    
	  | Op(op1,args1) , Op(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
	    -> unify_pairs (depth+1) (Mlist.zip (args1,args2))
		    
		    
	  | t1, t2 -> Fail (String.concat "" ["Term.unify_pair: " ; pretty t1 ; "~/~" ; pretty t2] )
		    
and (unify_pairs: int -> (term * term) list -> substitution) = 
  fun depth ->
	let rec (unify_pairs_rec: association list -> (t*t) list -> substitution) = fun assocs ->
	      function
		| [] -> Succ assocs
		| (t1,t2)::pairs -> 
			(match unify_pair depth (t1,t2) with
			| Succ new_assocs -> unify_pairs_rec (new_assocs @ assocs) pairs
			| Fail msg -> begin clear_assocs assocs ; Fail msg end
			)
	in
	  fun pairs -> unify_pairs_rec [] pairs
;;


let rec (laxist_unify_pair: int -> term * term -> substitution) = 
  fun depth (term1,term2) ->
	debug depth ["Term.laxist_unify_pair:" ; pretty term1 ; " ~?~ " ; pretty term2 ] ;
	match term1,term2 with
	| t1, t2 when t1=t2 -> Succ []
		    
	| U(o1), U(o2) when o1#undefined && o2#undefined && o1 == o2 -> Succ []
		  
	| U(o1), U(o2) when o1#defined && o2#defined -> unify_pair depth (o1#get,o2#get)
		  
	| U(o1), U(o2) when o1#defined && o2#undefined -> unify_pair depth (o1#get, U o2)
		  
	| U(o1), U(o2) when o1#undefined && o2#defined -> unify_pair depth (U o1, o2#get)
		    
	| U(o), t when o#undefined && o#unifiable ->
		if (deeply_refers_to t o) 
		then Fail (String.concat "" ["Term.laxist_unify_pair: self-reference in unification" ;  pretty (U o) ; " ~/~ " ; pretty t ])
		else begin o#set t ; Succ [ (U o,t) ] end
		      
	| t, U(o) when o#undefined && o#unifiable ->
		if (deeply_refers_to t o) 
		then Fail (String.concat "" ["Term.laxist_unify_pair: self-reference in unification" ;  pretty (U o) ; " ~/~ " ; pretty t ])
		else begin o#set t ; Succ [ (U o,t) ] end
		      
	| U(o), t -> laxist_unify_pair depth (o#get,t)
	| t, U(o) -> laxist_unify_pair depth (t,o#get)
		    
	| V(n1), V(n2) when n1=n2 -> Succ [] 
	| P(n1), P(n2) when n1=n2 -> Succ [] 
	| S(n1), S(n2) when n1=n2 -> Succ [] 

	| S(n), t when depth>0 ->
		(match t with
		| S _ | I _ ->
			begin 
			  debug 0 [ "\n/!\\ Term.laxist_unify_pair:" ;  pretty term1 ; "~FORCED~" ; pretty term2 ] ; 
			  Succ [ (S n, t) ] 
			end
		| _ -> Fail (String.concat "" ["Term.laxist_unify_pair: " ; pretty term1 ; "~/~" ; pretty term2] )
		)

	| t, S(n) when depth>0 ->
		(match t with
		| S _ | I _ ->
			begin 
			  debug 0 [ "\n/!\\ Term.laxist_unify_pair:" ;  pretty term1 ; "~FORCED~" ; pretty term2 ] ; 
			  Succ [ (t, S n) ] 
			end
		| _ -> Fail (String.concat "" ["Term.laxist_unify_pair: " ; pretty term1 ; "~/~" ; pretty term2] )
		)
		    
	| Qq(x1,t1), Qq(x2,t2) 
	| Ex(x1,t1), Ex(x2,t2) 
	  -> laxist_unify_pairs depth [(x1,x2) ; (t1,t2)]

	| Neg(t1), Neg(t2) 
	  -> laxist_unify_pair depth (t1,t2)

	| Impl(g1,d1), Impl(g2,d2)  
	| Et(g1,d1), Et(g2,d2) 
	| Ou(g1,d1), Ou(g2,d2) 
	  -> laxist_unify_pairs depth [ (g1,g2) ; (d1,d2) ]
	      
	| Pred(op1,[t1]) , Pred(op2,[t2]) when op1=op2 -> laxist_unify_pair 1 (t1,t2)

	| Pred(op1,args1) , Pred(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
	  -> laxist_unify_pairs depth (Mlist.zip (args1,args2))
      
	|   Op(op1,args1) ,   Op(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
	  -> unify_pairs depth (Mlist.zip (args1,args2))
		    
	| t1, t2 -> Fail (String.concat "" ["Term.laxist_unify_pair: " ; pretty t1 ; "~/~" ; pretty t2] )
		    
and (laxist_unify_pairs: int -> (term * term) list -> substitution) = 
  fun depth ->
	let rec (laxist_unify_pairs_rec: association list -> (t*t) list -> substitution) = fun assocs ->
	      function
		| [] -> Succ assocs
		| (t1,t2)::pairs -> 
			(match laxist_unify_pair depth (t1,t2) with
			| Succ new_assocs -> laxist_unify_pairs_rec (new_assocs @ assocs) pairs
			| Fail msg -> begin clear_assocs assocs ; Fail msg end
			)
	in
	  fun pairs -> laxist_unify_pairs_rec [] pairs
;;


let (unify: term -> term -> substitution) = fun t1 t2 ->
      debug 2 ["Term.unify" ; pretty t1 ; " ~?~ " ; pretty t2 ] ;
      match unify_pair 3 (ground t1, ground t2) with
      | Fail conflicts -> 
	      let msg = String.concat "" [ "Term.unify: " ; pretty t1 ; " ~/~ " ; pretty t2 ; " due to the conflicts:\n" ; conflicts ]
	      in 
		begin
		  debug 2 [ "\n" ; msg ; "\n" ] ;
		  Fail msg
		end
      | Succ assocs -> 
	      begin
		debug 2 ["Term.unify:" ; pretty t1 ; " ~OK~ " ; pretty t2] ;
		(* FIXME ?à quoi sert ce truc?:  List.iter (fun (t1,t2) -> if not (unifiable t1) then reset t1 else ()) assocs ; *)
		Succ assocs
	      end
;;


let (is_substitution_valid: substitution -> bool) = 
  function
    | Fail _ -> false
    | Succ _ -> true
;;

let (clear: substitution -> substitution) = 
  function
    | Succ assocs -> begin clear_assocs assocs ; Succ assocs end
    | fail -> fail
;;

let (compute_unification: term -> term -> substitution) = fun t1 t2 -> clear (unify t1 t2) ;;

let (unifiable: term -> term -> bool) = fun t1 t2 -> is_substitution_valid (compute_unification t1 t2) ;;

let (compute_laxist_unification: term -> term -> substitution) = fun t1 t2 -> clear (laxist_unify_pair 0 (t1,t2)) ;;

(* MATCHING *)

let rec (match_pair: term * term -> substitution) = fun (term1,term2) ->
      match term1,term2 with
    | t1, t2 when t1=t2 -> Succ []

    | U(o1), U(o2) when ground(U o1) = ground(U o2) -> Succ []
	      
    | U(o), t when o#undefined && o#unifiable ->
	    if (deeply_refers_to t o) 
	    then Fail (String.concat "" ["Term.match_pair: self-reference in matching" ;  pretty term1 ; " ~/~ " ; pretty term2 ])
	    else begin o#set t ; Succ [ (U o,t) ] end

    | U(o), t -> match_pair (ground (U o), t)

    | t, U(o) when o#undefined -> Fail (String.concat " " ["Term.match_pair:" ; pretty term1 ; " ~/~ " ; pretty term2 ]) 
    | t, U(o) -> match_pair (t, ground (U o))

    | P(n1), P(n2) when n1=n2 -> Succ [] 
    | S(n1), S(n2) when n1=n2 -> Succ [] 
(*
| I 0, S(n) -> 
	    begin 
	      print_string (String.concat " " [ "\n/!\\ Term.match_pair: FIXME" ;  pretty (I 0) ; "~FORCED~" ; pretty (S n) ]) ; 
	      Succ [ (I 0,S n) ] 
	    end

| S(n), I 0 -> 
	    begin 
	      print_string (String.concat " " [ "\n/!\\ Term.match_pair: FIXME" ;  pretty (I 0) ; "~FORCED~" ; pretty (S n) ]) ; 
	      Succ [ (S n,I 0) ] 
	    end
*)
    | V(n1), V(n2) when n1=n2 -> Succ [] 
     
    | Impl(g1,d1), Impl(g2,d2)  
    | Et(g1,d1), Et(g2,d2) 
    | Ou(g1,d1), Ou(g2,d2) 
      -> match_pairs [ (g1,g2) ; (d1,d2) ]
	      
    | Pred(op1,args1) , Pred(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
      -> match_pairs (Mlist.zip (args1,args2))

    | Op(op1,args1) , Op(op2,args2) when op1=op2 && (List.length args1) = (List.length args2)
      -> match_pairs (Mlist.zip (args1,args2))

    | Qq(x1,t1), Qq(x2,t2) -> match_pairs [(x1,x2) ; (t1,t2)]

    | Ex(x1,t1), Ex(x2,t2) -> match_pairs [(x1,x2) ; (t1,t2)]

    | Neg(t1), Neg(t2) -> match_pair (t1,t2)

    | t1, t2 -> Fail (String.concat "" ["Term.match_pair:" ; pretty t1 ; "~/~" ; pretty t2] )

and (match_pairs: (term * term) list -> substitution) = 
  let rec (match_pairs_rec: association list -> (t*t) list -> substitution) = fun assocs ->
	function
	  | [] -> Succ assocs
	  | (e1,e2)::pairs -> 
		  (match match_pair (e1,e2) with
		  | Succ new_assocs -> match_pairs_rec (new_assocs @ assocs) pairs
		  | Fail msg -> begin clear_assocs assocs ; Fail msg end
		  )
  in
    fun pairs -> match_pairs_rec [] pairs
;;


let (set_to_match: term -> term -> substitution) = fun t1 t2 -> match_pair (t1,t2) ;;

let (compute_matching: term -> term -> substitution) = fun t1 t2 -> clear (set_to_match t1 t2) ;;



(* PREDICATES *)

let (is_an_instance_of: term -> term -> bool) = fun t1 t2 -> is_substitution_valid (compute_matching t1 t2) 


(* Term.splittable
 * this test is used in the heuristics of the prover
 * to tell if a formula can be proved by decomposition 
 *)

let rec (splittable: term -> bool) = 
  function 
    | U(o) when o#undefined -> true (* since U(o) is not instanciated we must try the proof by decomposition since we don't know its actual form *)

    | U(o) -> splittable (ground (U o))

    | P(_) | S(_) | V(_) | I(_) | True | False | Absurde | Fun(_) | Apply(_,_) 
      -> false

    | Ou(_,_) -> false

    | _ -> true
;;

type 't computation = (unit -> 't) -> 't ;;

let (with_unifiable_do: term -> 't computation) = fun term k ->
      match term with
      |	U(o) -> o#set_unifiable true ; let result = k () in o#set_unifiable false ; result
;;

(* Term.could_provide 
 * this test is used in the heuristics of the prover 
 * to tell if a formula could provide the desired conclusion
 *)

let (=?=) t1 t2 = is_substitution_valid (clear (laxist_unify_pair 0 (t1,t2))) ;;

let rec (could_provide: formule -> formule -> bool) = fun formule goal ->
      (formule =?= goal)
    ||
      (match formule with
      | Ou(_,_) | Ex(_,_)  -> true (* /!\ *)

      | U(o) -> (U o) =?= goal

      | Impl(_,c) -> could_provide c goal 

      |	Et(f1,f2) -> (could_provide f1 goal) || (could_provide f2 goal)

      |	Neg(Neg(f)) -> could_provide f goal

      | Qq(u,p_u) -> with_unifiable_do u (fun _ -> could_provide p_u goal)

      |	False -> true

      |	_ -> false
      )
    ||
      (match goal with
      | Ou(a,b) -> (could_provide formule a) || (could_provide formule b)

      | False -> could_provide formule (Neg(unknown()))

      |	_ -> false
      )
;;


let (=?=) t1 t2 = compute_unification t1 t2 ;;

let rec (can_provide: formule -> formule -> substitution) = fun formule goal ->
      (formule =?= goal)
   <||>
      (match formule with
      | Ex(_,_)  -> Succ [] (* /!\ *)

      | U(o) ->  (U o) =?= goal

      | Impl(_,c) -> can_provide c goal 

      | Et(f1,f2) -> (can_provide f1 goal) <||> (can_provide f2 goal)

      | Ou(f1,f2) -> (can_provide f1 goal) <&&> (can_provide f2 goal)

      | Neg(Neg(f)) -> can_provide f goal

      | Qq(u,p_u) -> with_unifiable_do u (fun _ -> can_provide p_u goal)

      | False -> Succ [] 

      | f -> Fail (String.concat " " [ "Term.can_provide:" ; pretty f ; pretty goal ])
      )
  <||>
      (match goal with
      | Ou(a,b) -> (can_provide formule a) <||> (can_provide formule b)

      | False -> can_provide formule (Neg(unknown()))

      | f -> Fail (String.concat " " [ "Term.can_provide:" ; pretty f ; pretty goal ])
      )
;;



