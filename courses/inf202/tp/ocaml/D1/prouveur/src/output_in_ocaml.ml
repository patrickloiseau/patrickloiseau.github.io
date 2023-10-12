(* INDENTATION *)

type indentation = int

let (indent: indentation -> string -> string) = fun indentation string ->
  if indentation=0 then string else "\n" ^ (Mep.n_fois (indentation," ")) ^ string

let (inc: indentation -> indentation) = fun indentation -> indentation+2


(* OCAML SYNTAX *)

let (ocaml_funcall: string list -> string) = fun strings ->
      "(" ^ (String.concat " " strings) ^ ")" 

let (ocaml_funcall_with: indentation -> string list -> string) = fun indentation strings ->
      String.concat ""
	[ indent indentation "(" ; 
	  String.concat " " strings ;
	  indent indentation ")" ]
					  
let (ocaml_constructor: string list -> string) = 
  function
    | [] -> "()"
    | [const] -> const
    | [unary ; arg] -> ocaml_funcall [unary ; arg] 
    | c::args -> c ^ "(" ^ (String.concat "," args) ^ ")"

let (ocaml_list: ('t -> string) -> 't list -> string) = fun pretty ts ->
      "[" ^ (String.concat ";" (List.map pretty ts)) ^ "]"
      
let ocaml_string = Mstring.pretty ;;



(* OUPUT FORMULAE IN OCAML SYNTAX *)
      
open Term

let rec (ocaml_name: term -> string) = 
  function
    | Error msg -> "(*" ^ msg ^ "*)"
    | U(o) -> ocaml_string (o#pretty_with ocaml_name)
    | P(s) 
    | S(s) 
    | V(s) -> ocaml_string s
    | True -> ocaml_constructor ["True"]
    | False -> ocaml_constructor ["False"] 
    | Absurde -> ocaml_constructor ["Absurde"]
    | I n -> string_of_int n
    | Impl(_,_) -> " ==> "
    | Et(_,_) 
    | Conj _ -> " & "
    | Ou(_,_) 
    | Disj _ -> " || "
    | Qq(_,_)   -> "Qq" 
    | Qr(_,_,_) -> "Qqin"
    | Ex(_,_)   -> "Ex"
    | Neg(_)    -> "!"
    | Pred(s,_) -> ocaml_string s
    | Op(s,_)   -> ocaml_string s


let rec (ocaml_term: term -> string) = 
  function
    | Error msg -> "(*" ^ msg ^ "*)"
    | U(o) -> ocaml_funcall ["var" ; ocaml_string (o#pretty_with ocaml_term)]
    | P(s) -> ocaml_constructor ["P" ; ocaml_string s]
    | S(s) -> ocaml_constructor ["S" ; ocaml_string s]
    | V(s) -> ocaml_constructor ["V" ; ocaml_string s]
    | True -> ocaml_constructor ["True" ]
    | False -> ocaml_constructor ["False" ]
    | Absurde -> ocaml_constructor ["Absurde"]
    | I n -> ocaml_constructor ["I" ; string_of_int n]
    | Impl(p,c) -> par ( (ocaml_term p) ^ " ==> " ^ (ocaml_term c) )
    | Et(f1,f2) -> par( String.concat " & " [ ocaml_term f1 ; ocaml_term f2])
    | Ou(f1,f2) -> par( String.concat " || " [ ocaml_term f1 ; ocaml_term f2])
    | Conj forms -> String.concat " & " (List.map ocaml_term forms)
    | Disj forms -> String.concat " || " (List.map ocaml_term forms)
    | Qq(v,f)    -> ocaml_constructor [ "Qq" ; ocaml_term v ; ocaml_term f ]
    | Qr(v,d,f)  -> ocaml_constructor [ "Qqin" ; ocaml_term v ; ocaml_term d ; ocaml_term f ]
    | Ex(v,f)    -> ocaml_constructor [ "Ex" ; ocaml_term v ; ocaml_term f ]
    | Neg(p)     -> ocaml_funcall ["!" ; ocaml_term p]
(* specific predicate *)
    | Pred("reflexive",[r]) -> ocaml_funcall ["reflexive" ; ocaml_term r]

    | Pred("relation",[Op("o",[r;s]);_;_]) -> ocaml_funcall [ "o"; ocaml_term r ; ocaml_term s ]

    | Pred("relation",[r;a;b]) -> ocaml_funcall ["relation"; ocaml_name r ; ocaml_name a ; ocaml_name b]

    | Pred(string,exprs) -> ocaml_constructor [ "Pred" ; ocaml_string string ; ocaml_list ocaml_term exprs ]
    | Op(string,exprs)   -> ocaml_constructor [ "Op"   ; ocaml_string string ; ocaml_list ocaml_term exprs ]




(* OUTPUT PROOF_SCHEME IN OCAML SYNTAX *)

open Option
open Proof_scheme



(* output proof_scheme in ocaml format *)

let (ocaml_hyp: hyp -> string) = fun h ->  ocaml_string (key_of_hyp h)
  
let (ocaml_proof_scheme: proof_scheme -> string) = 

  let rec (ops_with_indent: indentation -> proof_scheme -> string) = fun dec -> function
    | Error(error_msg) | NoProof(error_msg,_,_) ->
	    ocaml_funcall [ "impossible" ; ocaml_string error_msg ]

    | A(n) -> 
	    ocaml_funcall ["Preuve.a_finir" ; string_of_int n]

    | ADP(n,f) -> 
	    ocaml_funcall ["Preuve.de" ; string_of_int n ; ocaml_term f]
	      
    | HYP_apply(h) ->
	    ocaml_funcall ["Hyp.apply" ; ocaml_hyp h]
	      
    | IMPL_elim(p1,p2) ->
	    (ocaml_funcall_with dec ["Impl.elim" ; ops_with_indent (inc dec) p1 ; ops_with_indent (inc dec) p2 ])
	      
    | IMPL_intro(h,p) ->
	    (ocaml_funcall_with dec ["Impl.intro" ; ocaml_hyp h ; ops_with_indent (inc dec) p ])

    | ET_elim(i,p) ->
	    (ocaml_funcall_with dec ["Et.elim" ; string_of_int i ; ops_with_indent (inc dec) p ])

    | ET_intro(p1,p2) ->
	    (ocaml_funcall_with dec ["Et.intro" ; ops_with_indent (inc dec) p1 ; ops_with_indent (inc dec) p2 ])

    | OU_elim(p0,p1,p2) ->
	    (ocaml_funcall_with dec ("Ou.elim" ::(List.map (fun p -> ops_with_indent (inc dec) p) [p0;p1;p2])))

    | OU_intro(i,p,_free_formula_) ->
	    (ocaml_funcall_with dec ["Ou.intro" ; string_of_int i ; ops_with_indent (inc dec) p])
  
    | QQ_elim(_pred_,e,p) ->
	    (ocaml_funcall_with dec ["Qq.elim" ; ocaml_term e ; ops_with_indent (inc dec) p])

    | QQ_intro(_pred_,x,x0,p) ->
	    (ocaml_funcall_with dec ["Qq.auto_intro" ; ops_with_indent (inc dec) p])
	  
    | _ -> "..."

(*
  | EQ_trans of proof_scheme list
  | EQ_elim  of (expr -> formule) * expr * expr * proof_scheme * proof_scheme

  | ABS_intro of proof_scheme * proof_scheme
  | ABS_elim of proof_scheme * conclusion

  | NEGNEG_elim of proof_scheme

  | DEF_apply of name * arguments * proof_scheme * conclusion

  | REC of var * domain * (expr -> formule) * proof_scheme list 

  | QQ_elim  of (expr -> formule) * expr * proof_scheme
  | QQ_intro of (expr -> formule) * var * symbol * proof_scheme
*)
in 
  fun p -> ops_with_indent 2 p
