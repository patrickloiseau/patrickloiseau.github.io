open Option
open Term
open Proof

let (<=) t1 t2 = Pred("<=",[t1;t2]) ;;
let (&)  t1 t2 = Et(t1,t2) ;;
let (||) t1 t2 = Ou(t1,t2) ;;
let (==) t1 t2 = Pred("=",[t1;t2]) ;;
let (==>) t1 t2 = Impl(t1,t2) ;;
let int n = I n ;;
let (+) t1 t2 = Op("+",[t1;t2]) ;;


(* NAT *)

let nat = 
  let x = Term.quantified_var "x" 
  and n = Term.var "n" and i = Term.var "i" 
  and y = Term.quantified_var "y" 
  in
    [ AXM("nat-supeg-0", Qq(x, (x <= int 0) ==> (int 0 == x)) ) 
    ; AXM("inf-eq-n+1", (i <= (n + int 1)) ==> ((i <= n) || ( i == (n + int 1))) )  
    ; AXM("inf-refl", Qq(y, y <= y) ) 
    ] ;;


(* EQUALITY *)

let equal = [ let t = Term.var "t" in AXM("=_{refl}", t == t) ]


(* NBCOUPE *)

let nbcoupe = fun t -> Op("nbcoupe",[t]) ;;

let nb_coupe = 
  [ AXM("nbcoupe_0", (nbcoupe (int 0)) == (int 0))
  ; let a = Term.var "a" and b = Term.var "b" in AXM("nbcoupe_{a+b}", (nbcoupe (a+b)) == Op("+", [ nbcoupe a ; nbcoupe b ; int 1]))
  ] ;;



let rec (selectionner: name -> facts -> axiom option) = fun name -> 
      function
	| [] -> Fail ("Axiom.selectionner: cannot find axiom " ^ name)
	| HYP(_,_)::facts 
	| LEM(_,_)::facts 
	| USE(_,_)::facts
	  -> selectionner name facts
	| AXM(n,c)::facts -> if n=name then Succ (AXM(n,c)) else selectionner name facts
;;


let (exploit: axiom -> prover) = function AXM(name,conc) ->
      fun (facts,c) ->
	    let clone = Term.clone conc in 
	      begin
		Explain.print 0 ["Axiom.apply (" ; name ; "):" ; Term.pretty clone ; " is a clone of " ; Term.pretty conc ] ;

		(* 1. The conclusion to prove (c) must take the form of the conclusion of the axiom: this is ensured by adjusting (setting) c to match the conclusion.
		 * 2. In the case of an axiom with free variables without universal quantification: the conclusion of the axiom is instanciated to meet the conclusion to prove.
		 * 3. The original axiom must remain uninstanciated in order to be reused in another context.
		 * 
                 * [1,2] explain why we use matching for axiom of the form QQ(x,...) and unification for axioms with free variables (like =_refl: ?t = ?t)
		 * [3] explains why we use clone of the axiom to avoid unwanted instanciation
		 *)

		match Term.set_to_match c conc with
		| Succ _ -> Proof.return (Proof_scheme.AXM_apply(name,clone)) 
		| Fail _ -> 
			(match Term.unify c clone with
			| Succ _   -> Proof.return (Proof_scheme.AXM_apply(name,clone)) 
			| Fail msg -> Proof.fail [ "Axiom.apply:" ; msg ]
			)
	      end


let (apply: name -> prover) = fun name ->
      fun (facts,c) ->
	      match selectionner name facts with
	      | Succ axm -> 
		      begin
			Explain.starts 0 ["Axiom.apply" ; Proof.pretty_fact axm ; "to prove" ; Term.pretty c ] ; 
			let proof = exploit axm (facts,c) in
			  Explain.print 0 ["Axiom.apply" ; Proof.pretty_fact axm ; "to prove" ; Term.pretty c ] ; 
			  Explain.ends 0 ;
			  proof
		      end
	      | Fail _ -> Proof.fail [ "Axiom.apply: no axiom" ; name ]



	    
