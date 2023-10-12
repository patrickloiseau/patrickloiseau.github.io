open Option
open Proof

module Formule = Term


(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;


(* CONSTRUCTEUR: Hyp.fresh *)

let (fresh: unit -> key) = fun () -> Key.fresh "H" ;;

let (record: key -> unit) = fun key -> Key.record key ;; 



(* PREDICATE *)

let (est_hypothese: fact -> bool) = function HYP(_,_) -> true | _ -> false 

(* Hyp.equiv tests if a set of hypothesis is equivalent to a (sub)set of hypothesis? *)

let equiv ~(current:hyp list) ~(previous: hyp list) = 
  let 
      hyp_equal = fun (k1,c1) (k2,c2) -> c1 = c2 
  in 
    Mlist.forall_in
      (Ens.minus current previous)
      (fun h -> Mlist.member_with hyp_equal h previous)
;;



(* ACCESSEUR *)

let (hyps_of: facts -> hyp list) = Proof.hyps_of_facts ;;

let (conclusion_of: hyp -> formule) = Proof_scheme.conclusion_of_hyp ;;

let (key_of: hyp -> key) = Proof_scheme.key_of_hyp ;;



(* PRINTING *)

let (pretty: hyp -> string) = Proof_scheme.pretty_hyp ;;


(* Hyp.exploit tient compte du numéro d'hypothèse *)

let rec (selectionner_hypothese: key -> facts -> hyp option) = fun k -> 
      function
	| [] -> Fail (k)
		  
	| HYP(id,f)::facts -> if id=k then Succ (id,f) else selectionner_hypothese k facts
	    
	| LEM(_,_)::facts -> selectionner_hypothese k facts
;;


let (exploit: hyp -> prover) = function h -> 
      function (facts,c) ->
	    Explain.starts  _x_ [ "Hyp.exploit" ; pretty h ; " to prove " ; Term.pretty c ] ;
	    Explain.returns _x_
	      ( let (k,conc) = h in
		match  Term.set_to_match c conc with
		| Succ assocs -> 
			begin
			  Explain.print _x_ [ "succeeds with" ; Term.pretty_assocs assocs ] ;
			  Proof.return (Proof_scheme.HYP_apply(h)) ;
			end
		| Fail msg -> 
			if _interactive_mode_ 
			then Proof.return (Proof_scheme.HYP_apply(h)) 
			else Proof.fail [ "Hyp.exploit" ; Key.pretty k ; ":" ; msg ] 
	       )
;;

let (apply: key -> prover) = function k -> 
      function (facts,c) ->
	    match selectionner_hypothese k facts with
	    |	Succ h -> exploit h (facts,c)
	    |	Fail _ -> Proof.fail ["Hyp.apply: cannot find hypothesis" ; k ]
;;


(* Hyp.find se débrouille pour trouver la bonne hypothèse *)
 
(* USEFUL ?
let  (auto_exploit: conclusion -> prover) = fun c -> 
      fun (facts,_) ->
	    let 
		hyps = hyps_of facts
	    in 
	      match List.filter (fun h -> Formule.unifiable c (conclusion h)) hyps with
	      | [] -> return (Proof_scheme.NoProof("Hyp.find: no hyp provides this conclusion",hyps,c))
	      | h::_ -> return (Proof_scheme.HYP_apply(h))
;;

*)

