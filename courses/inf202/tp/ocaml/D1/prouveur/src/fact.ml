open Option
open Proof

(* explaination level *)

let _x_ = 1 ;;


(* PRINTING *)

let (pretty: fact -> string) = Proof.pretty_fact ;;

let (prettys: facts -> string) = fun facts -> String.concat ", " (List.map pretty facts)  ;;


(* ACCESSEUR *)

let (conclusion_of: fact -> conclusion) =  
  function
    | HYP(_,c) 
    | LEM(_,c) 
    | AXM(_,c) 
    | USE(_,c) -> c
;;

let (hyps_of: facts -> facts) = 
  List.filter (function HYP(_,_) -> true | _ -> false) ;;
  


(* EXPLOIT *)

let (exploit: fact -> prover) = fun fact ->
      fun (facts,c) ->
	    begin
	      Explain.starts _x_ [ "Fact.exploit" ; pretty fact ; " to prove " ; Term.pretty c ] ;
	      let proof = 
		(match fact with
		| LEM(ps,conc) -> Proof.return ps 
		| HYP(k,conc)  -> Hyp.exploit (k,conc) (facts,c)
		| USE(prover,conc) -> 
			(match Term.set_to_match conc c with
			| Succ assocs -> 
				begin
				  Explain.print _x_ [ "with" ; Term.pretty_assocs assocs ] ; 
				  prover (facts,conc) 
				end
			| Fail _ -> Proof.fail [ "Fact.use" ; pretty fact ]
			)
		| AXM(n,conc) -> Axiom.exploit (AXM(n,conc)) (facts,c)
		)
	      in
		Explain.print _x_ ["Fact.exploit " ; pretty fact ; " to prove " ; Term.pretty c ] ;
		Explain.ends _x_ ;
		proof
	    end
;;


(* CONSTRUCTEUR *)

let (lemma: proofs -> conclusion -> fact) = fun proof c -> LEM(one proof, c) ;;


(* FILTER *)

let (all_but: facts -> (fact -> bool) -> facts) = fun facts p ->
      List.filter (fun fact -> not (p fact)) facts 
;; 


(* PREDICATE *)

let (could_provide: fact -> formule -> bool) = fun fact goal -> 
      Term.could_provide (conclusion_of fact) goal


let (can_provide: fact -> formule -> bool) = fun fact goal ->
      Term.is_substitution_valid (Term.can_provide (conclusion_of fact) goal)



