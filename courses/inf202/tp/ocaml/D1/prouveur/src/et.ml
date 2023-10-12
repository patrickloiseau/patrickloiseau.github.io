open Proof

let (>>) = Proof.bind ;; 


(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;


(* Les 2 règles du ET_elim

          adp                        adp                
       -------- 	          -------- 	
         A & B  	            A & B  	
     ----------- /\e1	         ----------- /\e2
          A                          B            
*)

let (elim1: prover -> facts * conclusion -> proofs) = fun proof_of -> 
      fun (facts,c) ->
	    let conj = Term.Et(c,Term.unknown()) 
	    in (proof_of (facts, conj)) >> (fun p -> Proof.return (Proof_scheme.ET_elim(1,p)))
;;


let (elim2: prover -> facts * conclusion -> proofs) = fun proof_of -> 
      fun (facts,c) ->
	    let conj = Term.Et(Term.unknown(),c) 
	    in (proof_of (facts, conj)) >> (fun p -> Proof.return (Proof_scheme.ET_elim(2,p)))

;;

let (elim: int -> prover -> facts * conclusion -> proofs) = 
  function
    | 1 -> elim1
    | 2 -> elim2
;;


(* Règle du ET_intro

      proof_1    proof_2 
      -----   ------ 	
        F1   	F2        
     ---------------- /\i
         (F1 /\ F2)             
*)


let (intro: prover -> prover -> prover) = fun proof1_of proof2_of -> 
      fun (facts,c) ->
	    let (f1,f2) = 
	      match c with
	      | Term.Et(f1,f2) -> (f1,f2)
	      |	_ -> Term.unknown() , Term.unknown()
	    in
	      Explain.starts _x_ [ Explain.rule [ "(/\\i) "] ] ;
	      Explain.returns _x_
		( 
		  (proof1_of (facts,f1)) >> (fun p1 -> 
			Explain.print  _x_ [ Explain.goal [ Term.pretty (conclusion_of p1) ] ] ;
			(proof2_of (facts,f2)) >> (fun p2 ->	
			      Explain.print _x_ [ Explain.goal [ Term.pretty (conclusion_of p2) ] ] ;
			      Explain.print _x_ [ Explain.success [ Term.pretty (Term.Et(conclusion_of p1, conclusion_of p2)) ] ] ;
			      Proof.return (Proof_scheme.ET_intro(p1,p2)) ))
		 )
;;

