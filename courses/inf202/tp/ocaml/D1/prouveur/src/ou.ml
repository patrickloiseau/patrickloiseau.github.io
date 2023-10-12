open Proof

let (>>) = Proof.bind ;;
let (>*>) = Mlist.bind ;;

(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;


(* Les 2 règles du OU_intro

       proof                       proof                
      -------- 	                  -------- 	
         A    	                     B  	
     ----------- \/_i1	         ----------- /\_i2
       A \/ B                      A \/ B            
*)

let (intro: int -> prover -> prover) = fun i proof_of -> 
 fun (facts,c) -> 
	match c with
	| Term.Ou(f1 ,f2) -> 
		let (f_to_prove,given_f) = if i=1 then (f1,f2) else (f2,f1)
		in 
		  (proof_of (facts,f_to_prove)) >> (fun p -> return (Proof_scheme.OU_intro(i,p,given_f)))

	| Term.U(o) -> 
		(proof_of (facts, Term.unknown())) >> (fun p -> return (Proof_scheme.OU_intro(i,p,Term.unknown())))




(* La règle du OU_elim

       proofd_of    proofa_of     proofb_of
      -----------   ---------    -----------
         A \/ B       A => C       B => C  	            
     ------------------------------------------ \/_e
                       C  
*)

let (--)  = Fact.all_but ;;

let (elim: prover -> prover -> prover -> prover) = fun proofd_of proofa_of proofb_of -> 
 fun (facts, c) -> 
       let disj = Term.Ou(Term.unknown(),Term.unknown()) in
	   Explain.starts _x_ ["(\\/_e) exploits " ; Term.pretty disj ; " to prove " ; Term.pretty c ] ;
	   let proof = 
	   (proofd_of (facts,disj))  
	     >> (fun pd ->
		   let disj = conclusion_of pd in
		     Explain.print _x_ ["(\\/_e) proved goal 1:" ; Term.pretty disj ] ;
		     match disj with 
		     | Term.Ou(a,b) ->
			     let other_facts = facts -- (fun fact -> (Fact.conclusion_of fact) = disj) in
			       (proofa_of (other_facts,Term.Impl(a,c))) >> (fun pa ->
				     Explain.print _x_ ["(\\/_e) proved goal 2:" ; Term.pretty (Term.Impl(a,c)) ] ;
				     (proofb_of (other_facts,Term.Impl(b,c))) >> (fun pb ->
					   begin
					     Explain.print _x_ ["(\\/_e) proved goal 3:" ; Term.pretty (Term.Impl(b,c)) ] ;
					     Explain.print _x_ ["(\\/_e) exploits " ; Term.pretty (Proof.conclusion_of pd) ; Term.pretty (Proof.conclusion_of pa) ; Term.pretty (Proof.conclusion_of pb) ] ;
					     return (Proof_scheme.OU_elim(pd, pa, pb)) 
					   end ))
				 
		     | not_a_disj -> return (Proof_scheme.error [ "Ou.elim: " ; Term.pretty not_a_disj])
		) 
	   in
	     Explain.ends _x_ ;
	     proof

