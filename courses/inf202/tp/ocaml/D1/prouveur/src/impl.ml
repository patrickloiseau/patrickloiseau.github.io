open Proof
open Proof_scheme

let (>>) = Proof.bind ;; 
let (--) = Fact.all_but ;;

(* explaination level *)

let _x_ = 1 ;;


(* USE THE MONAD STYLE instead of the LET STYLE

  let p = proof_of (facts,c)  in f p 

   is equivalent to 

  (proof_of (facts,c)) >> (fun p -> f p) 

*)


 
(* Règle du IMPL_intro

            H(n): p
              .
              . 
             proof_c
            -------
               c
       ---------------- =>_i [ H(n) ]
             p => c
*)


let (intro: key -> prover -> facts * conclusion -> proofs) = fun k proof_of -> 
      fun (facts,f) -> 
	    begin
	      Explain.starts _x_ [ Explain.rule [ "(=>i)" ] ] ; 
	      Explain.returns _x_
	      (match f with
	      | Term.Impl(p,c) -> 
		      let h = (k,p) 
		      in 
			begin
			  Hyp.record k ;
			  Explain.print _x_ [ Explain.leadsto 1 [ "... +" ; Explain.hypothesis [ Hyp.pretty h ] ; "|--" ; Explain.goal [ Term.pretty c ] ] ] ; 
			  (match (proof_of (HYP(h)::facts, c)) >> (fun p -> Proof.return (IMPL_intro(h,p))) with
			  | []    -> Proof.return (NoProof("=>_i [" ^ k ^ "] impossible",Hyp.hyps_of facts,c)) 
			  | proof -> proof
			  )
			end
			  
	      | Term.U(i) ->
		      let p = Term.var k
		      and c = Term.unknown()
		      in let h = (k,p)
		      in 
			begin
			  Hyp.record k ;
			  Explain.print _x_ ["GOAL:" ; Explain.hypothesis [ Hyp.pretty h ] ; ",... |--" ; Explain.goal [ Term.pretty c ] ] ; 
			  (proof_of (HYP(h)::facts, c)) >> (fun p -> Proof.return (IMPL_intro(h,p))) 
			end
			  
	      | _ -> Proof.fail [ "Impl.intro" ]
	      )
	    end



(* Règle du IMPL_elim

       proof_1     proof_2
       -----   --------
         p?      p? => c
     -------------------- =>_e
             c
*)


let (elim: prover -> prover -> facts * conclusion -> proofs) = fun proof1_of proof2_of -> 
      fun (facts,c) ->
	    begin
	      Explain.starts _x_ [ Explain.rule ["(=>e)"] ] ; 
	      Explain.returns _x_
		(let u = Term.unknown()
 		 in (proof2_of (facts, Term.Impl(u,c))) (* énumère toutes les preuves possibles de Impl(?,c) *)
		     >> (fun p2 ->  (* pour chaque preuve p2 de cette énumération *)
			  let premisse = Term.premisse (Proof.conclusion_of p2) (* we can't use directly u since u is not instanciated. *)
                          (* FIXME2: on ne jette pas l'implication prouvée par p2 mais on la met en dernière position des faits à exploiter *)
                          (* in let facts = (facts -- (fun fact -> Fact.conclusion_of fact = implication)) @ [ Fact.lemma [p2] implication ] *)
			  in proof1_of (facts, premisse) 
			      >> (fun p1 -> Proof.return (IMPL_elim(p1,p2)) ))
		)
	    end

