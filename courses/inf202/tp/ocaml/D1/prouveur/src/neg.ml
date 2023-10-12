
module Formule = Term

open Proof
open Proof_scheme

let (>>) = Proof.bind ;;


(* Règle du !! elim

  proof_of with the additional hypothesis : H: C => _|_
  --------  
     C      H: C => _|_ 
  ---------------------- =>_e  
           _|_
  ---------------------- =>_i [H]
    (C => _|_) => _|_
  .................... def ! 
         !!C
  -------------------- !!_elim
           C
*)

let (negneg: prover -> prover) = fun proof_of ->
      fun (facts,c) ->
	    match c with
	    | Formule.False -> Proof.fail [ "Neg.negneg" ]
	    | _ -> 
		    let h = (Hyp.fresh(), Formule.Impl(c,Formule.False))
		    in (proof_of ((HYP h)::facts,c)) >> (fun p -> Proof.return (NEGNEG_elim(IMPL_intro(h, IMPL_elim(p, HYP_apply(h))))))



(* Definition of ! 
                          			 
        A => _|_                   !C		   
  ................ def !    ................ def ! 
         !A		         C => _|_          

*)


let (apply: prover -> prover) = fun proof_of ->
      fun (facts,c) ->
	    match c with
	      | Formule.Impl(a,Formule.False) 
	      | Formule.Neg(a) 
		-> Def.apply "neg" [a] proof_of (facts,c)
	      |	_ ->
		      Proof.return (Proof_scheme.error [ "Neg.def" ; Formule.pretty c])
;;


let (exploit: prover -> prover) = fun proof_of ->
      fun (facts,c) ->
	    match c with
	      | Formule.Impl(a,Formule.False) 
	      | Formule.Neg(a) 
		-> Def.exploit "neg" [a] proof_of (facts,c)
	      |	_ ->
		      return (Proof_scheme.error [ "Neg.def" ; Formule.pretty c])
;;
