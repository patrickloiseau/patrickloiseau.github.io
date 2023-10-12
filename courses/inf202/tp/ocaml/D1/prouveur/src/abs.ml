
module Formule = Term

open Proof
open Proof_scheme

let (>>) = Proof.bind ;;


(* Règle du _|_ elim

    _|_
  -------- _|_elim
     C

*)

let (elim: prover -> prover) = fun proof_of ->
      fun (facts,c) ->
	    match c with
	    | Formule.False -> Proof.fail [ "Abs.elim" ]
	    | _ -> (proof_of (facts,Formule.False)) >> (fun p -> Proof.return (ABS_elim(p,c)))
;;


(* Rule of _|_ intro is useless
                                                     !A
                                                   .......... def neg
    A    !A                                    A    A => _|_	      
   -------- _|_ intro    is equivalent to    ---------------- =>_e
     _|_                                            _|_              

*)
