
module Formule = Term
module Expr    = Term

open Formule
open Term
open Proof

let (>>) = Proof.bind ;;

let (nat: (expr -> formule) -> prover -> prover -> prover) = fun prop proof0_of proofr_of -> 
      fun (facts,c) -> 
	    match c with
	    | Formule.Qr(n,S "Nat", prop_n) when prop n = prop_n ->
		    let i = Formule.quantified_var (Formule.id n)
		    in
		      (proof0_of (facts, prop (I 0))) 
			>> (fun p0 ->
			      (proofr_of (facts, Qq(i, Impl(prop i, prop (Op("+",[i ; I 1])))))) 
				>> (fun pr ->
				      return (Proof_scheme.REC(n,S "Nat",prop,[p0;pr])) ))

	    | _ -> Proof.fail [ "Rec.nat" ]
;;


