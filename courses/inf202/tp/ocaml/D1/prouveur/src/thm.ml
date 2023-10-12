
open Proof

let (>>) = Proof.bind ;;

type theorem = prover * formule

let (apply: theorem -> prover) = fun (proof_of,proposition) ->
      fun (facts,conclusion) ->
	    (proof_of ([],proposition)) 
	      >> 
	    (fun p -> 
		  if (Term.unifiable proposition conclusion)
		  then Proof.return p
		  else Proof.fail [ "Thm.apply" ; "cannot unify:" ; Term.pretty proposition ; "~/~" ; Term.pretty conclusion ]
	    )
	      
