
open Proof
open Proof_scheme

type expr = Term.expr 
type equality = Term.formule

let (>*>) = Proof.map_on ;;
let (>>)  = Proof.bind ;;


let (equalities: expr -> int -> expr -> equality list) = 
  fun e_lhs n e_rhs ->
	let  vars =  (Mlist.make 1 n) >*> (fun i -> Term.unknown())
	in (Mlist.zip (e_lhs :: vars, vars @ [e_rhs])) >*> (fun (x,y) -> Term.eq x y)  
;;


let (trans: prover list -> facts * conclusion -> proofs) = fun provers -> 
      fun (facts,c) ->
	    let n = List.length provers
	    in
	      match c with
	      | Term.Pred("=",[e_lhs ; e_rhs]) ->
		      let equalities_to_prove = (equalities e_lhs (n-1) e_rhs) >*> (fun eq -> (facts,eq))
		      in let proofs = Mlist.apply provers equalities_to_prove
		      in (Mlist.product proofs) >> (fun p -> return (Proof_scheme.EQ_trans(p)))
			  
	      | _ -> return (error ["Eq.trans" ; Term.pretty c ])
;;


(* Liebniz rule for exploitation of an equality

   proof_of   proof_of
  ---------   -------
     P(a)       a=b  
   ------------------ =_e with P
           P(b)
*)


let (elim_with: (expr -> formule) -> expr * expr -> prover -> prover -> prover) = fun prop (a,b) proof1_of proof2_of ->
      fun (facts,c) ->
	    begin
	      Explain.print 0 ["(=e) exploits" ; Term.pretty (Term.eq a b) ; "with [ # ->" ; Term.pretty (prop (Term.V "#")) ; "]"] ;
	      (proof1_of (facts, prop a)) >> (fun p1 ->
		    (proof2_of (facts, Term.eq a b)) >> (fun p2 ->
			  Proof.return (Proof_scheme.EQ_elim(prop,a,b,p1,p2)) ))
	    end


let (elim: expr * expr -> prover -> prover -> prover) = fun (a,b) proof1_of proof2_of ->
      fun (facts,c) ->
	    let c = Term.ground c 
	    in let (a,b,prop) = let prop = Term.generalize b c in if not (Term.equal (prop a) c) then (a,b,prop) else (b,a,Term.generalize a c)
	    in 
	      begin
		Explain.print 0 ["(=e) exploits" ; Term.pretty (Term.eq a b) ; "with [ # ->" ; Term.pretty (prop (Term.V "#")) ; "]"] ;
		(proof1_of (facts, prop a)) >> (fun p1 ->
		      (proof2_of (facts, Term.eq a b)) >> (fun p2 ->
			    Proof.return (Proof_scheme.EQ_elim(prop,a,b,p1,p2)) ))
	      end
		  
