open Proof
open Term
open Option

let (>>)  = Proof.bind ;;

(* explaination level *)

let _x_ = 1 ;;

(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;

(* predicat *)

type predicat = expr -> formule 



(* Regle du existe intro

      proof
     ---------
      pred(T) 
   -------------- Ex_i
   Ex x, pred(x)
*)


let (basic_intro: predicat -> prover -> prover) = fun pred proof_of ->
      fun (facts,c) ->
	    let x = 
	      match c with
	      | Ex(x, _) -> x
	      |	_ -> Term.quantified_var("")
	    in
	      Explain.starts _x_ [ Explain.rule [ "(EXi)" ] ] ; 
	      let t = Term.unknown() in
		Explain.print _x_ [ Explain.goal [ Term.pretty (pred t)]] ;
		Explain.returns _x_
		(
		 (proof_of (facts, pred t)) >> (fun proof -> Proof.return (Proof_scheme.EX_intro(pred, x, t, proof)))
		)

;;

let (auto_intro: prover -> prover) = fun proof_of ->
      fun (facts,c) ->
	    match c with
	    | Ex(u,p_u) -> 
		    let prop = Term.generalize u p_u
		    in basic_intro prop proof_of (facts,c)
;;

let intro = basic_intro ;;




(* Règle du Ex.elim 

  On utilise une version différente de celle du cours (mais équivalente)

  D'après la preuve 1 on sait qu'il existe un 'x' pour lequel la prédicat pred est vrai,
  On souhaite exploiter l'existence d'un tel 'x' pour démontrer C

  Comme on ne sait pas qui est cet 'x',
  il faut montrer que C est une conséquence de pred(x) pour n'importe quel 'x' 
  c'est ce que fait la preuve 2.


     proof1                 proof2
   -------------      ----------------------
   Ex x, pred(x)      QQ x, (pred(x) ==> C)
  ------------------------------------------- Ex_e
                    C

*)

let (elim: prover -> prover -> prover) = fun proof1_of proof2_of ->
      fun (facts,c) ->
	    let u = Term.unknown() and p_u = Term.unknown() in
	      (proof1_of (facts,Term.Ex(u,p_u)))
		>>
	      (fun p1 ->
		    let Term.Ex(x,p_x) = conclusion_of p1 in
		      (proof2_of (facts,Term.Qq(x,Term.Impl(p_x,c))))
			>>
		      (fun p2 -> Proof.return (Proof_scheme.EX_elim(p1,p2)) )
	      )
;;






