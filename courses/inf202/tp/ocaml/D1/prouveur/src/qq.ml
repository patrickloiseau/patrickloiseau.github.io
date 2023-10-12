open Proof
open Term
open Option

let (>>)  = Proof.bind ;;
let (<|>) = Proof.alt ;;

(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;

(* predicat *)

type predicat = expr -> formule 


(* Regle du quelque soit intro

      proof_of
     ----------
      pred(U0) 
   -------------- Qq_i (Uo notin hypothesis, U0 notin conclusion)
    Qq u, pred(u)

*)


let (intro: predicat -> prover -> prover) = fun pred proof_of ->
      fun (facts,c) ->
	    match c with
	    | Qq(x, _) -> 
		    let x0 = Term.S (Key.fresh (String.capitalize (Term.id x)))
		    in 
		      Explain.starts _x_ [ Explain.rule [ "(QQi) requires to prove " ; Term.pretty (pred x0) ; " for a fresh " ; Term.pretty x0] ] ; 
		      Explain.returns _x_
			( 
			  (proof_of (facts, pred x0)) 
			    >> (fun proof -> 
				    Proof.return (Proof_scheme.QQ_intro(pred, x, x0, proof))
			       )
			 )
			
	    | _ -> Proof.fail [ "Qq.intro" ]
;;

let (basic_intro: predicat -> Term.t -> prover -> prover) = fun pred fresh_skolem_constant proof_of ->
      fun (facts,c) ->
	    match c with
	    | Qq(x, _) -> 
		    let x0 = fresh_skolem_constant
		    in 
		      Explain.starts _x_ [ Explain.rule [ "(QQi) requires to prove " ; Term.pretty (pred x0) ; " for a fresh " ; Term.pretty x0 ] ] ; 
		      Explain.returns _x_
			( 
			  (proof_of (facts, pred x0) 
			    >> (fun proof -> 
				    Proof.return (Proof_scheme.QQ_intro(pred, x, x0, proof))
			       )
			  )
			 )
			
	    | _ -> Proof.fail [ "Qq.intro" ]
;;


let (auto_intro: Term.t -> prover -> prover) = fun fresh_skolem_constant prove ->
      fun (facts,c) ->
	    match c with
	    | Qq(x,p_x) -> 
		    let pred = Term.generalize x p_x
		    in basic_intro pred fresh_skolem_constant prove (facts,c)

	    | _ -> Proof.fail [ "Qq.intro" ]
;;



(* Regle du quel-que-soit elim

                                         Pour tout x dans un ensemble D récursif    

	adp                                adp		       
      ----------                        ----------               
      Qq x, P(x)		         Qrec x:D, P(x)	       
  --------------- Qq_e (x:=e)	      ----------------- Qq_e (x:=e)  
        P(e)                   	           P(e)                   

*)

let (elim_with: predicat -> (var * expr) -> prover -> prover) = fun pred (x,e) proof_of ->
      fun (facts,c) ->
            match compute_unification c (pred e) with
	    | Succ _ -> 
		    ( (proof_of (facts, Qq(x, pred x)))
		     <|>
		      (let recursive_set = Term.unknown() in proof_of (facts, Qr(x,recursive_set,pred x)))
                    )
		      >> (fun p -> Proof.return (Proof_scheme.QQ_elim(pred, e, p)) ) 

	    | Fail _ -> Proof.fail [ "Qq.elim" ]
;;


(* QQ.elim is a very subtle part of the prover. 

   HOW DOES IT WORK?

   Consider the goal of proving:   ((I2 <= (N1+1)) => Q(I2)) from axiom  (QQ n, (QQ i, ((i <= (n+1)) => ((i <= n)\/(i = (n+1))))))

   During the proof intermediate goals (like G1) are made of uninstanciated variable, for instance :

     (G1)           c = (QQ ?_{24}, (?_{23} => (?_{22}\/?_{21})))  

   Then, Qq.elim makes a new intermediate goal (G2) to prove

     (G2)  QQ(x,pred x) = (QQ x, (QQ ?_{24}, (?_{23} => (?_{22}\/?_{21})))))  

   The proof of Goal G2 is obtained by unification with a clone of the axiom (QQ n, (QQ i, ((i <= (n+1)) => ((i <= n)\/(i = (n+1))))))

   Then, x:= n, ?_{24}:=i, ?_{23}:= i<=n+1, ?_{22}:=i<=n, ?_{23}:=i=n+1

   Once the proof of G2 -- that is QQ(x,pred x) -- succeeds, Qq.elim (deeply) set x to the value e provided by the prover (e is N1), thus n becomes N1

   and pred x then becomes QQ ?_{24}:=i, ?_{23}:= i<=n+1  =>  ?_{22}:=i<=n  \/  ?_{23}:=i=n+1

   Another QQ.elim with e = I2 will (deeply) instanciate ?_{24}:=i meaning that i will becomes I2.

   Due to side effects, n:=N1 and i:=I2 will impact all occurences of n and i, everywhere in the proof even in the axiom when n and i where not instanciated.
   That's why we must use clones of the proposition (that are copies with new uninstanciated variable) to store a partially instanciated proposition.
   Clones avoid the unwanted capture of variables that must remains uninstanciated.  
   
*)

let (elim_backup: expr -> prover -> prover) = fun e proof_of ->
      fun (facts,c) ->
	    let (-->) = fun x f -> f x
	    in let pred = Term.generalize e c
	    in let u = Term.unknown() (* we use unknown() to allow unification *)
	    in 
	      Explain.starts _x_ [ Explain.rule [ "(QQe)" ] ] ; 
	      Explain.returns _x_
		(
		 (proof_of (facts, Qq(u, pred u)) (* FIXME: useful? <|> (let d = Term.unknown() in proof_of (facts, Qr(x,d,pred x))) *) )
		   >> (fun proof ->
			 let Qq(x,p_x) = (conclusion_of proof) --> Term.ground --> Term.clone in
			   let pretty_x = Term.pretty x and pretty_e = Term.pretty e and capture_free_pred = begin Term.follow_then_set x e ; p_x --> Term.ground --> (Term.generalize e) end in
			     begin
			       Explain.print _x_ [ Explain.success ["(QQe) succeeds in proving" ] ; Explain.goal [Term.pretty c ] ; " as P(" ; pretty_e ; ")"] ;
			       Explain.print _x_ [ "with" ; pretty_x ; ":=" ; pretty_e ; "and P:= fun # ->" ; Term.pretty (capture_free_pred (Term.V "#")) ] ;
			       Proof.return (Proof_scheme.QQ_elim(capture_free_pred, e, proof))
			    end
		      ) 
		)


let (elim: expr -> prover -> prover) = fun e proof_of ->
      fun (facts,c) ->
	    let (-->) = fun x f -> f x
	    and u = Term.unknown() and uprop = Term.unknown() (* we use unknown() to allow unification *)
	    in 
	      Explain.starts _x_ [ Explain.rule [ "(QQe)" ] ] ; 
	      Explain.returns _x_
		(
		 (proof_of (facts, Qq(u, uprop))
		   >> (fun proof ->
			 let Qq(x,p_x) = (conclusion_of proof) --> Term.ground --> Term.clone in
			   let (* capture_free_predicate *) pred = begin Term.follow_then_set x e ; p_x --> Term.ground --> (Term.generalize e) end 
			   and pretty_x = Term.pretty x and pretty_e = Term.pretty e in
			     begin
			       Explain.print _x_ [ Explain.success ["(QQe) succeeds in proving" ] ; Explain.goal [Term.pretty c ] ; " as P(" ; pretty_e ; ")"] ;
			       Explain.print _x_ [ "with" ; pretty_x ; ":=" ; pretty_e ; "and P:= fun # ->" ; Term.pretty (pred (Term.V "#")) ] ;
			       Proof.return (Proof_scheme.QQ_elim(pred, e, proof))
			     end
		      ) 
		 )
		)


