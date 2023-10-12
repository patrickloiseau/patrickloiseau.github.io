open Prouveur
open Term
open Exercice

(* Série 2 *)

(* Prouvez en DN les propositions suivants: 

   Proposition 2.1.  (A /\ B ==> C) ==> (A ==> (B ==> C))
   Proposition 2.2.  (A /\ (B \/ C)) ==> (A /\ B) \/ (A /\ C)
*)

(*  On déclare des propositions booleennes *)

let a = P("A") and b = P("B") and c = P("C") and d = P("D") and e = P("E")  ;;


(* On formalise l'énoncé : 
   Proposition 2.1. (A /\ B ==> C) ==> (A ==> (B ==> C))
*)

let prop_2_1 = ((a & b) ==> c) ...... (.......... (..............)) ;;

(* On donne une nom d'exercice à cette proposition *)

let exo_2_1 = ("exo_2_1", prop_2_1) ;;

(* On prouve la proposition en DN à l'aide d'une ADP (arbre de preuve) *)

let adp = 
  (Adp.a_finir 1)
;;

verify_and_print [] "-html" adp exo_2_1 ;;


(* On formalise l'énoncé : 
   Proposition 2.2.  (A /\ (B \/ C)) ==> (A /\ B) \/ (A /\ C)
*)

let prop_2_2 = (...... (b || c)) ................................................ ;;

(* On donne une nom d'exercice à cette proposition *)

let exo_2_2 = ("exo_2_2", prop_2_2) ;;

(* On prouve la proposition en DN à l'aide d'une ADP (arbre de preuve) *)

let adp = 
  (Impl.intro "H1" 
     (Ou.elim 
	(Et.elim 2 (Hyp.apply "H1"))
	(Adp.a_finir 2)
	(Adp.a_finir 3)
     )
  ) 
;;

verify_and_print [] "-html" adp exo_2_2 ;;





