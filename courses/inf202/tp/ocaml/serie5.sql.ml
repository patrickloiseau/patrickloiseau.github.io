open Term
open Exercice

(* S�rie 5 - QUANTIFICATEURS ET DOUBLE NEGATION

  Prouvez en DN les propositions suivantes: 

   Proposition 5.1:  non( Ex(x, P x) ) ==> Qq(y, non (P y))

   Proposition 5.2:  non( Qq(x, P x) ) ==> Ex(y, non (P y))
*)



(* On d�clare une variable quantifi�e x pour �crire un pour_tout *)

let x = quantified_var "x" and y = quantified_var "y" ;;

(* On formalise l'�nonc� sous la forme d'une formule logique *)

let thm_5_1 = (non (Ex(x,Pred("P",[x])))) ==> Qq(y,non (Pred("P",[y]))) ;;

(* On donne une nom d'exercice � ce th�or�me *)

let exo_5_1 = ("exo_5_1", thm_5_1) ;;

(* On prouve le th�or�me en DN � l'aide d'une ADP (arbre de preuve) *)

let adp_5_1 =
  let y1 = fresh "y" in
    (Impl.intro "H1"
(Adp.a_finir 1)
    )
;;

(* On v�rifie que l'adp est bien une preuve et on l'affiche *)

verify_and_print [Ln.traduire_en_francais] "-html" adp_5_1 exo_5_1 ;;
      

(* EXERCICE 5.2

     Proposition 5.2:  non( Qq(x, P x) ) ==> Ex(y, non (P y))
*)

(* On formalise l'�nonc� sous la forme d'une formule logique *)

let thm_5_2 = (non ..........................................) ==> .................................................. ;;

(* On donne une nom d'exercice � ce th�or�me *)

let exo_5_2 = ("exo_5_2", thm_5_2) ;;

(* On prouve le th�or�me en DN � l'aide d'une ADP (arbre de preuve) *)


