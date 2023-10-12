open Prouveur
open Term
open Exercice
open Def

(* S�rie 3 -- ENSEMBLES

  Prouvez en DN les propositions suivantes: 

   Proposition 3.1:  l'ensemble vide est inclus dans tout ensemble

   Proposition 3.2:  A inclus B  /\ B inter C = {}  ==> A inter C = {}

   Proposition 3.3:  B inter C = {}  implique il n'existe pas d'�l�ment dans A inter B

   Proposition 3.4:  si A est inclus dans B et si B est inclus dans C alors A est inclus dans C

*)

(* DEFINITONS *)

(* On d�finit le symbole de l'ensemble vide *)

let vide = S "{}" ;;

(* On donne les d�finitions n�cessaires pour travailler sur des ensembles *)

let definitions_ensemble = 
  [
   ("{}", function [x] ->
	 ( Pred(":",[x;vide]) )
	   =$= 
	 False
   );

   ("inclus", function [e;f] ->
	 ( Pred("inclus",[e;f]) )
	   =$=
	 ( let x = quantified_var "x" in Qq(x, Impl(Pred(":",[x;e]) , Pred(":",[x;f]))) )
   );
    
   ("=ens=", function [e;f] ->
	 ( Pred("=ens=",[e;f]) )
	   =$=
	 ( Et(Pred("inclus",[e;f]), Pred("inclus",[f;e])) )
   );

   ("inter", function [e;f] -> let x = Term.unknown() in
     ( Pred(":",[x ; Op("inter",[e;f])]) )
       =$=
     ( Et( Pred(":",[x;e]) , Pred(":",[x;f])) )
   )
 ] ;;


(* On ajoute ces d�finitions aux d�finitions existantes *)

Def._definitions :=  definitions_ensemble @ !(Def._definitions) ;;


(* EXERCICE 3.1 *)

(*  On d�clare une variable quantifi�e pour formaliser l'�nonc� 3.1 *)

let e = quantified_var "E" ;;

(* On formalise l'�nonc� � l'aide 
   - du quantificateur  Qq(x, pr�dicat sur x)
   - du pr�dicat  Pred("inclus",[ens ; ens])

   Proposition 3.1: l'ensemble vide est inclus dans tout ensemble
*)

let prop_3_1 = Qq(e, Pred("inclus",[vide ; e])) ;;

(* On donne une nom d'exercice � cette proposition *)

let exo_3_1 = ("exo_3_1", prop_3_1) ;;

(* On prouve la proposition en DN � l'aide d'une ADP (arbre de preuve) *)

let adp_3_1 = 
  let e0 = fresh "E" 
  and x0 = fresh "x" in
    (Qq.auto_intro e0
       (Def.apply "inclus" [ vide ; e0 ]
	  (Adp.a_finir 1)
       )
    )
;;

verify_and_print [] "-html" adp_3_1 exo_3_1 ;;


(* On en fait un th�or�me pour le r�utiliser dans l'exercice 3.2 *)

let thm_3_1 = (adp_3_1, prop_3_1) ;;

(* Pour r�utiliser un th�or�me on utilise la commande: (Thm.apply thm_3_1)  *)



(* EXERCICE 3.2 *)

(* On d�clare des noms d'ensembles *)

let a = S("A") and b = S("B") and c = S("C") ;;

(* On formalise l'�nonc� � l'aide 
   - des pr�dicats  : Pred("inclus",[ ens ; ens ])   Pred("=ens=",[ ens ; ens ])
   - de l'op�rateur : Op("inter", [ ens ; ens ])
  
   Proposition 3.2.  A inclus B  /\ B inter C = {}  ==> A inter C = {}
*)

let prop_3_2 = 
   ( Pred("inclus",[......]) & Pred("=ens=", [ Op("inter",[......]) ; ........ ]) )
   ==> 
   ......................................................................................
;;

(* On donne une nom d'exercice � cette proposition *)

let exo_3_2 = ("exo_3_2", prop_3_2) ;;

(* On prouve la proposition en DN � l'aide d'une ADP (arbre de preuve) 

   Remarquez qu'on peut r�utiliser l'adp de l'exercice 3.1
   � condition que les hypoth�ses de adp_3_1 ne se confondent
   pas avec celle de l'adp_3_2
*)

let adp_3_2 =
  let x0 = fresh "X" in
    (Impl.intro "H1" 
       (Def.apply "=ens=" [ Op("inter",[a;c]) ; vide ]
	  (Adp.a_finir 1)
       )
    )
;;

verify_and_print [] "html" adp_3_2 exo_3_2 ;;




(* EXERCICE 3.3 *)

(*  On d�clare deux variables pour des ensembles E1 et E2 
   et une variable quantifi�e pour formaliser l'�nonc� 3.3 *)

let e1 = var "E1" and e2 = var "E2" and x = quantified_var "x" ;;

(* On formalise l'�nonc� � l'aide:
   - de l'op�rateur: Op("inter",[ens;ens])
   - du pr�cicat : =ens= 
   - du pr�cicat : appartient not�  Pred(":",[elt;ens])
   - du quantificateur Ex(x, pred x) 
   - de la n�gation: non
   
    Proposition 3.3:  E1 inter E2 = {}  implique il n'existe pas d'�l�ment dans E1 inter E2 
*)

let prop_3_3 = 
  ..........................................................................................
   ==> 
  ............................................................................................
;;

(* On donne une nom d'exercice � cette proposition *)

let exo_3_3 = ("exo_3_3", prop_3_3) ;;

(* On prouve la proposition en DN � l'aide d'une ADP (arbre de preuve) *)

let adp_3_3 = 
  (Adp.a_finir 1)
;;

verify_and_print [] "-html" adp_3_3 exo_3_3 ;;


(* EXERCICE 4.3 

   Prouvez en DN la proposition 

   Proposition 3.4:  si A est inclus dans B et si B est inclus dans C alors A est inclus dans C

*)



