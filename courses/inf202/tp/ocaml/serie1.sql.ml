(* SI VOUS TRAVAILLEZ sous emacs: 
   #load "prouveur.cmo" ;;
 *)

open Prouveur
open Term
open Exercice

(* exo_1_1 *

  Mod�lisez et prouvez en DN l'�nonc� suivant 

   Socrate est un homme
   Tous les hommes sont mortels
   donc Socrate est mortel.

*)

(* On d�clare une variable quantifi�e x pour �crire un pour_tout *)

let x = quantified_var "x" ;;

(* On formalise l'�nonc� sous la forme d'une formule logique � l'aide de pr�dicat Pred ..., de symboles S..., de conjonction &, d'implication ==>, de pour tout Qq *)

let thm_1_1 = ( Pred("H",[S "Socrate"]) & Qq(x , Pred("H",[x]) ==> Pred("M",[x])) ) ==> Pred("M",[S "Socrate"]) ;;

(* On donne une nom d'exercice � ce th�or�me *)

let exo_1_1 = ("exo_1_1", thm_1_1) ;;


(* On prouve le th�or�me en DN � l'aide d'une ADP (arbre de preuve) *)

let adp =
  (Impl.intro "H1" 
     (Impl.elim 
	(Et.elim1 
	   (Hyp.apply "H1") 
	) 
	(Qq.elim (S "Socrate")
           (Et.elim2 
	      (Hyp.apply "H1") 
	   )
	)
     )
  )
;; 

(* On v�rifie que l'adp est bien une preuve de l'exo_1_1 et on l'affiche *)

verify_and_print [] "-html" adp exo_1_1 ;;


(* Maintenant que vous avez vu l'objectif du TP,
   d�roulons les �tapes de la construction de l'arbre de preuve. 
   On proc�de comme en TD :
   - on construit l'arbre en remontant jusqu'� �tre bloqu�
   - puis on poursuit la construction de l'arbre en descendant 
     depuis les hypoth�ses
*)


(* �tape 1 de construction: on affiche ce que l'on doit prouver *)

print_string("\n\n �tape 1 de construction") ;;

let adp =
     (Adp.a_finir 1)
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 2 de construction :
   - on peut construire l'arbre en remontant 
*)

print_string("\n\n �tape 2 de construction") ;;

let adp =
  (Impl.intro "H1" 
     (Adp.a_finir 1)
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 3 de construction :
   - on est bloqu� ; on ne peut plus remonter
   - donc on constuit l'arbre en descendant
     depuis les hypoth�ses.
   
   /!\ REMARQUEZ QUE le prouver indique que la preuve est incorrecte.
   
   En effet, il pense que  Hyp.apply est ce qu'on propose comme  preuve de  M(Socrate)
   ce qui est incorrecte.

   Il faut dire au prouveur qu'on est en train de descendre et qu'il manque des pas de d�ductions 
   entre la partie montante de l'arbre et la partie descendante.

   On lui indique cela dans l'�tape suivante grace � : Adp.descendant
*)

print_string("\n\n �tape 3 de construction") ;;

let adp =
  (Impl.intro "H1" 
	(Hyp.apply "H1")
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 4 de construction :
   - L'arbre n'est toujours pas complet
     mais le prouveur accepte la partie descendante
     
   - il indique par une ligne de ################
     que l'on obtient pas ce qu'on devait montrer 
*)

print_string("\n\n �tape 4 de construction") ;;

let adp =
  (Impl.intro "H1" 
     (Adp.descendant
	(Hyp.apply "H1")
     )
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 5 de construction :
   - on effectue un pas de d�duction de plus 
     dans la partie descendante
*)

print_string("\n\n �tape 5 de construction") ;;

let adp =
  (Impl.intro "H1" 
     (Adp.descendant
	(Et.elim 1
	   (Hyp.apply "H1")
	)
     )
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 6 de construction :
   - on a tout a coup une intuition et 
     on d�cide de faire un pas de plus en remontant
     en appliquant la r�gle du  Impl.elim

   - le prouveur d�couvre et affiche ce qu'il faut alors montrer 
*)

print_string("\n\n �tape 6 de construction") ;;

let adp =
  (Impl.intro "H1" 
     (Impl.elim
	(Adp.descendant
	   (Et.elim 1
	      (Hyp.apply "H1")
	   )
	)
	(Adp.descendant
	   (Adp.a_finir 1)
	)
     )
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* �tape 7 de contruction :
   Maintenant que vous avez vu comment descendre et remonter
   � vous de finir l'arbre � l'aide des r�gles du fichier
   
     regle.ml

*)

print_string("\n\n �tape 7 de construction") ;;

let adp =
  (Impl.intro "H1" 
     (Impl.elim
	(Adp.descendant
	   (Et.elim 1
	      (Hyp.apply "H1")
	   )
	)
	(Adp.descendant
	   (Adp.a_finir 1)
	)
     )
  )
;;

verify_and_print [] "-html" adp exo_1_1 ;;


(* Pour sauvegarder l'arbre dans un fichier html
   utilisez verify_and_print avec "html" au lieu de "-html"
*)
   
verify_and_print [] "html" adp exo_1_1 ;;

(* Ouvrez le fichier exo_1_1.html avec un navigateur web pour voir le r�sultat *)




