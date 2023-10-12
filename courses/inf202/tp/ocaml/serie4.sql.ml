open Prouveur
open Term
open Exercice
open Def 

(* Série 4 - RELATIONS

  Prouvez en DN les propositions suivantes: 

   Proposition 4.1: Si la relation R est reflexive et si la relation S est reflexive 
                    alors la relation SoR est reflexive
*)

(* DEFINITONS *)

(*  On déclare deux relations R et S sur l'ensemble A afin de formaliser l'énoncé 4.1 *)

let r = (relation "R" "A" "A") ;;

let s = (relation "S" "A" "A") ;;

(* On definit la notation pour indiquer que "x est en relation r avec y" *)

let inrel = fun x r y -> Op("",[x;r;y]) ;;

let dans = fun x ens -> Op(":",[x;ens]) ;;

(* On donne les définitions de reflexive et de la composition de relation *)

let definitions_relations = 
  [    
       ("reflexive", function [ r ] -> let Pred("relation",[_;ensA;_]) = r in

	 ( Pred("reflexive",[r]) ) 
	   =$= 
	 ( let x = quantified_var "x" in Qq(x, Impl(dans x ensA, inrel x r x)) )
       ) ;

       ("composition", function [sor] -> let Pred("relation", [ Op(" o ",[s;r]) ; _ ; _ ]) = sor and x = unknown() and z = unknown() in

	 (inrel x sor z) 
	   =$=
	 (let y = quantified_var "y" in Ex(y, Et( inrel x s y , inrel y r z)))
       )
     ] ;;

(* On ajoute ces définitions aux définitions existantes *)

Def._definitions :=  definitions_relations @ !(Def._definitions) ;;


(* EXERCICE 4.1 *)

(* On formalise l'énoncé 4.1 à l'aide 
   - du prédicat: reflexive
   - de l'opérateur de composition: o  
     la notation SoR mathématique s'écrit (o s r) en ocaml 

   Proposition 4.1: Si la relation R est reflexive et si la relation S est reflexive 
                    alors la relation SoR est reflexive
*)

let prop_4_1 = ((reflexive r) & (reflexive s)) ==> (reflexive (o s r)) ;;

(* On donne une nom d'exercice à cette proposition *)

let exo_4_1 = ("exo_4_1", prop_4_1) ;;

(* On prouve la proposition en DN à l'aide d'une ADP (arbre de preuve) *)


let adp_4_1 =
  let x1 = fresh "x"
  in
    (Impl.intro "H1" 
       (Def.apply "reflexive" [ .............. ] 
(Adp.a_finir 1)
       )
    )
;;

verify_and_print [] "html" adp_4_1 exo_4_1 ;;






