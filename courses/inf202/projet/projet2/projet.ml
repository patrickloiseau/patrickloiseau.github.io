open Prouveur ;;
open Proof_tree ;;
open Term ;;
open Preuve ;;
open Exercice ;;


let rec (pretty_proof: proof_tree -> string) = fun preuve ->
      match preuve with
     (* HYP_apply  of hypotheses * hyp * conclusion *)
      |	HYP_apply(hypotheses,h,conclusion) -> "D'apr�s l'hypoht�se (" ^ h ^ "), on sait que " ^ (pretty ...) ^ "."
      |	_ -> "..."
;;


(* TEST *)

let (preuve_en_francais: theorem -> string) = fun theorem ->
      let (preuve,formule) = theorem in pretty_proof preuve
;;

let exo1_1 = ( "exo_1_1" , (((P "A") ==> ((P "A") ==> (P "B"))) ==> ((P "A") ==> (P "B"))) ) ;;

let adp1_1 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Impl.elim (Hyp.apply "H2") 
        (Impl.elim (Hyp.apply "H2") (Hyp.apply "H1")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp1_1 exo1_1 ;;

(*
      H2:A  H1:(A ==> (A ==> B))     
      __________________________ =>_e
H2:A  (A ==> B)                      
_____________________________________ =>_e
B
_________ =>_i [H2:A]
(A ==> B)
_________________________________ =>_i [H1:(A ==> (A ==> B))]
((A ==> (A ==> B)) ==> (A ==> B))


D�montrons ((A ==> (A ==> B)) ==> (A ==> B)) :
Pour cela, supposons (A ==> (A ==> B)) (hypoth�se [H1]) et montrons (A ==> B) 
  Pour cela, supposons A (hypoth�se [H2]) et montrons B 
    Puisqu'on a A d'apr�s [H2], il suffit de montrer (A ==> B) pour obtenir B. 
    (A ==> B) est une cons�quence directe des hypoth�ses H2: A et H1: (A ==> (A ==> B))

Ceci ach�ve la d�monstration de ((A ==> (A ==> B)) ==> (A ==> B))
*)

let exo1_2 = ( "exo_1_2" , (((P "A") ==> ((P "B") ==> (P "C"))) ==> (((P "A") ==> (P "B")) ==> ((P "A") ==> (P "C")))) ) ;;

let adp1_2 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Impl.intro "H3" 
        (Impl.elim 
          (Impl.elim (Hyp.apply "H3") (Hyp.apply "H2")
          ) 
          (Impl.elim (Hyp.apply "H3") (Hyp.apply "H1")
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp1_2 exo1_2 ;;


(*
H3:A  H2:(A ==> B)       H3:A  H1:(A ==> (B ==> C))     
__________________ =>_e  __________________________ =>_e
B                        (B ==> C)                      
________________________________________________________ =>_e
C
_________ =>_i [H3:A]
(A ==> C)
_________________________ =>_i [H2:(A ==> B)]
((A ==> B) ==> (A ==> C))
_________________________________________________ =>_i [H1:(A ==> (B ==> C))]
((A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C)))


D�montrons ((A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C))) :
Pour cela, supposons (A ==> (B ==> C)) (hypoth�se [H1]) et montrons ((A ==> B) ==> (A ==> C)) 
  Pour cela, supposons (A ==> B) (hypoth�se [H2]) et montrons (A ==> C) 
    Pour cela, supposons A (hypoth�se [H3]) et montrons C 
      Pour cela, on va montrer d'une part B et d'autre part (B ==> C)
      - B est une cons�quence directe des hypoth�ses H3: A et H2: (A ==> B)
      - (B ==> C) est une cons�quence directe des hypoth�ses H3: A et H1: (A ==> (B ==> C))

Ceci ach�ve la d�monstration de ((A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C)))
*)

let exo2_1 = ( "exo_2_1" , (((P "A") & (P "B")) ==> ((P "B") & (P "A"))) ) ;;

let adp2_1 = 
  (Impl.intro "H1" 
    (Et.intro 
      (Et.elim 2 (Hyp.apply "H1")
      ) 
      (Et.elim 1 (Hyp.apply "H1")
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_1 exo2_1 ;;


(*
H1:(A /\ B)         H1:(A /\ B)       
___________ /\_e 2  ___________ /\_e 1
B                   A                 
______________________________________ /\_i
(B /\ A)
_______________________ =>_i [H1:(A /\ B)]
((A /\ B) ==> (B /\ A))


D�montrons ((A /\ B) ==> (B /\ A)) :
Pour cela, supposons (A /\ B) (hypoth�se [H1]) et montrons (B /\ A) 
  1. B est la partie gauche de la conjonction (A /\ B)  
      qui correspond � l'hypoth�se [H1] 
  2. A est la partie droite de la conjonction (A /\ B)  
      qui correspond � l'hypoth�se [H1]

Ceci ach�ve la d�monstration de ((A /\ B) ==> (B /\ A))
*)

let exo2_2 = ( "exo_2_2" , (((P "A") & ((P "B") & (P "C"))) ==> (((P "A") & (P "B")) & (P "C"))) ) ;;

let adp2_2 = 
  (Impl.intro "H1" 
    (Et.intro 
      (Et.intro 
        (Et.elim 1 (Hyp.apply "H1")
        ) 
        (Et.elim 1 
          (Et.elim 2 (Hyp.apply "H1")
          )
        )
      ) 
      (Et.elim 2 
        (Et.elim 2 (Hyp.apply "H1")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_2 exo2_2 ;;


(*
                           H1:(A /\ (B /\ C))                                     
                           __________________ /\_e 2                              
H1:(A /\ (B /\ C))         (B /\ C)                        H1:(A /\ (B /\ C))       
__________________ /\_e 1  ________ /\_e 1                 __________________ /\_e 2
A                          B                               (B /\ C)                 
____________________________________________________ /\_i  ________ /\_e 2          
(A /\ B)                                                   C                        
____________________________________________________________________________________ /\_i
((A /\ B) /\ C)
_____________________________________ =>_i [H1:(A /\ (B /\ C))]
((A /\ (B /\ C)) ==> ((A /\ B) /\ C))


D�montrons ((A /\ (B /\ C)) ==> ((A /\ B) /\ C)) :
Pour cela, supposons (A /\ (B /\ C)) (hypoth�se [H1]) et montrons ((A /\ B) /\ C) 
  1. D�montrons (A /\ B) :
     1. A est la partie droite de la conjonction (A /\ (B /\ C))  
         qui correspond � l'hypoth�se [H1] 
     2. B est la partie droite de la conjonction (B /\ C)  
         qui est la partie gauche de la conjonction (A /\ (B /\ C))  
           qui correspond � l'hypoth�se [H1] 
   
  2. C est la partie gauche de la conjonction (B /\ C)  
      qui est la partie gauche de la conjonction (A /\ (B /\ C))  
        qui correspond � l'hypoth�se [H1]

Ceci ach�ve la d�monstration de ((A /\ (B /\ C)) ==> ((A /\ B) /\ C))
*)

let exo2_3 = ( "exo_2_3" , (((P "A") || (P "B")) ==> (((P "A") ==> (P "C")) ==> (((P "B") ==> (P "C")) ==> (P "C")))) ) ;;

let adp2_3 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Impl.intro "H3" 
        (Ou.elim (Hyp.apply "H1") (Hyp.apply "H2") (Hyp.apply "H3")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_3 exo2_3 ;;


(*
H1:(A \/ B)  H2:(A ==> C)  H3:(B ==> C)
_______________________________________ \/_e
C
_________________ =>_i [H3:(B ==> C)]
((B ==> C) ==> C)
_________________________________ =>_i [H2:(A ==> C)]
((A ==> C) ==> ((B ==> C) ==> C))
________________________________________________ =>_i [H1:(A \/ B)]
((A \/ B) ==> ((A ==> C) ==> ((B ==> C) ==> C)))


D�montrons ((A \/ B) ==> ((A ==> C) ==> ((B ==> C) ==> C))) :
Pour cela, supposons (A \/ B) (hypoth�se [H1]) et montrons ((A ==> C) ==> ((B ==> C) ==> C)) 
  Pour cela, supposons (A ==> C) (hypoth�se [H2]) et montrons ((B ==> C) ==> C) 
    Pour cela, supposons (B ==> C) (hypoth�se [H3]) et montrons C 
      Pour cela, exploitons (A \/ B)  
        qui correspond � l'hypoth�se [H1] 
      Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
      on doit donc prouver C dans chacun des cas : 
      - Cas 1: D�montrons (A ==> C) : c'est exactement l'hypoth�se [H2] 
      - Cas 2: D�montrons (B ==> C) : c'est exactement l'hypoth�se [H3]

Ceci ach�ve la d�monstration de ((A \/ B) ==> ((A ==> C) ==> ((B ==> C) ==> C)))
*)

let exo2_4 = ( "exo_2_4" , ((P "A") ==> ((P "A") || (P "B"))) ) ;;

let adp2_4 = 
  (Impl.intro "H1" 
    (Ou.intro 1 (Hyp.apply "H1")
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_4 exo2_4 ;;


(*
H1:A
________ \/_i
(A \/ B)
________________ =>_i [H1:A]
(A ==> (A \/ B))


D�montrons (A ==> (A \/ B)) :
Pour cela, supposons A (hypoth�se [H1]) et montrons (A \/ B) 
  Pour montrer (A \/ B) inutile de montrer B,
  on se contente de montrer A en remarquant que c'est exactement l'hypoth�se [H1]

Ceci ach�ve la d�monstration de (A ==> (A \/ B))
*)

let exo2_5 = ( "exo_2_5" , ((P "B") ==> ((P "A") || (P "B"))) ) ;;

let adp2_5 = 
  (Impl.intro "H1" 
    (Ou.intro 2 (Hyp.apply "H1")
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_5 exo2_5 ;;


(*
H1:B
________ \/_i
(A \/ B)
________________ =>_i [H1:B]
(B ==> (A \/ B))


D�montrons (B ==> (A \/ B)) :
Pour cela, supposons B (hypoth�se [H1]) et montrons (A \/ B) 
  Pour montrer (A \/ B) inutile de montrer A,
  on se contente de montrer B en remarquant que c'est exactement l'hypoth�se [H1]

Ceci ach�ve la d�monstration de (B ==> (A \/ B))
*)

let exo2_6 = ( "exo_2_6" , (((P "A") || (P "A")) ==> (P "A")) ) ;;

let adp2_6 = 
  (Impl.intro "H1" 
    (Ou.elim (Hyp.apply "H1") 
      (Impl.intro "H2" (Hyp.apply "H2")
      ) 
      (Impl.intro "H3" (Hyp.apply "H3")
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_6 exo2_6 ;;


(*
             H2:A                   H3:A                 
             _________ =>_i [H2:A]  _________ =>_i [H3:A]
H1:(A \/ A)  (A ==> A)              (A ==> A)            
_________________________________________________________ \/_e
A
________________ =>_i [H1:(A \/ A)]
((A \/ A) ==> A)


D�montrons ((A \/ A) ==> A) :
Pour cela, supposons (A \/ A) (hypoth�se [H1]) et montrons A 
  Pour cela, exploitons (A \/ A)  
    qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver A dans chacun des cas : 
  - Cas 1: D�montrons (A ==> A) :
        Pour cela, supposons A (hypoth�se [H2]) et montrons A  c'est exactement l'hypoth�se [H2] 
      
  - Cas 2: D�montrons (A ==> A) :
        Pour cela, supposons A (hypoth�se [H3]) et montrons A  c'est exactement l'hypoth�se [H3] 
     

Ceci ach�ve la d�monstration de ((A \/ A) ==> A)
*)

let exo2_7 = ( "exo_2_7" , ((((P "A") || (P "B")) ==> (P "C")) ==> ((P "A") ==> (P "C"))) ) ;;

let adp2_7 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Impl.elim 
        (Ou.intro 1 (Hyp.apply "H2")
        ) (Hyp.apply "H1")
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_7 exo2_7 ;;


(*
H2:A                            
________ \/_i                   
(A \/ B)       H1:((A \/ B) ==> C)
__________________________________ =>_e
C
_________ =>_i [H2:A]
(A ==> C)
________________________________ =>_i [H1:((A \/ B) ==> C)]
(((A \/ B) ==> C) ==> (A ==> C))


D�montrons (((A \/ B) ==> C) ==> (A ==> C)) :
Pour cela, supposons ((A \/ B) ==> C) (hypoth�se [H1]) et montrons (A ==> C) 
  Pour cela, supposons A (hypoth�se [H2]) et montrons C 
    Puisqu'on a ((A \/ B) ==> C) d'apr�s [H1], il suffit de montrer (A \/ B) pour obtenir C. 
    
    Pour montrer (A \/ B) inutile de montrer B,
    on se contente de montrer A en remarquant que c'est exactement l'hypoth�se [H2]

Ceci ach�ve la d�monstration de (((A \/ B) ==> C) ==> (A ==> C))
*)

let exo2_8 = ( "exo_2_8" , ((((P "A") || (P "B")) ==> (P "C")) ==> (((P "A") ==> (P "C")) & ((P "B") ==> (P "C")))) ) ;;

let adp2_8 = 
  (Impl.intro "H1" 
    (Et.intro 
      (Impl.intro "H2" 
        (Impl.elim 
          (Ou.intro 1 (Hyp.apply "H2")
          ) (Hyp.apply "H1")
        )
      ) 
      (Impl.intro "H3" 
        (Impl.elim 
          (Ou.intro 2 (Hyp.apply "H3")
          ) (Hyp.apply "H1")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_8 exo2_8 ;;


(*
H2:A                                     H3:B                                   
________ \/_i                            ________ \/_i                          
(A \/ B)       H1:((A \/ B) ==> C)       (A \/ B)       H1:((A \/ B) ==> C)     
__________________________________ =>_e  __________________________________ =>_e
C                                        C                                      
_________ =>_i [H2:A]                    _________ =>_i [H3:B]                  
(A ==> C)                                (B ==> C)                              
________________________________________________________________________________ /\_i
((A ==> C) /\ (B ==> C))
_______________________________________________ =>_i [H1:((A \/ B) ==> C)]
(((A \/ B) ==> C) ==> ((A ==> C) /\ (B ==> C)))


D�montrons (((A \/ B) ==> C) ==> ((A ==> C) /\ (B ==> C))) :
Pour cela, supposons ((A \/ B) ==> C) (hypoth�se [H1]) et montrons ((A ==> C) /\ (B ==> C)) 
  1. D�montrons (A ==> C) :
     Pour cela, supposons A (hypoth�se [H2]) et montrons C 
       Puisqu'on a ((A \/ B) ==> C) d'apr�s [H1], il suffit de montrer (A \/ B) pour obtenir C. 
       
       Pour montrer (A \/ B) inutile de montrer B,
       on se contente de montrer A en remarquant que c'est exactement l'hypoth�se [H2] 
   
  2. D�montrons (B ==> C) :
     Pour cela, supposons B (hypoth�se [H3]) et montrons C 
       Puisqu'on a ((A \/ B) ==> C) d'apr�s [H1], il suffit de montrer (A \/ B) pour obtenir C. 
       
       Pour montrer (A \/ B) inutile de montrer A,
       on se contente de montrer B en remarquant que c'est exactement l'hypoth�se [H3] 
  

Ceci ach�ve la d�monstration de (((A \/ B) ==> C) ==> ((A ==> C) /\ (B ==> C)))
*)

let exo2_9_1 = ( "exo_2_9_1" , (((P "A") ==> (P "C")) ==> (((P "B") ==> (P "C")) ==> (((P "A") || (P "B")) ==> (P "C")))) ) ;;

let adp2_9_1 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Impl.intro "H3" 
        (Ou.elim (Hyp.apply "H3") (Hyp.apply "H1") (Hyp.apply "H2")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_9_1 exo2_9_1 ;;


(*
H3:(A \/ B)  H1:(A ==> C)  H2:(B ==> C)
_______________________________________ \/_e
C
________________ =>_i [H3:(A \/ B)]
((A \/ B) ==> C)
________________________________ =>_i [H2:(B ==> C)]
((B ==> C) ==> ((A \/ B) ==> C))
________________________________________________ =>_i [H1:(A ==> C)]
((A ==> C) ==> ((B ==> C) ==> ((A \/ B) ==> C)))


D�montrons ((A ==> C) ==> ((B ==> C) ==> ((A \/ B) ==> C))) :
Pour cela, supposons (A ==> C) (hypoth�se [H1]) et montrons ((B ==> C) ==> ((A \/ B) ==> C)) 
  Pour cela, supposons (B ==> C) (hypoth�se [H2]) et montrons ((A \/ B) ==> C) 
    Pour cela, supposons (A \/ B) (hypoth�se [H3]) et montrons C 
      Pour cela, exploitons (A \/ B)  
        qui correspond � l'hypoth�se [H3] 
      Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
      on doit donc prouver C dans chacun des cas : 
      - Cas 1: D�montrons (A ==> C) : c'est exactement l'hypoth�se [H1] 
      - Cas 2: D�montrons (B ==> C) : c'est exactement l'hypoth�se [H2]

Ceci ach�ve la d�monstration de ((A ==> C) ==> ((B ==> C) ==> ((A \/ B) ==> C)))
*)

let exo2_9_2 = ( "exo_2_9_2" , ((((P "A") ==> (P "C")) & (((P "B") ==> (P "C")) & ((P "A") || (P "B")))) ==> (P "C")) ) ;;

let adp2_9_2 = 
  (Impl.intro "H1" 
    (Ou.elim 
      (Et.elim 2 
        (Et.elim 2 (Hyp.apply "H1")
        )
      ) 
      (Et.elim 1 (Hyp.apply "H1")
      ) 
      (Et.elim 1 
        (Et.elim 2 (Hyp.apply "H1")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_9_2 exo2_9_2 ;;


(*
H1:((A ==> C) /\ ((B ==> C) /\ (A \/ B)))                                                           H1:((A ==> C) /\ ((B ==> C) /\ (A \/ B)))       
_________________________________________ /\_e 2                                                    _________________________________________ /\_e 2
((B ==> C) /\ (A \/ B))                           H1:((A ==> C) /\ ((B ==> C) /\ (A \/ B)))         ((B ==> C) /\ (A \/ B))                         
_______________________ /\_e 2                    _________________________________________ /\_e 1  _______________________ /\_e 1                  
(A \/ B)                                          (A ==> C)                                         (B ==> C)                                       
____________________________________________________________________________________________________________________________________________________ \/_e
C
______________________________________________ =>_i [H1:((A ==> C) /\ ((B ==> C) /\ (A \/ B)))]
(((A ==> C) /\ ((B ==> C) /\ (A \/ B))) ==> C)


D�montrons (((A ==> C) /\ ((B ==> C) /\ (A \/ B))) ==> C) :
Pour cela, supposons ((A ==> C) /\ ((B ==> C) /\ (A \/ B))) (hypoth�se [H1]) et montrons C 
  Pour cela, exploitons (A \/ B)  
    qui est la partie gauche de la conjonction ((B ==> C) /\ (A \/ B))  
      qui est la partie gauche de la conjonction ((A ==> C) /\ ((B ==> C) /\ (A \/ B)))  
        qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver C dans chacun des cas : 
  - Cas 1: D�montrons (A ==> C) : 
       c'est la partie droite de la conjonction ((A ==> C) /\ ((B ==> C) /\ (A \/ B)))  
         qui correspond � l'hypoth�se [H1] 
  - Cas 2: D�montrons (B ==> C) : 
       c'est la partie droite de la conjonction ((B ==> C) /\ (A \/ B))  
         qui est la partie gauche de la conjonction ((A ==> C) /\ ((B ==> C) /\ (A \/ B)))  
           qui correspond � l'hypoth�se [H1]

Ceci ach�ve la d�monstration de (((A ==> C) /\ ((B ==> C) /\ (A \/ B))) ==> C)
*)

let exo2_9_3 = ( "exo_2_9_3" , ((((P "A") || (P "B")) & (((P "A") ==> (P "C")) & ((P "B") ==> (P "C")))) ==> (P "C")) ) ;;

let adp2_9_3 = 
  (Impl.intro "H1" 
    (Ou.elim 
      (Et.elim 1 (Hyp.apply "H1")
      ) 
      (Impl.intro "H2" 
        (Impl.elim (Hyp.apply "H2") 
          (Et.elim 1 
            (Et.elim 2 (Hyp.apply "H1")
            )
          )
        )
      ) 
      (Impl.intro "H3" 
        (Impl.elim (Hyp.apply "H3") 
          (Et.elim 2 
            (Et.elim 2 (Hyp.apply "H1")
            )
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_9_3 exo2_9_3 ;;


(*
                                                        H1:((A \/ B) /\ ((A ==> C) /\ (B ==> C)))                    H1:((A \/ B) /\ ((A ==> C) /\ (B ==> C)))            
                                                        _________________________________________ /\_e 2             _________________________________________ /\_e 2     
                                                        ((A ==> C) /\ (B ==> C))                                     ((A ==> C) /\ (B ==> C))                             
                                                        ________________________ /\_e 1                              ________________________ /\_e 2                      
                                                  H2:A  (A ==> C)                                              H3:B  (B ==> C)                                            
                                                  ______________________________________________________ =>_e  ______________________________________________________ =>_e
H1:((A \/ B) /\ ((A ==> C) /\ (B ==> C)))         C                                                            C                                                          
_________________________________________ /\_e 1  _________ =>_i [H2:A]                                        _________ =>_i [H3:B]                                      
(A \/ B)                                          (A ==> C)                                                    (B ==> C)                                                  
__________________________________________________________________________________________________________________________________________________________________________ \/_e
C
______________________________________________ =>_i [H1:((A \/ B) /\ ((A ==> C) /\ (B ==> C)))]
(((A \/ B) /\ ((A ==> C) /\ (B ==> C))) ==> C)


D�montrons (((A \/ B) /\ ((A ==> C) /\ (B ==> C))) ==> C) :
Pour cela, supposons ((A \/ B) /\ ((A ==> C) /\ (B ==> C))) (hypoth�se [H1]) et montrons C 
  Pour cela, exploitons (A \/ B)  
    qui est la partie droite de la conjonction ((A \/ B) /\ ((A ==> C) /\ (B ==> C)))  
      qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver C dans chacun des cas : 
  - Cas 1: D�montrons (A ==> C) :
        Pour cela, supposons A (hypoth�se [H2]) et montrons C 
          Puisqu'on a A d'apr�s [H2], il suffit de montrer (A ==> C) pour obtenir C. 
           
          qui est la partie droite de la conjonction ((A ==> C) /\ (B ==> C))  
            qui est la partie gauche de la conjonction ((A \/ B) /\ ((A ==> C) /\ (B ==> C)))  
              qui correspond � l'hypoth�se [H1] 
      
  - Cas 2: D�montrons (B ==> C) :
        Pour cela, supposons B (hypoth�se [H3]) et montrons C 
          Puisqu'on a B d'apr�s [H3], il suffit de montrer (B ==> C) pour obtenir C. 
           
          qui est la partie gauche de la conjonction ((A ==> C) /\ (B ==> C))  
            qui est la partie gauche de la conjonction ((A \/ B) /\ ((A ==> C) /\ (B ==> C)))  
              qui correspond � l'hypoth�se [H1] 
     

Ceci ach�ve la d�monstration de (((A \/ B) /\ ((A ==> C) /\ (B ==> C))) ==> C)
*)

let exo2_13 = ( "exo_2_13" , ((((P "A") & (P "C")) || ((P "B") & (P "C"))) ==> (((P "A") || (P "B")) & (P "C"))) ) ;;

let adp2_13 = 
  (Impl.intro "H1" 
    (Et.intro 
      (Ou.elim (Hyp.apply "H1") 
        (Impl.intro "H5" 
          (Ou.intro 1 
            (Et.elim 1 (Hyp.apply "H5")
            )
          )
        ) 
        (Impl.intro "H6" 
          (Ou.intro 2 
            (Et.elim 1 (Hyp.apply "H6")
            )
          )
        )
      ) 
      (Ou.elim (Hyp.apply "H1") 
        (Impl.intro "H7" 
          (Et.elim 2 (Hyp.apply "H7")
          )
        ) 
        (Impl.intro "H8" 
          (Et.elim 2 (Hyp.apply "H8")
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_13 exo2_13 ;;


(*
                           H5:(A /\ C)                                 H6:(B /\ C)                                                                                                                                            
                           ___________ /\_e 1                          ___________ /\_e 1                                                                                                                                     
                           A                                           B                                                                           H7:(A /\ C)                          H8:(B /\ C)                             
                           ________ \/_i                               ________ \/_i                                                               ___________ /\_e 2                   ___________ /\_e 2                      
                           (A \/ B)                                    (A \/ B)                                                                    C                                    C                                       
                           _______________________ =>_i [H5:(A /\ C)]  _______________________ =>_i [H6:(B /\ C)]                                  ________________ =>_i [H7:(A /\ C)]  ________________ =>_i [H8:(B /\ C)]     
H1:((A /\ C) \/ (B /\ C))  ((A /\ C) ==> (A \/ B))                     ((B /\ C) ==> (A \/ B))                          H1:((A /\ C) \/ (B /\ C))  ((A /\ C) ==> C)                     ((B /\ C) ==> C)                        
_________________________________________________________________________________________________________________ \/_e  ___________________________________________________________________________________________________ \/_e
(A \/ B)                                                                                                                C                                                                                                       
________________________________________________________________________________________________________________________________________________________________________________________________________________________________ /\_i
((A \/ B) /\ C)
____________________________________________ =>_i [H1:((A /\ C) \/ (B /\ C))]
(((A /\ C) \/ (B /\ C)) ==> ((A \/ B) /\ C))


D�montrons (((A /\ C) \/ (B /\ C)) ==> ((A \/ B) /\ C)) :
Pour cela, supposons ((A /\ C) \/ (B /\ C)) (hypoth�se [H1]) et montrons ((A \/ B) /\ C) 
  1. D�montrons (A \/ B) :
     Pour cela, exploitons ((A /\ C) \/ (B /\ C))  
       qui correspond � l'hypoth�se [H1] 
     Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
     on doit donc prouver (A \/ B) dans chacun des cas : 
     - Cas 1: D�montrons ((A /\ C) ==> (A \/ B)) :
           Pour cela, supposons (A /\ C) (hypoth�se [H5]) et montrons (A \/ B) 
             Pour montrer (A \/ B) inutile de montrer B,
             on se contente de montrer A en remarquant que est la partie droite de la conjonction (A /\ C)  
               qui correspond � l'hypoth�se [H5] 
         
     - Cas 2: D�montrons ((B /\ C) ==> (A \/ B)) :
           Pour cela, supposons (B /\ C) (hypoth�se [H6]) et montrons (A \/ B) 
             Pour montrer (A \/ B) inutile de montrer A,
             on se contente de montrer B en remarquant que est la partie droite de la conjonction (B /\ C)  
               qui correspond � l'hypoth�se [H6] 
         
   
  2. D�montrons C :
     Pour cela, exploitons ((A /\ C) \/ (B /\ C))  
       qui correspond � l'hypoth�se [H1] 
     Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
     on doit donc prouver C dans chacun des cas : 
     - Cas 1: D�montrons ((A /\ C) ==> C) :
           Pour cela, supposons (A /\ C) (hypoth�se [H7]) et montrons C  est la partie gauche de la conjonction (A /\ C)  
               qui correspond � l'hypoth�se [H7] 
         
     - Cas 2: D�montrons ((B /\ C) ==> C) :
           Pour cela, supposons (B /\ C) (hypoth�se [H8]) et montrons C  est la partie gauche de la conjonction (B /\ C)  
               qui correspond � l'hypoth�se [H8] 
         
  

Ceci ach�ve la d�monstration de (((A /\ C) \/ (B /\ C)) ==> ((A \/ B) /\ C))
*)

let exo2_14 = ( "exo_2_14" , ((((P "A") || (P "B")) & (P "C")) ==> (((P "A") & (P "C")) || ((P "B") & (P "C")))) ) ;;

let adp2_14 = 
  (Impl.intro "H1" 
    (Ou.elim 
      (Et.elim 1 (Hyp.apply "H1")
      ) 
      (Impl.intro "H44" 
        (Ou.intro 1 
          (Et.intro (Hyp.apply "H44") 
            (Et.elim 2 (Hyp.apply "H1")
            )
          )
        )
      ) 
      (Impl.intro "H56" 
        (Ou.intro 2 
          (Et.intro (Hyp.apply "H56") 
            (Et.elim 2 (Hyp.apply "H1")
            )
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_14 exo2_14 ;;


(*
                                  H1:((A \/ B) /\ C)                           H1:((A \/ B) /\ C)                  
                                  __________________ /\_e 2                    __________________ /\_e 2           
                           H44:A  C                                     H56:B  C                                   
                           ________________________________ /\_i        ________________________________ /\_i      
                           (A /\ C)                                     (B /\ C)                                   
                           ______________________ \/_i                  ______________________ \/_i                
H1:((A \/ B) /\ C)         ((A /\ C) \/ (B /\ C))                       ((A /\ C) \/ (B /\ C))                     
__________________ /\_e 1  ______________________________ =>_i [H44:A]  ______________________________ =>_i [H56:B]
(A \/ B)                   (A ==> ((A /\ C) \/ (B /\ C)))               (B ==> ((A /\ C) \/ (B /\ C)))             
___________________________________________________________________________________________________________________ \/_e
((A /\ C) \/ (B /\ C))
____________________________________________ =>_i [H1:((A \/ B) /\ C)]
(((A \/ B) /\ C) ==> ((A /\ C) \/ (B /\ C)))


D�montrons (((A \/ B) /\ C) ==> ((A /\ C) \/ (B /\ C))) :
Pour cela, supposons ((A \/ B) /\ C) (hypoth�se [H1]) et montrons ((A /\ C) \/ (B /\ C)) 
  Pour cela, exploitons (A \/ B)  
    qui est la partie droite de la conjonction ((A \/ B) /\ C)  
      qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver ((A /\ C) \/ (B /\ C)) dans chacun des cas : 
  - Cas 1: D�montrons (A ==> ((A /\ C) \/ (B /\ C))) :
        Pour cela, supposons A (hypoth�se [H44]) et montrons ((A /\ C) \/ (B /\ C)) 
          Pour cela, il suffit de montrer l'un des deux termes de la disjonction.
          D�montrons (A /\ C) :
             1. A correspond � l'hypoth�se [H44] 
             2. C est la partie gauche de la conjonction ((A \/ B) /\ C)  
                 qui correspond � l'hypoth�se [H1] 
      
  - Cas 2: D�montrons (B ==> ((A /\ C) \/ (B /\ C))) :
        Pour cela, supposons B (hypoth�se [H56]) et montrons ((A /\ C) \/ (B /\ C)) 
          Pour cela, il suffit de montrer l'un des deux termes de la disjonction.
          D�montrons (B /\ C) :
             1. B correspond � l'hypoth�se [H56] 
             2. C est la partie gauche de la conjonction ((A \/ B) /\ C)  
                 qui correspond � l'hypoth�se [H1] 
     

Ceci ach�ve la d�monstration de (((A \/ B) /\ C) ==> ((A /\ C) \/ (B /\ C)))
*)

let exo2_15 = ( "exo_2_15" , ((((P "A") & (P "B")) || (P "C")) ==> (((P "A") || (P "C")) & ((P "B") || (P "C")))) ) ;;

let adp2_15 = 
  (Impl.intro "H1" 
    (Et.intro 
      (Ou.elim (Hyp.apply "H1") 
        (Impl.intro "H5" 
          (Ou.intro 1 
            (Et.elim 1 (Hyp.apply "H5")
            )
          )
        ) 
        (Impl.intro "H6" 
          (Ou.intro 2 (Hyp.apply "H6")
          )
        )
      ) 
      (Ou.elim (Hyp.apply "H1") 
        (Impl.intro "H10" 
          (Ou.intro 1 
            (Et.elim 2 (Hyp.apply "H10")
            )
          )
        ) 
        (Impl.intro "H11" 
          (Ou.intro 2 (Hyp.apply "H11")
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_15 exo2_15 ;;


(*
                    H5:(A /\ B)                                                                                        H10:(A /\ B)                                                                   
                    ___________ /\_e 1                                                                                 ____________ /\_e 2                                                            
                    A                                           H6:C                                                   B                                            H11:C                             
                    ________ \/_i                               ________ \/_i                                          ________ \/_i                                ________ \/_i                     
                    (A \/ C)                                    (A \/ C)                                               (B \/ C)                                     (B \/ C)                          
                    _______________________ =>_i [H5:(A /\ B)]  ________________ =>_i [H6:C]                           _______________________ =>_i [H10:(A /\ B)]  ________________ =>_i [H11:C]     
H1:((A /\ B) \/ C)  ((A /\ B) ==> (A \/ C))                     (C ==> (A \/ C))                   H1:((A /\ B) \/ C)  ((A /\ B) ==> (B \/ C))                      (C ==> (B \/ C))                  
____________________________________________________________________________________________ \/_e  ______________________________________________________________________________________________ \/_e
(A \/ C)                                                                                           (B \/ C)                                                                                           
______________________________________________________________________________________________________________________________________________________________________________________________________ /\_i
((A \/ C) /\ (B \/ C))
____________________________________________ =>_i [H1:((A /\ B) \/ C)]
(((A /\ B) \/ C) ==> ((A \/ C) /\ (B \/ C)))


D�montrons (((A /\ B) \/ C) ==> ((A \/ C) /\ (B \/ C))) :
Pour cela, supposons ((A /\ B) \/ C) (hypoth�se [H1]) et montrons ((A \/ C) /\ (B \/ C)) 
  1. D�montrons (A \/ C) :
     Pour cela, exploitons ((A /\ B) \/ C)  
       qui correspond � l'hypoth�se [H1] 
     Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
     on doit donc prouver (A \/ C) dans chacun des cas : 
     - Cas 1: D�montrons ((A /\ B) ==> (A \/ C)) :
           Pour cela, supposons (A /\ B) (hypoth�se [H5]) et montrons (A \/ C) 
             Pour montrer (A \/ C) inutile de montrer C,
             on se contente de montrer A en remarquant que est la partie droite de la conjonction (A /\ B)  
               qui correspond � l'hypoth�se [H5] 
         
     - Cas 2: D�montrons (C ==> (A \/ C)) :
           Pour cela, supposons C (hypoth�se [H6]) et montrons (A \/ C) 
             Pour montrer (A \/ C) inutile de montrer A,
             on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H6] 
         
   
  2. D�montrons (B \/ C) :
     Pour cela, exploitons ((A /\ B) \/ C)  
       qui correspond � l'hypoth�se [H1] 
     Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
     on doit donc prouver (B \/ C) dans chacun des cas : 
     - Cas 1: D�montrons ((A /\ B) ==> (B \/ C)) :
           Pour cela, supposons (A /\ B) (hypoth�se [H10]) et montrons (B \/ C) 
             Pour montrer (B \/ C) inutile de montrer C,
             on se contente de montrer B en remarquant que est la partie gauche de la conjonction (A /\ B)  
               qui correspond � l'hypoth�se [H10] 
         
     - Cas 2: D�montrons (C ==> (B \/ C)) :
           Pour cela, supposons C (hypoth�se [H11]) et montrons (B \/ C) 
             Pour montrer (B \/ C) inutile de montrer B,
             on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H11] 
         
  

Ceci ach�ve la d�monstration de (((A /\ B) \/ C) ==> ((A \/ C) /\ (B \/ C)))
*)

let exo2_16_1 = ( "exo_2_16_1" , (((P "A") || (P "C")) ==> (((P "B") || (P "C")) ==> (((P "A") & (P "B")) || (P "C")))) ) ;;

let adp2_16_1 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Ou.elim (Hyp.apply "H2") 
        (Impl.intro "H77" 
          (Ou.elim (Hyp.apply "H1") 
            (Impl.intro "H101" 
              (Ou.intro 1 
                (Et.intro (Hyp.apply "H101") (Hyp.apply "H77")
                )
              )
            ) 
            (Impl.intro "H102" 
              (Ou.intro 2 (Hyp.apply "H102")
              )
            )
          )
        ) 
        (Impl.intro "H202" 
          (Ou.intro 2 (Hyp.apply "H202")
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_16_1 exo2_16_1 ;;


(*
                          H101:A  H77:B                                                                                                           
                          _____________ /\_i                                                                                                      
                          (A /\ B)                               H102:C                                                                           
                          _______________ \/_i                   _______________ \/_i                                                             
                          ((A /\ B) \/ C)                        ((A /\ B) \/ C)                                                                  
                          _______________________ =>_i [H101:A]  _______________________ =>_i [H102:C]                                            
             H1:(A \/ C)  (A ==> ((A /\ B) \/ C))                (C ==> ((A /\ B) \/ C))                     H202:C                               
             _________________________________________________________________________________________ \/_e  _______________ \/_i                 
             ((A /\ B) \/ C)                                                                                 ((A /\ B) \/ C)                      
             _______________________ =>_i [H77:B]                                                            _______________________ =>_i [H202:C]
H2:(B \/ C)  (B ==> ((A /\ B) \/ C))                                                                         (C ==> ((A /\ B) \/ C))              
__________________________________________________________________________________________________________________________________________________ \/_e
((A /\ B) \/ C)
______________________________ =>_i [H2:(B \/ C)]
((B \/ C) ==> ((A /\ B) \/ C))
_____________________________________________ =>_i [H1:(A \/ C)]
((A \/ C) ==> ((B \/ C) ==> ((A /\ B) \/ C)))


D�montrons ((A \/ C) ==> ((B \/ C) ==> ((A /\ B) \/ C))) :
Pour cela, supposons (A \/ C) (hypoth�se [H1]) et montrons ((B \/ C) ==> ((A /\ B) \/ C)) 
  Pour cela, supposons (B \/ C) (hypoth�se [H2]) et montrons ((A /\ B) \/ C) 
    Pour cela, exploitons (B \/ C)  
      qui correspond � l'hypoth�se [H2] 
    Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
    on doit donc prouver ((A /\ B) \/ C) dans chacun des cas : 
    - Cas 1: D�montrons (B ==> ((A /\ B) \/ C)) :
          Pour cela, supposons B (hypoth�se [H77]) et montrons ((A /\ B) \/ C) 
            Pour cela, exploitons (A \/ C)  
              qui correspond � l'hypoth�se [H1] 
            Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
            on doit donc prouver ((A /\ B) \/ C) dans chacun des cas : 
            - Cas 1: D�montrons (A ==> ((A /\ B) \/ C)) :
                  Pour cela, supposons A (hypoth�se [H101]) et montrons ((A /\ B) \/ C) 
                    Pour cela, il suffit de montrer l'un des deux termes de la disjonction.
                    D�montrons (A /\ B) :
                       1. A correspond � l'hypoth�se [H101] 
                       2. B correspond � l'hypoth�se [H77] 
                
            - Cas 2: D�montrons (C ==> ((A /\ B) \/ C)) :
                  Pour cela, supposons C (hypoth�se [H102]) et montrons ((A /\ B) \/ C) 
                    Pour montrer ((A /\ B) \/ C) inutile de montrer (A /\ B),
                    on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H102] 
                
        
    - Cas 2: D�montrons (C ==> ((A /\ B) \/ C)) :
          Pour cela, supposons C (hypoth�se [H202]) et montrons ((A /\ B) \/ C) 
            Pour montrer ((A /\ B) \/ C) inutile de montrer (A /\ B),
            on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H202] 
       

Ceci ach�ve la d�monstration de ((A \/ C) ==> ((B \/ C) ==> ((A /\ B) \/ C)))
*)

let exo2_16_2 = ( "exo_2_16_2" , ((((P "A") || (P "C")) & ((P "B") || (P "C"))) ==> (((P "A") & (P "B")) || (P "C"))) ) ;;

let adp2_16_2 = 
  (Impl.intro "H1" 
    (Ou.elim 
      (Et.elim 1 (Hyp.apply "H1")
      ) 
      (Impl.intro "H975" 
        (Ou.elim 
          (Et.elim 2 (Hyp.apply "H1")
          ) 
          (Impl.intro "H8008" 
            (Ou.intro 1 
              (Et.intro (Hyp.apply "H975") (Hyp.apply "H8008")
              )
            )
          ) 
          (Impl.intro "H9010" 
            (Ou.intro 2 (Hyp.apply "H9010")
            )
          )
        )
      ) 
      (Impl.intro "H9017" 
        (Ou.intro 2 (Hyp.apply "H9017")
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_16_2 exo2_16_2 ;;


(*
                                                                    H975:A  H8008:B                                                                                                            
                                                                    _______________ /\_i                                                                                                       
                                                                    (A /\ B)                                H9010:C                                                                            
                                                                    _______________ \/_i                    _______________ \/_i                                                               
                                  H1:((A \/ C) /\ (B \/ C))         ((A /\ B) \/ C)                         ((A /\ B) \/ C)                                                                    
                                  _________________________ /\_e 2  _______________________ =>_i [H8008:B]  _______________________ =>_i [H9010:C]                                             
                                  (B \/ C)                          (B ==> ((A /\ B) \/ C))                 (C ==> ((A /\ B) \/ C))                      H9017:C                               
                                  ________________________________________________________________________________________________________________ \/_e  _______________ \/_i                  
H1:((A \/ C) /\ (B \/ C))         ((A /\ B) \/ C)                                                                                                        ((A /\ B) \/ C)                       
_________________________ /\_e 1  _______________________ =>_i [H975:A]                                                                                  _______________________ =>_i [H9017:C]
(A \/ C)                          (A ==> ((A /\ B) \/ C))                                                                                                (C ==> ((A /\ B) \/ C))               
_______________________________________________________________________________________________________________________________________________________________________________________________ \/_e
((A /\ B) \/ C)
____________________________________________ =>_i [H1:((A \/ C) /\ (B \/ C))]
(((A \/ C) /\ (B \/ C)) ==> ((A /\ B) \/ C))


D�montrons (((A \/ C) /\ (B \/ C)) ==> ((A /\ B) \/ C)) :
Pour cela, supposons ((A \/ C) /\ (B \/ C)) (hypoth�se [H1]) et montrons ((A /\ B) \/ C) 
  Pour cela, exploitons (A \/ C)  
    qui est la partie droite de la conjonction ((A \/ C) /\ (B \/ C))  
      qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver ((A /\ B) \/ C) dans chacun des cas : 
  - Cas 1: D�montrons (A ==> ((A /\ B) \/ C)) :
        Pour cela, supposons A (hypoth�se [H975]) et montrons ((A /\ B) \/ C) 
          Pour cela, exploitons (B \/ C)  
            qui est la partie gauche de la conjonction ((A \/ C) /\ (B \/ C))  
              qui correspond � l'hypoth�se [H1] 
          Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
          on doit donc prouver ((A /\ B) \/ C) dans chacun des cas : 
          - Cas 1: D�montrons (B ==> ((A /\ B) \/ C)) :
                Pour cela, supposons B (hypoth�se [H8008]) et montrons ((A /\ B) \/ C) 
                  Pour cela, il suffit de montrer l'un des deux termes de la disjonction.
                  D�montrons (A /\ B) :
                     1. A correspond � l'hypoth�se [H975] 
                     2. B correspond � l'hypoth�se [H8008] 
              
          - Cas 2: D�montrons (C ==> ((A /\ B) \/ C)) :
                Pour cela, supposons C (hypoth�se [H9010]) et montrons ((A /\ B) \/ C) 
                  Pour montrer ((A /\ B) \/ C) inutile de montrer (A /\ B),
                  on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H9010] 
              
      
  - Cas 2: D�montrons (C ==> ((A /\ B) \/ C)) :
        Pour cela, supposons C (hypoth�se [H9017]) et montrons ((A /\ B) \/ C) 
          Pour montrer ((A /\ B) \/ C) inutile de montrer (A /\ B),
          on se contente de montrer C en remarquant que c'est exactement l'hypoth�se [H9017] 
     

Ceci ach�ve la d�monstration de (((A \/ C) /\ (B \/ C)) ==> ((A /\ B) \/ C))
*)

let exo2_17 = ( "exo_2_17" , (((P "B") & ((P "A") || ((P "B") ==> (P "C")))) ==> ((P "A") || (P "C"))) ) ;;

let adp2_17 = 
  (Impl.intro "H1" 
    (Ou.elim 
      (Et.elim 2 (Hyp.apply "H1")
      ) 
      (Impl.intro "H8" 
        (Ou.intro 1 (Hyp.apply "H8")
        )
      ) 
      (Impl.intro "H10" 
        (Ou.intro 2 
          (Impl.elim 
            (Et.elim 1 (Hyp.apply "H1")
            ) (Hyp.apply "H10")
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_17 exo2_17 ;;


(*
                                                                 H1:(B /\ (A \/ (B ==> C)))                           
                                                                 __________________________ /\_e 1                    
                                                                 B                                  H10:(B ==> C)     
                                                                 ________________________________________________ =>_e
                                   H8:A                          C                                                    
                                   ________ \/_i                 ________ \/_i                                        
H1:(B /\ (A \/ (B ==> C)))         (A \/ C)                      (A \/ C)                                             
__________________________ /\_e 2  ________________ =>_i [H8:A]  ________________________ =>_i [H10:(B ==> C)]        
(A \/ (B ==> C))                   (A ==> (A \/ C))              ((B ==> C) ==> (A \/ C))                             
______________________________________________________________________________________________________________________ \/_e
(A \/ C)
______________________________________ =>_i [H1:(B /\ (A \/ (B ==> C)))]
((B /\ (A \/ (B ==> C))) ==> (A \/ C))


D�montrons ((B /\ (A \/ (B ==> C))) ==> (A \/ C)) :
Pour cela, supposons (B /\ (A \/ (B ==> C))) (hypoth�se [H1]) et montrons (A \/ C) 
  Pour cela, exploitons (A \/ (B ==> C))  
    qui est la partie gauche de la conjonction (B /\ (A \/ (B ==> C)))  
      qui correspond � l'hypoth�se [H1] 
  Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
  on doit donc prouver (A \/ C) dans chacun des cas : 
  - Cas 1: D�montrons (A ==> (A \/ C)) :
        Pour cela, supposons A (hypoth�se [H8]) et montrons (A \/ C) 
          Pour montrer (A \/ C) inutile de montrer C,
          on se contente de montrer A en remarquant que c'est exactement l'hypoth�se [H8] 
      
  - Cas 2: D�montrons ((B ==> C) ==> (A \/ C)) :
        Pour cela, supposons (B ==> C) (hypoth�se [H10]) et montrons (A \/ C) 
          Pour montrer (A \/ C) inutile de montrer A,
          on se contente de montrer C en remarquant que
          Puisqu'on a (B ==> C) d'apr�s [H10], il suffit de montrer B pour obtenir C. 
           
          qui est la partie droite de la conjonction (B /\ (A \/ (B ==> C)))  
            qui correspond � l'hypoth�se [H1] 
     

Ceci ach�ve la d�monstration de ((B /\ (A \/ (B ==> C))) ==> (A \/ C))
*)

let exo2_18 = ( "exo_2_18" , ((((P "A") ==> (P "B")) || ((P "A") ==> (P "C"))) ==> ((P "A") ==> ((P "B") || (P "C")))) ) ;;

let adp2_18 = 
  (Impl.intro "H1" 
    (Impl.intro "H2" 
      (Ou.elim (Hyp.apply "H1") 
        (Impl.intro "H6" 
          (Ou.intro 1 
            (Impl.elim (Hyp.apply "H2") (Hyp.apply "H6")
            )
          )
        ) 
        (Impl.intro "H7" 
          (Ou.intro 2 
            (Impl.elim (Hyp.apply "H2") (Hyp.apply "H7")
            )
          )
        )
      )
    )
  ) ;;

verify_and_print [ preuve_en_francais ] "-html" adp2_18 exo2_18 ;;


(*
                             H2:A  H6:(A ==> B)                            H2:A  H7:(A ==> C)                          
                             __________________ =>_e                       __________________ =>_e                     
                             B                                             C                                           
                             ________ \/_i                                 ________ \/_i                               
                             (B \/ C)                                      (B \/ C)                                    
                             ________________________ =>_i [H6:(A ==> B)]  ________________________ =>_i [H7:(A ==> C)]
H1:((A ==> B) \/ (A ==> C))  ((A ==> B) ==> (B \/ C))                      ((A ==> C) ==> (B \/ C))                    
_______________________________________________________________________________________________________________________ \/_e
(B \/ C)
________________ =>_i [H2:A]
(A ==> (B \/ C))
_______________________________________________ =>_i [H1:((A ==> B) \/ (A ==> C))]
(((A ==> B) \/ (A ==> C)) ==> (A ==> (B \/ C)))


D�montrons (((A ==> B) \/ (A ==> C)) ==> (A ==> (B \/ C))) :
Pour cela, supposons ((A ==> B) \/ (A ==> C)) (hypoth�se [H1]) et montrons (A ==> (B \/ C)) 
  Pour cela, supposons A (hypoth�se [H2]) et montrons (B \/ C) 
    Pour cela, exploitons ((A ==> B) \/ (A ==> C))  
      qui correspond � l'hypoth�se [H1] 
    Or on ne sait pas lequel des deux membres de la disjonction est vrai ; 
    on doit donc prouver (B \/ C) dans chacun des cas : 
    - Cas 1: D�montrons ((A ==> B) ==> (B \/ C)) :
          Pour cela, supposons (A ==> B) (hypoth�se [H6]) et montrons (B \/ C) 
            Pour montrer (B \/ C) inutile de montrer C,
            on se contente de montrer B en remarquant queB est une cons�quence directe des hypoth�ses H2: A et H6: (A ==> B) 
        
    - Cas 2: D�montrons ((A ==> C) ==> (B \/ C)) :
          Pour cela, supposons (A ==> C) (hypoth�se [H7]) et montrons (B \/ C) 
            Pour montrer (B \/ C) inutile de montrer B,
            on se contente de montrer C en remarquant queC est une cons�quence directe des hypoth�ses H2: A et H7: (A ==> C) 
       

Ceci ach�ve la d�monstration de (((A ==> B) \/ (A ==> C)) ==> (A ==> (B \/ C)))
*)
