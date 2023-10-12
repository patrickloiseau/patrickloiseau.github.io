
(* IMPLICATION *) 

(* Règle du IMPL_intro

           /     Hn: P
          |       .
          |       . 
          |      proof1
          |     --------
          |        C
  proof = | ---------------- ==>_i [ Hn ]
           \      P ==> C
*)


Impl.intro: key -> prover -> prover
Impl.intro  key    proof1  = proof
            "Hn"   C         P==>C

(* Règle du IMPL_elim


           /   proof1    proof2
          |   --------  --------
          |      P       P ==> C
  proof = | ----------------------- ==>_e
           \           C
*)

Impl.elim: prover -> prover -> prover
Impl.elim  proof1    proof2  = proof
           P         P==>C      C


(* CONJONCTION *)

(* La règle du ET_elim

         proof                      proof                
       -------- 	          -------- 	
        F1 & F2                    F1 & F2  	
     ----------- /\e1	         ----------- /\e2
          F1                          F2            
*)

Et.elim: int -> prover -> prover
Et.elim: 1      proof   = proof 
                F1 & F2   F1

Et.elim: int -> prover -> prover
Et.elim  2      proof   = proof 
                F1 & F2   F2


(* Règle du ET_intro

      proof1    proof2 
      -------   ------- 	
        F1   	  F2        
     ---------------- /\i
         (F1 /\ F2)             
*)


Et.intro: prover -> prover -> prover
Et.intro  proof1    proof2  = proof
          F1        F2        F1 & F2  


(* DISJONCTION *)

(* La règle du OU_elim

        proof0       proof1        proof2
      ----------   ---------    -----------
        A || B       A ==> C       B ==> C  	            
     ------------------------------------------ \/_e
                       C  
*)

Ou.elim: prover -> prover -> prover -> prover
Ou.elim  proof0    proof1    proof2  = proof
         A || B    A ==> C   B ==> C   C	            


(* Règle du Ou.intro

       proof                       proof                
      -------- 	                  -------- 	
         A    	                     B  	
     ----------- \/_i1	         ----------- \/_i2
       A \/ B                      A \/ B            
*)

Ou.intro: int -> prover -> prover
Ou.intro  int    proof   = proof
           1       A       A || B   (la règle sait reconnaître le B qu'il faut)

Ou.intro  int    proof   = proof
           2       B       A || B   (la règle sait reconnaître le A qu'il faut)


(* NEGATION et ABSURDE *)

(* Règle du Abs.elim 

     proof
    -------
      _|_
   ----------- _|_e
       C
*)

Abs.elim: prover -> prover
Abs.elim: proof  = proof
           _|_       C         


(* Definition de la NEGATION
                          			 
        A => _|_                   !C		   
  .  ............. Neg.def  ................ Neg.def 
         !A		         C => _|_          

*)

Neg.def:  prover   -> prover
Neg.def:  proof    =  proof
          A => _|_      !A
Neg.def:  proof    =  proof
           !C         C => _|_


(* Règle du !!_elim

  proof_of _|_ with the additional hypothesis : H: !C
  ----------------------
           _|_
  ---------------------- =>_i [H]
    (!C) => _|_
  .................... def ! 
         !!C
  -------------------- !!_elim
           C
*)


Neg.negneg: prover     -> prover
Neg.negneg: proof      -> proof
            !C => _|_       C 



(* DEFINITION *)

(* Règle du Def.apply

         proof
    ---------------------
     QQ x. x:A ==> x R x
    --------------------- def_apply: reflexive [R]
       reflexive(R:AxA)
*)

Def.apply: name        -> arguments -> prover               -> prover
           "reflexive"    [ R ]        proof                 = proof
                                       QQ x. x:A ==> x R x     reflexive(R:AxA) 

(* Règle du Def.exploit

         proof
    ---------------------
       reflexive(R:AxA)
    --------------------- def_exploit: reflexive [R]
     QQ x. x:A ==> x R x
*)

Def.exploit: name       -> arguments -> prover           -> prover
             "reflexive"   [ R ]        proof             = proof
                                        reflexive(R:AxA)    QQ x. x:A ==> x R x


(* QUANTIFICATEUR UNIVERSELLE *)

(* Règle du Qq.intro

       proof
     ----------
      pred(Uo) 
   --------------- Qq_i (Uo /:/ hypothesis, Uo /:/ conclusion)
    Qq u, pred(u)

*)

Qq.auto_intro: prover   -> prover
Qq.auto_intro  proof     = proof
               pred(Uo)    Qq u, pred(u) 

(* /!\ La fonction Qq.intro 
   - reconnaît d'elle-même le prédicat pred 
   - crée elle-même un Uo nouveau qui n'apparaît ni dans les hypothèse, ni dans la conclusion. 
*)


(* Règle du QQ_e

	  adp
      ------------- 
      Qq x, pred(x)
  ------------------- Qq_e (x:=e)	  
        pred(e)                   	  

*)

Qq.elim: expr -> prover        -> prover
Qq.elim  e       adp            = adp
                 Qq x, pred(x)    pred(e)


(* QUANTIFICATION EXISTENTIELLE *)

(* Règle du Ex.intro 

     proof
   ---------
    pred(T)
  -------------- Ex_i 
  Ex u, pred(u)

*)

Ex.auto_intro: prover  -> prover
Ex.auto_intro  proof    = proof
               pred(T)    Ex u, pred(u) 


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

Ex.elim: prover       -> prover                -> prover 
Ex.elim  proof1          proof2                 = proof
         Ex x, pred(x)   QQ x, (pred(x) ==> C)    C 


(* HYPOTHESE *)

(* Règle du Hyp_apply

 Supposons que  H: formule  fasse partie des hypothèses


    ------------ Hyp.apply H
       formule
*)

Hyp.apply: hyp    -> prover
Hyp.apply: string  = proof
           "H"      formule



(* THEOREM *)

(* Règle du Thm_apply 

     \ proof /
     ---------
      formule
  ----------------- Thm.apply
      formule
*)

Thm.apply: theorem         -> prover
Thm.apply  (proof,formule)  = proof
                              formule
