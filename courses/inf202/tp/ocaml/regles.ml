
(* IMPLICATION *) 

(* R�gle du IMPL_intro

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

(* R�gle du IMPL_elim


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

(* La r�gle du ET_elim

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


(* R�gle du ET_intro

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

(* La r�gle du OU_elim

        proof0       proof1        proof2
      ----------   ---------    -----------
        A || B       A ==> C       B ==> C  	            
     ------------------------------------------ \/_e
                       C  
*)

Ou.elim: prover -> prover -> prover -> prover
Ou.elim  proof0    proof1    proof2  = proof
         A || B    A ==> C   B ==> C   C	            


(* R�gle du Ou.intro

       proof                       proof                
      -------- 	                  -------- 	
         A    	                     B  	
     ----------- \/_i1	         ----------- \/_i2
       A \/ B                      A \/ B            
*)

Ou.intro: int -> prover -> prover
Ou.intro  int    proof   = proof
           1       A       A || B   (la r�gle sait reconna�tre le B qu'il faut)

Ou.intro  int    proof   = proof
           2       B       A || B   (la r�gle sait reconna�tre le A qu'il faut)


(* NEGATION et ABSURDE *)

(* R�gle du Abs.elim 

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


(* R�gle du !!_elim

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

(* R�gle du Def.apply

         proof
    ---------------------
     QQ x. x:A ==> x R x
    --------------------- def_apply: reflexive [R]
       reflexive(R:AxA)
*)

Def.apply: name        -> arguments -> prover               -> prover
           "reflexive"    [ R ]        proof                 = proof
                                       QQ x. x:A ==> x R x     reflexive(R:AxA) 

(* R�gle du Def.exploit

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

(* R�gle du Qq.intro

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
   - reconna�t d'elle-m�me le pr�dicat pred 
   - cr�e elle-m�me un Uo nouveau qui n'appara�t ni dans les hypoth�se, ni dans la conclusion. 
*)


(* R�gle du QQ_e

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

(* R�gle du Ex.intro 

     proof
   ---------
    pred(T)
  -------------- Ex_i 
  Ex u, pred(u)

*)

Ex.auto_intro: prover  -> prover
Ex.auto_intro  proof    = proof
               pred(T)    Ex u, pred(u) 


(* R�gle du Ex.elim 

  On utilise une version diff�rente de celle du cours (mais �quivalente)

  D'apr�s la preuve 1 on sait qu'il existe un 'x' pour lequel la pr�dicat pred est vrai,
  On souhaite exploiter l'existence d'un tel 'x' pour d�montrer C

  Comme on ne sait pas qui est cet 'x',
  il faut montrer que C est une cons�quence de pred(x) pour n'importe quel 'x' 
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

(* R�gle du Hyp_apply

 Supposons que  H: formule  fasse partie des hypoth�ses


    ------------ Hyp.apply H
       formule
*)

Hyp.apply: hyp    -> prover
Hyp.apply: string  = proof
           "H"      formule



(* THEOREM *)

(* R�gle du Thm_apply 

     \ proof /
     ---------
      formule
  ----------------- Thm.apply
      formule
*)

Thm.apply: theorem         -> prover
Thm.apply  (proof,formule)  = proof
                              formule
