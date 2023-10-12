(* 

 ARBRE DE PREUVE 

 Un ADP est une version compacte de la preuve.
 C'est un arbre constitué uniquement des règles à appliquer. 
 Il ne contient pas les formules logiques (ni conclusion, ni hypothèse).
 Il est donc plus court à écrire 

 DANS LES EXERCICES VOUS CONSTRUIREZ des ADP

*)      

type adp = Proof.prover

(* CONSTRUCTEUR d'ADP *)

(* + toutes les regles de la DN: voir regle.ml *)

(* + 2 constructeurs d'ADP incomplets *)

let (a_finir: int -> adp) = fun i -> Proof.unknown i ;;

let (>>) = Proof.bind ;; 

let (descendant: adp -> adp) = fun adp ->
      fun (facts,formule_a_prouver) -> 
	    (adp (facts,Term.unknown())) >> (fun p -> Proof.return (Proof_scheme.Gap(p,formule_a_prouver)))
;;


let (* OBSOLETE *) (a_prouver: int -> Proof.conclusion -> adp) = fun i c -> Proof.to_prove i c ;;


