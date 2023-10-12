open Proof
open Preuve
open Adp
open Term
open Output

type exo_ref = string

type exercice = exo_ref * conclusion

type format = string 

(* VERIFICATION ET AFFICHAGE D'UN ADP *)

let (verify_and_print: (theorem printer) list -> format -> adp -> exercice -> unit) = fun printers format prover (exo_ref,formule_a_prouver) ->
      let preuve = Proof.smallest_proof_tree (prover ([],formule_a_prouver))
      in 
	begin
	  print_string (String.concat " " 
			  [ "\n\n==================================================================================";
			    "\n\n Exercice" ; exo_ref ; "- Demontrez en DN \n\n" ;
			    Output.pretty_term_in Output.Ascii formule_a_prouver 
			  ]) ;
	  print_string ("\n\n VERIFICATION: ") ;
	  let check1 = Proof_tree.is_valid preuve 
	  and check2 = (Proof_tree.conclusion_of preuve) == formule_a_prouver
	  in 
	    begin 
	      print_string(if check1 then "preuve valide"  else "* /!\\ preuve invalide /!\\ *") ;
	      (
	       if (check1 && check2)
	       then print_string (String.concat " " ["\n\n  *     \n  * BRAVO, EXERCICE" ; exo_ref ; "REUSSI \n  *" ])
	       else print_string (String.concat " " ["\n\n  * /!\\\n  * /!\\  exercice" ; exo_ref ; "à finir \n  * /!\\" ])
						    ) ;
	       print_string( "\n\n== preuve ========================================================================\n\n") ;
	       let file = (exo_ref,format) and theorem = (preuve,formule_a_prouver)
	       in Preuve.output_in_format printers file theorem ;
	       print_string ("\n\n==================================================================================")
	    end
	end
;;


(* Proposition *)

let (p: string -> Term.t) = function x -> Term.P(x) ;;

let a = p "A" and b = p "B" and c = p "C" and d = p "D" and e = p "E"  ;;

(* Operateur pour ecrire des formules *)

let (==>) p c = Term.Impl(p,c) ;;

let (&) f1 f2 = Term.Et(f1,f2) ;;

let (||) f1 f2 = Term.Ou(f1,f2) ;;

let (==) e1 e2 = Term.eq e1 e2 ;; 

let non f = Term.Neg(f) ;;

let abs = Term.False ;;

let (<==>) f1 f2 = (f1 ==> f2) & (f2 ==> f1) ;;

let (<=) t1 t2 = Term.Pred("<=",[t1;t2]) ;;

(* Operateur pour ecrire des expressions *)

let (+) e1 e2 = Term.Op("+",[e1;e2]) ;;

let ( * ) e1 e2 = Term.Op("*",[e1;e2]) ;;

let int n = Term.I(n) ;;


(* relations *)

let (reflexive: Term.t -> Term.t) = fun t -> Pred("reflexive",[t])

let (o: Term.t -> Term.t -> Term.t) = fun s r ->
      let Pred("relation",[_; domain_A ; _]) = r
      and Pred("relation",[_; _; domain_C ]) = s
      in
	Pred("relation",[Op(" o ",[s;r]) ; domain_A ; domain_C])

let (relation: string -> string -> string -> Term.t) = fun r domain_A domain_B -> Pred("relation",[Term.S r ; Term.var domain_A ; Term.var domain_B])

