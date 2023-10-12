(* traduction des types en francais *)

type       fait = Proof.fact
type      faits = Proof.facts
type        key = Proof.key
type  hypothese = Proof.hyp
type hypotheses = Proof.hypotheses
type formule = Term.formule

(* PREUVE 

   Une preuve est un arbre qui contient à chaque étape
   - la règle à appliquer 
   - les formules logiques de toutes les hypothèses disponibles et de la conclusion
   Il est facile à imprimer mais pénible à écrire car ilfaut sans cesse redonner les hypothèses et la conclusion.

   EN TP vous IMPRIMEREZ des PREUVES mais vous CONSTUIREZ des ARBRES DE PREUVE
*)

type preuve  = Proof_tree.proof_tree 
type theorem = Proof_tree.theorem

type 't printer = 't -> string

type filename = string
type extension = string
type file = filename * extension

(* AFFICHAGE D'UNE PREUVE *)

let (output_in_format: (theorem printer) list -> file -> theorem -> unit) = fun printers (filename,extension) theorem ->
      let html = (extension = "html")
      in let printers = (Output.pretty_interactive_proof_tree_in (if html then Output.Html else Output.Ascii)) :: printers 
      in let preuves = List.map (fun printer -> printer theorem) printers
      in
	if html
	then File.output_in (filename,"html") (String.concat "\n" ["<PRE>" ; String.concat "</PRE>\n<PRE>" preuves ; "</PRE>"])
	else print_string                     (String.concat "\n\n" preuves) 
;;



