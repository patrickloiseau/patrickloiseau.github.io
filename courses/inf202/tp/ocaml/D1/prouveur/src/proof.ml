open Proof_scheme

(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;

(* PROVER MODE *)

let _interactive_mode_ = true ;;

(* TYPES *)

type name = string

(* a proof is a list of proof_scheme *)

type proofs = proof_scheme list 

type t = proofs 

(* prover *)

type prover = (facts * conclusion) -> proofs 

(* fact *)

and fact = 
  | HYP of (key * conclusion)
  | LEM of Proof_scheme.t * conclusion
  | AXM of name * conclusion
  | USE of prover * conclusion

and facts = fact list
and axiom = fact

(* FIXME: this version is left for compatibility reason, TO BE REMOVED *)

type proof_maker = prover 

(* FACT *)

(* filter *)

let (hyps_of_facts: facts -> hyp list) = fun facts -> Mlist.bind facts (function HYP(h) -> [h] | _ -> []) ;;

let (pretty_fact: fact -> string) =
  function
    | HYP(k,c) -> Proof_scheme.pretty_hyp (k,c)
    | LEM(_,c) -> String.concat "" [ "LM[" ; Formule.pretty c ; "]" ]
    | AXM(n,c) -> String.concat "" [ "AX[" ; n ; ":" ; Formule.pretty c ; "]" ]
    | USE(_,c) -> String.concat "" [ "USE[" ; Formule.pretty c ; "]" ]



(* 2. MASQUAGE DE L'IMPLANTATION DES PROOF *)

type proof_tree = Proof_tree.t

type        key = Proof_scheme.key
type    formule = Proof_scheme.formule
type        hyp = Proof_scheme.hyp
type hypotheses = Proof_scheme.hypotheses

type conclusion = Proof_scheme.conclusion


let (conclusion_of: proof_scheme -> conclusion) = fun ps -> 
      begin
(*	print_string (String.concat " " [ "\n#\n# FIXME Proof.conclusion_of used in LEM does permanent unification \n#"]) ; *)
	Proof_tree.conclusion_of 
	  (* FIXME Convert.proof_scheme_to_proof_tree ps*)
	  (Convert.ps_to_pt ps)
      end
;;




(* MONAD *)

let (return: proof_scheme -> proofs) = fun ps -> [ps] ;;

let (abort: prover) = fun (facts,c) -> return (NoProof("abort", hyps_of_facts facts, c)) ;;

let (fail: string list -> proofs) = fun strings ->
      begin 
	Explain.print _x_ [ Explain.strategy ["Fail..."] ; Explain.html strings ] ;
	[]
      end

let (map_on: 'a list -> ('a -> 'b) -> 'b list) = Mlist.map_on ;;

let (one: proofs -> proof_scheme) = fun p -> try List.hd p with Failure "hd" -> Error "Proof.one: no proof at all" ;;

(* bind does a backtracking until one success or fail *)

let rec (bind: 'x list -> ('x -> 'y list) -> 'y list) = fun xs f ->
      match xs with
      | [] -> []
      | x::xs -> 
	      (match f x with
	      | [] -> bind xs f
	      | ys -> ys
	      )
;;

let (sum: 'x list -> 'x list -> 'x list) = fun p1 p2 -> p1 @ p2 ;;      
      
let (alt: proofs -> proofs -> proofs) = fun proof1 ->
   match proof1 with
   | [NoProof(msg,hyps,c)] -> (fun _ -> [NoProof(msg,hyps,c)])
   | [] -> (fun proof2 -> proof2)
   | p::_ -> (fun _ -> [p])
;;


(* CONSTRUCTEUR *)

(* of prover *)

let (unknown: int -> prover) = fun i -> 
      fun (_,c) -> return (ADP(i,c))

let (to_prove: int -> conclusion -> prover) = fun i c -> 
      fun (_,_) -> return (ADP(i,c))

(* of proof *)

let (error: string list -> proofs) = fun strings -> return (Proof_scheme.error strings)


(* CONVERSION *)

let (* FIXME *) (smallest: proofs -> proof_scheme) = one ;;

let (smallest_proof_tree: proofs -> proof_tree) = fun proofs ->
      Convert.proof_scheme_to_proof_tree (smallest proofs)


(* USED ? PRINTING *)

let (prettys: Output.style -> proofs -> string list) = fun style p -> 
      List.map 
	(fun ps -> Output.pretty_proof_tree_in style (Convert.proof_scheme_to_proof_tree ps)) 
	p 

let (pretty: Output.style -> proofs -> string) = fun style p -> String.concat "\n\n" (prettys style p)

let (print: Output.style -> proofs -> unit) = fun style p -> print_string (String.concat "" [ "\n" ; pretty style p ; "\n" ])




