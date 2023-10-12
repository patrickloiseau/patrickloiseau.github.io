module Formule = Term
module Expr    = Term

type formule = Term.formule
type expr    = Term.expr
type var     = Term.var
type symbol  = Term.symbol
type domain  = Term.domain

type conclusion = formule

type key = Key.t

type error_msg = string

type name = string 



(* schémas de preuves = déroulement de preuves sans formules *)

type proof_scheme =
  | Error of string
  | NoProof of error_msg * hypotheses * conclusion

  | A of int (* une variable de type proof_scheme qu'on place quand on ne sait pas quoi mettre comme preuve *)
  | ADP of int * conclusion (* une variable de type proof_scheme dont on connaît la conclusion à prouver *)

  | HYP_apply of hyp

  | IMPL_elim  of proof_scheme * proof_scheme
  | IMPL_intro of hyp * proof_scheme

  | ET_elim of int * proof_scheme 
  | ET_intro of proof_scheme * proof_scheme 

  | OU_elim  of (proof_scheme * proof_scheme * proof_scheme)
  | OU_intro of (int * proof_scheme * formule)

  | EQ_trans of proof_scheme list
  | EQ_elim  of (expr -> formule) * expr * expr * proof_scheme * proof_scheme

  | ABS_intro of proof_scheme * proof_scheme
  | ABS_elim of proof_scheme * conclusion

  | NEGNEG_elim of proof_scheme

  | DEF_apply of name * arguments * proof_scheme * conclusion

  | REC of var * domain * (expr -> formule) * proof_scheme list 

  | QQ_elim  of (expr -> formule) * expr * proof_scheme
  | QQ_intro of (expr -> formule) * var * symbol * proof_scheme

  | EX_intro of (expr -> formule) * var * expr * proof_scheme
  | EX_elim  of proof_scheme * proof_scheme 

  | AXM_apply of name * conclusion

  | Gap of proof_scheme * conclusion

and arguments = expr list 

and t = proof_scheme (* pour accéder au type à l'extérieur du module *)

and hyp = key * conclusion

and hypotheses = hyp list


(* CONSTRUCTEUR *)

let (error: string list -> proof_scheme) = fun strings -> Error (String.concat " " (["*"]@strings@["*"]))


(* PREDICAT *)

(* UNUSED 
let rec (is_valid: proof_scheme -> bool) = function
    | Error(_) 
    | NoProof(_,_,_) 
    | A(_)
    | ADP(_,_) -> false

    | HYP_apply(_) -> true

    | OU_intro(_,ps,_)
    | ET_elim1(ps) 
    | ET_elim2(ps)  
    | IMPL_intro(_,ps) -> is_valid ps

    | IMPL_elim(ps1,ps2) 
    | ET_intro(ps1,ps2) -> is_valid ps1 && is_valid ps2

    | OU_elim(ps1,ps2,ps3) -> is_valid ps1 && is_valid ps2 && is_valid ps3

    | EQ_trans(pss) -> List.for_all is_valid pss

;;
*)


(* ACCESSEUR *)

(* hyp *)

let (key_of_hyp: hyp -> key) = fun (k,c) -> k 

let (conclusion_of_hyp: hyp -> conclusion) = fun (k,c) -> c 
  
let (pretty_hyp: hyp -> string) = fun (k,c) -> String.concat "" [ Key.pretty k ; ":" ; Term.pretty c]



