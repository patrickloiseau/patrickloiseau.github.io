(* DEBUGGING *)

let _debug_level = 0 ;;

let (debug: int -> string list -> unit) = fun i strings ->
      if i < _debug_level
      then print_string (String.concat " " (["\n" ; String.make i ' ' ] @ strings))
      else ()
;;


(* PROOF TREE *)

open Option
open Proof_scheme

type formule = Term.formule
type expr    = Term.expr
type var     = Term.var
type symbol  = Term.symbol

type conclusion = formule

type proof_tree =
  | Error of string
  | NoProof of (error_msg * hypotheses * conclusion)

  | A of int (* une variable de type proof_tree qu'on place quand on ne sait pas quoi mettre comme proof_tree *)
  | ADP of int * conclusion (* une variable de type proof_tree dont on connaît la conclusion à prouver *)

  | HYP_apply  of hypotheses * hyp * conclusion 

  | IMPL_elim  of hypotheses * proof_tree * proof_tree * conclusion
  | IMPL_intro of hypotheses * hyp * proof_tree * conclusion

  | ET_elim of hypotheses * int * proof_tree * conclusion
  | ET_intro of hypotheses * proof_tree * proof_tree * conclusion

  | OU_elim  of hypotheses * proof_tree * proof_tree * proof_tree * conclusion
  | OU_intro of hypotheses * int * proof_tree * formule * conclusion

  | EQ_trans of hypotheses * proof_tree list * conclusion
  | EQ_elim  of hypotheses * (expr -> formule) * expr * expr * proof_tree * proof_tree * conclusion

  | ABS_intro of hypotheses * proof_tree * proof_tree 
  | ABS_elim  of hypotheses * proof_tree * conclusion

  | NEGNEG_elim of hypotheses * proof_tree * conclusion

  | DEF_apply of hypotheses * name * arguments * proof_tree * conclusion

  | REC of hypotheses * var * domain * (expr -> formule) * proof_tree list * conclusion
  
  | QQ_elim  of hypotheses * (expr -> formule) * var * expr   * proof_tree * conclusion
  | QQ_intro of hypotheses * (expr -> formule) * var * symbol * proof_tree * conclusion

  | EX_intro of hypotheses * (expr -> formule) * var * expr * proof_tree * conclusion
  | EX_elim  of hypotheses * var * formule * proof_tree * proof_tree * conclusion

  | AXM_apply of name * conclusion

  | Gap of hypotheses * proof_tree * conclusion

and t = proof_tree 

(* THEOREM *)

type theorem = proof_tree * formule


(* CONSTRUCTEUR *)

let (error: string list -> proof_tree) = fun strings -> Error (String.concat " " strings)


(* EXTRACTION DES INFORMATIONS CONTENUES DANS D'UN ADP *)

(* hypotheses *)

let rec (hypotheses_of: proof_tree -> hypotheses) = 
  function
    | Error(_) 
    | A(_) 
    | ADP(_,_) -> []

    | NoProof(_,hs,_) 
    | HYP_apply(hs,_,_) 
    | IMPL_intro(hs,_,_,_) 
    | IMPL_elim(hs,_,_,_)  
    | ET_intro(hs,_,_,_)
    | ET_elim(hs,_,_,_)  
    | OU_intro(hs,_,_,_,_)
    | OU_elim(hs,_,_,_,_)
    | EQ_trans(hs,_,_) 
    | EQ_elim(hs,_,_,_,_,_,_)
    | ABS_intro(hs,_,_)
    | ABS_elim(hs,_,_)
    | NEGNEG_elim(hs,_,_)
    | DEF_apply(hs,_,_,_,_)
    | REC(hs,_,_,_,_,_)
    | QQ_elim(hs,_,_,_,_,_)
    | QQ_intro(hs,_,_,_,_,_)
    | EX_intro(hs,_,_,_,_,_) 
    | Gap(hs,_,_)
      -> hs

    | AXM_apply(_,_) -> []
;;

(* conclusion *)

let rec (conclusion_of: proof_tree -> conclusion) = 
  function
    | Error(msg) -> Term.error [ msg ]

    | A(n) -> Term.unknown()

    | ABS_intro(_,_,_) -> Term.False 

    | NoProof(_,_,c) 
    | ADP(_,c) 
    | HYP_apply(_,_,c) 
    | IMPL_intro(_,_,_,c) 
    | IMPL_elim(_,_,_,c)
    | ET_intro(_,_,_,c)
    | ET_elim(_,_,_,c)
    | OU_intro(_,_,_,_,c)
    | OU_elim(_,_,_,_,c)
    | EQ_trans(_,_,c) 
    | EQ_elim(_,_,_,_,_,_,c)
    | ABS_elim(_,_,c)
    | NEGNEG_elim(_,_,c)
    | DEF_apply(_,_,_,_,c)
    | REC(_,_,_,_,_,c)
    | QQ_elim(_,_,_,_,_,c)
    | QQ_intro(_,_,_,_,_,c)
    | EX_intro(_,_,_,_,_,c)
    | AXM_apply(_,c) 
    | Gap(_,_,c)
      -> c
;;

(* subtrees *)

let (subtrees_of: proof_tree -> proof_tree list) = 
  function
    | IMPL_intro(_,_,pt,_)
    | ET_elim(_,_,pt,_)              
    | OU_intro(_,_,pt,_,_)   
    | ABS_elim(_,pt,_) 
    | NEGNEG_elim(_,pt,_) 
    | DEF_apply(_,_,_,pt,_)	 
    | QQ_elim(_,_,_,_,pt,_)	 
    | QQ_intro(_,_,_,_,pt,_) 
      -> [pt]

    | IMPL_elim(_,pt1,pt2,_)
    | ET_intro(_,pt1,pt2,_)
    | EQ_elim(_,_,_,_,pt1,pt2,_) 
      -> [pt1 ; pt2]

    | OU_elim(_,pt1,pt2,pt3,_)	 -> [pt1;pt2;pt3]

    | EQ_trans(_,pts,_)             
    | REC(_,_,_,_,pts,_) -> pts

    | Gap(_,pt,_) -> [pt]

    | _ -> []
;;
		


(* VALID PROOF ? *)

(* Three ways to compare terms *)

(* unification with side-effets, used for propagation *)

let (=:=) t1 t2 = Term.is_substitution_valid (Term.unify t1 t2) ;;

(* comparison of terms after replacement of unifiable variable by their values *)

let (==) t1 t2 = (Term.pretty t1) = (Term.pretty t2) ;;

let (force_evaluation: 't list -> 't list) = List.map (fun x -> begin print_string(".") ; x end) ;;

let (conjonction: bool list -> bool) = fun predicates ->
      List.fold_left (&&) true (force_evaluation predicates)
  

let rec (is_valid: proof_tree -> bool) = fun proof_tree ->
      match proof_tree with
      | Error _ 
      | NoProof _
      | A _ 
      | ADP _ -> false
		
      | HYP_apply(hyps,h,c) ->
	      conjonction [ c =:= conclusion_of_hyp h ; List.mem h hyps ]
		    
      | IMPL_elim(_, pt1, pt2, c) ->
	      let c1 = conclusion_of pt1 and c2 = conclusion_of pt2
	      in conjonction [ is_valid pt1 ; is_valid pt2 ;
			       c2 =:= Term.Impl(c1,c) ]

	| IMPL_intro(hyps, h, pt, c) ->
		let c1 = conclusion_of_hyp h and c2 = conclusion_of pt 
		in conjonction [ is_valid pt ; 
				 c =:= Term.Impl(c1,c2) ; not(Ens.belongs h hyps) ]
		      
	| ET_elim(_, i, pt, c) ->
		conjonction [ is_valid pt ; 
			      c =:= Term.subterm i (conclusion_of pt) ]

	| ET_intro(_,pt1,pt2,c) ->
		let c1 = conclusion_of pt1 and c2 = conclusion_of pt2
		in conjonction [ is_valid pt1 ; is_valid pt2 ; 
				 c =:= Term.Et(c1,c2) ] 

	| OU_elim(_,pt,pt1,pt2,c) -> 
		let d = conclusion_of pt and c1 = conclusion_of pt1 and c2 = conclusion_of pt2
		in conjonction [ is_valid pt ; is_valid pt1 ; is_valid pt2 ;
				 d =:= Term.Ou(Term.premisse c1, Term.premisse c2) ; 
				 c =:= Term.conclusion c1 ;
				 c =:= Term.conclusion c2 ] 
			  
	| OU_intro(_, i, pt, f, c) -> 
		conjonction [ is_valid pt ; 
			      c =:= (if i=1 then Term.Ou(conclusion_of pt,f) else Term.Ou(f,conclusion_of pt)) ]
		    
	| EQ_trans(_,pts,c) ->
		let lhs = Term.left (conclusion_of (List.hd pts))
		and rhs = Term.right (conclusion_of (Mlist.last pts))
		in
		  conjonction ( (List.map is_valid pts) @ [ c =:= Term.eq lhs rhs ] )

	| EQ_elim(hs,prop,a,b,p_a,p_a_eq_b,c) ->
		conjonction [ is_valid p_a ; is_valid p_a_eq_b ;
			      (conclusion_of p_a) =:= (prop a) ;
			      (conclusion_of p_a_eq_b) =:= (Term.eq a b) ;
			      c =:= (prop b) ] 

	| ABS_intro(_,pt1,pt2) -> 
		conjonction [ is_valid pt1 ; is_valid pt2 ;
		(*FIXME*) ( (conclusion_of pt1 =:= Term.Neg(conclusion_of pt2)) || (Term.Neg(conclusion_of pt1) =:= conclusion_of pt2) ) ]	

	| ABS_elim(_,pt,_) ->
		conjonction [ is_valid pt ; 
			      conclusion_of pt =:= Term.False ]

	| NEGNEG_elim(_,pt,c) ->
		conjonction [ is_valid pt ; 
			      (conclusion_of pt) =:= Term.Impl(Term.Impl(Term.False,c),Term.False) ] 

	| DEF_apply(_,_,_,pt,c) ->
		conjonction [ is_valid pt ; 
			      (conclusion_of pt) =:= c ] 

	| REC(_,_,_,_,pts,_) ->
		conjonction (List.map is_valid pts)

	| QQ_intro(_,pred,x,x0,pt,c) ->
		conjonction [ is_valid pt ;
			      (conclusion_of pt) =:= (pred x0) ;
			      c =:= Term.Qq(x,pred x) ] 

        | QQ_elim(_,pred,x,e,pt,c) ->
		conjonction [ is_valid pt ;
			      (conclusion_of pt) =:= Term.Qq(x,pred x) ;
			      c =:= (pred e) ]

	| EX_intro(_,pred,x,e,pt,c) ->
		conjonction [ is_valid pt ;
			      c =:= Term.Ex(x,pred x) ;
			      (conclusion_of pt) =:= (pred e) ]

	| EX_elim(_,x,p_x,pte,ptq,c) ->
		let ce = conclusion_of pte
		and cq = conclusion_of ptq
		in
		  conjonction [ is_valid pte ; is_valid ptq ;
				ce =:= Term.Ex(x,p_x) ;
				cq =:= Term.Qq(x,Term.Impl(p_x,c)) ]
		    
	| AXM_apply(_,_) -> true

	| Gap(_,pt,c) -> 
		conjonction [ is_valid pt ;
			      (conclusion_of pt) =:= c ]
;;
	
