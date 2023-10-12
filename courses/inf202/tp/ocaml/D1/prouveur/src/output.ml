

(* PRETTY PRINTING / OUTPUT in latex, ascii, ocaml *)

type style = Ascii | Latex | Ocaml | Html ;;


(* OUTPUT Term in ascii, latex, ocaml *)

let (*USER*) (pretty_term_in: style -> Term.t -> string) = fun style ->
      match style with
      |	Ascii | Html -> Term.pretty
      |	Latex -> Term.latex
      |	Ocaml -> Output_in_ocaml.ocaml_term
;;


(* OUTPUT Proof_tree in ascii, latex, ocaml *)

open Option

open Proof_scheme (* needed for definitions of hyp *)
open Proof_tree

(* ascii *)

let (superposer: bool -> Mep.rcolonne list * formule * formule list * string list -> Mep.rcolonne) = 
  fun valid (prfs_en_rcolonnes, proof_conclusion, formules_a_prouver, regle) ->
	let 
	    str_formules_a_prouver = List.map Term.pretty formules_a_prouver
	and 
	    str_proof_conclusion = Term.pretty proof_conclusion
	in let
	    unproved = List.filter (fun f -> f <> str_proof_conclusion) str_formules_a_prouver
	in let 
	    coincide = ( unproved = [])
	in let
	    rcol = Mep.fusionner prfs_en_rcolonnes
	and 
	    str_unproved = String.concat " , " unproved
	and 
	    r = String.concat " " regle
	in let 
	    largeur_ligne = max (Mep.largeur_base rcol) (max (String.length str_proof_conclusion) (String.length str_unproved))
	in let 
	    fraction = Mep.n_fois (largeur_ligne, if valid then "_" else "*")
	in 	  
	  (if coincide then [] else [ str_unproved ; Mep.n_fois (largeur_ligne, "#") ])
	  @ [ str_proof_conclusion ; fraction ^ " " ^ r ] 
	  @ rcol
  

let colonne str = Mep.rcol str 


let rec (proof_tree_vers_colonne: proof_tree -> conclusion -> Mep.rcolonne) =  fun pt_a_afficher expected_conclusion -> 
      let valid = false
      in
      match pt_a_afficher with
      | Error msg -> colonne ( "\n" ^ msg ^ "\n")

      |	NoProof(msg,hs,c) ->
	      superposer false
		( List.map hyp_vers_colonne hs,
		  c,
		  [expected_conclusion], (* FIXME *)
		  ["/!\\" ; msg]
		 )
      | A n -> 
	      colonne (String.concat "" [ "\\" ; string_of_int n ; "/" ])
					       
      | ADP(n,c) -> 
	      superposer false
		([ proof_tree_vers_colonne (A n) c ], 
		 c,
		 [expected_conclusion],
		 ["?"]
		)

      | HYP_apply(_,h,c) -> 
	      colonne (pretty_conclusion_of pt_a_afficher)

      | IMPL_elim(_,pt1,pt2,c) -> 
	      let c1 = conclusion_of pt1 and c2 = conclusion_of pt2 
	      in let valid = ( c2 == Term.Impl(c1,c) )
	      in
		superposer valid
		  ([ proof_tree_vers_colonne pt1 c1 ; proof_tree_vers_colonne pt2 (Term.Impl(c1,c)) ],
		   c,
		   [expected_conclusion],
		   if valid 
		   then [ "=>_e" ]
		   else [ "=>_e IMPOSSIBLE:" ; Term.pretty_substitution (Term.unify c2 (Term.Impl(c1,c))) ; Term.pretty c2 ; "=/=" ; Term.pretty (Term.Impl(c1,c)) ] 
		  ) 

      | IMPL_intro(_,hyp,pt1,c) -> 
	      let c1 = conclusion_of pt1 and h = conclusion_of_hyp hyp 
	      in let valid =  c == (Term.Impl(h,c1))
	      in
		superposer valid
		  ([ proof_tree_vers_colonne pt1 (Term.conclusion c) ],
		   c,
		   [ expected_conclusion ; Term.Impl(h,c1) ], 
		   [ "=>_i" ; ("[" ^ (pretty_hyp hyp) ^ "]") ]
		  ) 

      |	ET_elim(_,i,pt,ci) ->
	      let c = conclusion_of pt
	      in
	      superposer (ci == (Term.subterm i c))
		([ proof_tree_vers_colonne pt c ],
		 ci,
		 [expected_conclusion ; Term.subterm i c],
		 [ "/\\_e" ; string_of_int i ]
		) 

      |	ET_intro(_,pt1,pt2,c) ->
	      let c1 = conclusion_of pt1 and c2 = conclusion_of pt2
	      in
	      superposer (c == (Term.Et(c1,c2)))
		([ proof_tree_vers_colonne pt1 c1 ; proof_tree_vers_colonne pt2 c2 ],
		 c,
		 [expected_conclusion ;Term.Et(c1,c2)],
		 [ "/\\_i" ]
		) 
   
      | OU_elim(_,pt,pt1,pt2,c) -> 
	      let c1 = Term.conclusion (conclusion_of pt1) and c2 = Term.conclusion (conclusion_of pt2)
	      and p1 = Term.premisse   (conclusion_of pt1) and p2 = Term.premisse   (conclusion_of pt2) 
	      in let valid = 	
		( (conclusion_of pt) == Term.Ou(p1,p2)
		    &&
		  c == c1
		    &&
		  c == c2
		 )
	      in superposer valid
		  ([ proof_tree_vers_colonne pt (Term.Ou(p1,p2)) ;  proof_tree_vers_colonne pt1 (Term.Impl(p1,c1)) ; proof_tree_vers_colonne pt2 (Term.Impl(p2,c2)) ],
		   c,
		   [expected_conclusion ; c1 ; c2],
		   [ "\\/_e" ]
		  ) 

      | OU_intro (_, i, pt,f,c) -> 
	      let f' = conclusion_of pt 
	      in let f_f_ = (if i=1 then Term.Ou(f',f) else Term.Ou(f,f'))
	      in
		superposer (c==f_f_)
		([ proof_tree_vers_colonne pt f'],
		 c,
		 [expected_conclusion ;f_f_],
		 [ "\\/_i" ] 
		) 

      |	EQ_trans(_,prfs,c) ->
	      superposer true
		( List.map (fun pt -> proof_tree_vers_colonne pt (conclusion_of pt) (* FIXME *)) prfs,
		  conclusion_of pt_a_afficher,
		  [], (* FIXME *)
		  [ "=_trans" ]
		 )

      | EQ_elim(hs,prop,a,b,p_a,p_a_eq_b,c) ->
	      superposer
		( (conclusion_of p_a) == (prop a)
		    &&
		  (conclusion_of p_a_eq_b) == (Term.eq a b)
 	            &&
		  c == (prop b)
                 )
		( [ proof_tree_vers_colonne p_a (conclusion_of p_a) (* FIXME *) ; proof_tree_vers_colonne p_a_eq_b (conclusion_of p_a_eq_b) (* FIXME *) ],
		  conclusion_of pt_a_afficher,
		  [], (* FIXME *)
		  [ "=_e"]
		 )

      | ABS_intro(_,pt1,pt2) -> 
	      let c1 = conclusion_of pt1 and c2 = conclusion_of pt2 
	      in
	      superposer ( (c1 == Term.Neg(c2)) || (Term.Neg(c1) == c2) )
		([ proof_tree_vers_colonne pt1 c1 ; proof_tree_vers_colonne pt2 c2 ],
		 conclusion_of pt_a_afficher,
		 [expected_conclusion], (* FIXME *)
		 [ "_|_ i" ] 
		) 

      | ABS_elim(_,pt,c) ->
	      superposer ( (conclusion_of pt) =:= Term.False )
		([ proof_tree_vers_colonne pt (conclusion_of pt) ],
		 c,
                 [], 
		 [ "_|_ e" ] 
		) 

      | NEGNEG_elim(_,pt,c) ->
	      superposer ( (conclusion_of pt) == Term.Impl(Term.Impl(c,Term.False),Term.False) )
		([ proof_tree_vers_colonne pt (conclusion_of pt) (* FIXME *) ],
		 conclusion_of pt_a_afficher,
                 [], (* FIXME *)
		 [ "!!e" ] 
		) 
		
      | DEF_apply(_,name,_,pt,_) ->
	      superposer true
		([ proof_tree_vers_colonne pt (conclusion_of pt) (* FIXME *) ],
		 conclusion_of pt_a_afficher,
                 [], (* FIXME *)
		 [ "def" ; name ] 
		) 

    | REC(hs,n,domain,pred,pts,c) ->
	    superposer true
	      ( List.map (fun pt -> proof_tree_vers_colonne pt (conclusion_of pt) (* FIXME *)) pts,
		conclusion_of pt_a_afficher,
                [], (* FIXME *)
		[ "rec" ; Term.pretty domain ]
	       )

    | QQ_intro(_,pred,x,x0,pt,c) -> 
	    let check1 =  (conclusion_of pt) == (pred x0)
	    and check2 =  c == Term.Qq(x,pred x)
	    in
	      superposer ( check1 && check2 )
		([ proof_tree_vers_colonne pt (pred x0) ],
		 c,
		 [expected_conclusion ; Term.Qq(x,pred x)],
		 [ "Qq_i" ; "(" ^ (Term.pretty x0) ; "is fresh)" (* ; "avec le predicat" ; Term.pretty_fun pred *) ]
		)
	      
    | QQ_elim(_,pred,x,e,pt,c) -> 
	    let check1 =  (conclusion_of pt) == Term.Qq(x,pred x)
	    and check2 =  c == (pred e) 
	    in
	      superposer ( check1 && check2 )
		([ proof_tree_vers_colonne pt (Term.Qq(x,pred x)) ],
		 c,
                 [],
		 if not check1
		 then [ "Qq_e error1:" ; Term.pretty (conclusion_of pt) ; "=/=" ; Term.pretty (Term.Qq(x,pred x)) ] 
		 else if not check2
		 then [ "Qq_e error2:" ; Term.pretty c ; "=/=" ; Term.pretty (pred e) ] 
		 else [ "Qq_e" ; ("[" ^ (Term.pretty x) ^ ":=" ^ (Term.pretty e) ^ "]")  (* ; "avec le predicat" ; Term.pretty_fun pred *) ]
	      )

    | EX_intro(_,pred,x,e,pt,c) -> 
	    let check1 = ( (conclusion_of pt) == (pred e) )
	    and check2 = ( c == Term.Ex(x, pred x) )
	    in
	      superposer ( check1 && check2 )
		([ proof_tree_vers_colonne pt (pred e) ],
		 c,
		 [expected_conclusion ; Term.Ex(x, pred x)],
		 if not check1
		 then [ "Ex_i error:" ; Term.pretty (conclusion_of pt) ; "=/=" ;  Term.pretty (pred e) ] 
		 else if not check2
		 then [ "Ex_i error:" ; Term.pretty c ; "=/=" ; Term.pretty (Term.Ex(x, pred x)) ] 
		 else [ "Ex_i" ; ("[" ^ (Term.pretty x) ^ ":=" ^ (Term.pretty e) ^ "]")]
	      )

    | EX_elim(_,x,p_x,pte,ptq,c) -> 
	    let ce = conclusion_of pte and cq = conclusion_of ptq in
	      let check1 = ( ce == Term.Ex(x,p_x) )
	      and check2 = ( cq == Term.Qq(x,Term.Impl(p_x,c)) )
	    in
	      superposer ( check1 && check2 )
		([ proof_tree_vers_colonne pte ce ; proof_tree_vers_colonne ptq cq ],
		 c,
		 [expected_conclusion],
		 ["Ex_e"]
		)

    | AXM_apply(name,c) ->
	    superposer true
	      ([],
	       c,
	       [expected_conclusion], (* FIXME *)
	       [ "Ax:" ; name]
	      )

    | Gap(_,pt,c) ->
	    let cpt = conclusion_of pt
	    in let valid = (cpt == c)
	    in 
	      superposer valid
		([ proof_tree_vers_colonne pt cpt ],
		 c,
		 [],
		 (if valid then ["C.Q.F.D."] else ["..."])
		)


and (pretty_conclusion_of: proof_tree -> string) = fun pt -> 
      let c = conclusion_of pt in
	(match pt with
	| HYP_apply(_,hyp,_) -> (pretty_key_of hyp) ^ ":"
	| _ -> (match pretty_keys (hypotheses_of pt) with
		| "" -> ""
		| str -> str ^ " |-- "
		)
	)
	^
        (Term.pretty c)

and (pretty_key_of: hyp -> string) = fun (k,f) -> Key.pretty k

and (pretty_keys: hyp list -> string) = 
  let rec (n_pretty_keys: int -> hyp list -> string) = fun n hs ->
	if n = 0
	then (string_of_int (List.length hs)) ^ "hyps"
	else 
	  match hs with 
	  | [] -> "" 
	  | [h] -> pretty_key_of h
	  | h::hs -> (pretty_key_of h) ^ "," ^ (n_pretty_keys (n-1) hs)
  in
    fun hyps -> n_pretty_keys 5 hyps
 
and (hyp_vers_colonne: hyp -> Mep.rcolonne) = fun h -> colonne (pretty_hyp h)

and (pretty: theorem -> string) = fun (proof_tree,expected_conclusion) -> 
      Mep.colonne_vers_chaine (List.rev (proof_tree_vers_colonne proof_tree expected_conclusion))
;;

let (print: theorem -> unit) = fun theorem -> print_string (pretty theorem) ;;




(* OUTPUT in LATEX *)

let (latex_keys: hyp list -> Latex.t) = 
  let rec (n_pretty_keys: int -> hyp list -> Latex.t) = fun n hs ->
	if n = 0
	then (string_of_int (List.length hs)) ^ "hyps"
	else 
	  match hs with 
	  | [] -> "" 
	  | [h] -> Key.latex (key_of_hyp h)
	  | h::hs -> (Key.latex (key_of_hyp h)) ^ "," ^ (n_pretty_keys (n-1) hs)
  in
    fun hyps -> n_pretty_keys 5 hyps


let (latex_hypothesis: hyp list -> Latex.t) = 
  function
    | [] -> ""
    | hs -> (latex_keys hs) ^ "~\\vdash~"  

let (latex_conclusion: hyp list -> conclusion -> Latex.t) = fun hs c ->
      (latex_hypothesis hs) ^ (Term.latex c)


let (transform_conclusion_of: proof_tree -> (conclusion -> conclusion) -> proof_tree) = fun proof_tree transform ->
      let c = transform (conclusion_of proof_tree) in
	match proof_tree with
	| NoProof(msg,hs,_)              -> NoProof(msg,hs,c)
	| ADP(n,_)                       -> ADP(n,c)
	| HYP_apply(hs,h,_)              -> HYP_apply(hs,h,c)  
	| IMPL_intro(hs,pt1,pt2,_)       -> IMPL_intro(hs,pt1,pt2,c) 
	| IMPL_elim(hs,pt1,pt2,_)        -> IMPL_elim(hs,pt1,pt2,c)
	| ET_intro(hs,pt1,pt2,c)         -> ET_intro(hs,pt1,pt2,c)
	| ET_elim(hs,i,pt,_)             -> ET_elim(hs,i,pt,c)
	| OU_intro(hs,i,pt,formule,_)    -> OU_intro(hs,i,pt,formule,c)
	| OU_elim(hs,pt1,pt2,pt3,_)	 -> OU_elim(hs,pt1,pt2,pt3,c)
	| EQ_trans(hs,pts,_)             -> EQ_trans(hs,pts,c) 
	| EQ_elim(hs,prop,a,b,pt1,pt2,_) -> EQ_elim(hs,prop,a,b,pt1,pt2,c)
	| ABS_elim(hs,pt,_)	         -> ABS_elim(hs,pt,c)
	| NEGNEG_elim(hs,pt,_)	         -> NEGNEG_elim(hs,pt,c)
	| DEF_apply(hs,name,args,pt,_)	 -> DEF_apply(hs,name,args,pt,c)
	| REC(hs,var,domain,prop,pts,_)	 -> REC(hs,var,domain,prop,pts,c)
	| QQ_elim(hs,prop,x,e,pt,_)	 -> QQ_elim(hs,prop,x,e,pt,c)
	| QQ_intro(hs,prop,x,e,pt,_)	 -> QQ_intro(hs,prop,x,e,pt,c)
	| AXM_apply(n,_)                 -> AXM_apply(n,c) 
	| _                              -> proof_tree
;;


(* SMART TREEs are splitted when too long *)

type latex_tree = Latex.t ;;

type declaration = latex_tree ;;

type smart_tree = declaration list * latex_tree ;;

type smart_trees = declaration list * latex_tree list ;;

type width = int ;;

let _screen_width = ref 80

let (width: proof_tree -> width) = 
  let (-->) x f = f x

  in let rec (all_conclusions: proof_tree  -> conclusion list) = fun proof_tree ->
	let subtrees = subtrees_of proof_tree in
	  (conclusion_of proof_tree) 
	  :: 
	    (Term.Conj (List.map conclusion_of subtrees)) 
	  :: 
	    (List.concat (List.map all_conclusions subtrees))
	      
  in fun proof_tree ->
	(all_conclusions proof_tree) --> (List.map (fun c -> String.length (Term.pretty c))) --> (List.fold_left max 0)
;;		  


let (latex: proof_tree -> Latex.t) = 

  let _proof_id = ref 0 

  in let fresh_proof_id () = 
    begin 
      _proof_id:= !_proof_id+1 ;
      "\\nabla_{" ^ (string_of_int !_proof_id) ^ "}"
    end

  in let rec (smart_tree: proof_tree -> smart_tree) = 
    function
      | Error(msg) -> [], Latex.macro "textcolor{red}" [msg]
		
      | NoProof(msg,hs,c) -> 
	      let latex_c = Latex.macro "fcolorbox{red}{white}" [ Latex.math (latex_conclusion hs c) ] in
		[],
		if msg ="" 
		then latex_c
		else Latex.infer [] latex_c [msg]

      | A(n) -> [], Latex.subscript ("\\nabla") (Key.make "" n)
		
      | ADP(n,c) -> [], Latex.infer [] (Term.latex c) [ Latex.subscript ("\\nabla") (Key.make "" n) ]

      | HYP_apply(hs,(k,c),_) -> [], Latex.macro "Overbrace" [ Term.latex (c) ; Key.latex k ]

      | IMPL_intro(hs,h,pt,c) -> 
	      let (decls,tree) = smart_tree pt in
		decls,
		Latex.infer [ "\\impl_i" ; Latex.bracket( Key.latex (key_of_hyp h)) ] (latex_conclusion hs c) [ tree ]

      | ET_intro(hs,pt1,pt2,c) -> 
	      let (decls,trees) = smart_trees [pt1 ; pt2] in
		decls,
		Latex.infer ["\\andl_i"] (latex_conclusion hs c) trees

      | IMPL_elim(hs,pt1,pt2,c) -> 
	      let (decls,trees) = smart_trees [pt1 ; pt2] in
		decls,
		Latex.infer ["\\impl_e"] (latex_conclusion hs c) trees

      | ET_elim(hs,i,pt,c) -> 
	      let (decls,tree) = smart_tree pt in
		decls,
		Latex.infer ["\\andl_{e_"^(string_of_int i)^"}"] (latex_conclusion hs c) [ tree ]
		  
      | OU_elim(hs,pt,pt1,pt2,c) -> 
	      let (decls,trees) = smart_trees [pt ; pt1 ; pt2] in 
		decls, 
		Latex.infer ["\\vee_{e}"] (latex_conclusion hs c) trees
		
      | OU_intro(hs,i,pt,f,c) ->
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\vee_{i_"^(string_of_int i)^"}" ] (latex_conclusion hs c) [ tree ]

      | EQ_trans(hs,pts,c) ->
	      let (decls,trees) = smart_trees pts in 
		decls, 
		Latex.infer ["=_{trans}"] (latex_conclusion hs c) trees

      | EQ_elim(hs,prop,a,b,pt1,pt2,c) ->
	      let psi = Key.latex (Key.fresh "\\Phi")
	      in
	      let pt1 = transform_conclusion_of pt1 (fun c -> Term.Op("\\leftrightarrow", [ c ; Term.Op(psi,[a])]))
	      in let (decls,trees) = smart_trees [ pt1 ; pt2 ] in 
		decls, 
		Latex.infer [ "=_e" ; Latex.group ["with~" ; psi ; ":= \\fbox{$\\cdot$}\\rightarrow " ; Latex.par (Term.latex (prop (Term.V "\\fbox{$\\cdot$}"))) ] ] 
		  (latex_conclusion hs (Term.Op("\\leftrightarrow", [ Term.Op(psi,[ b ]) ; c ])))
		  trees
      
      | ABS_intro(hs,pt1,pt2) -> 
	      let (decls,trees) = smart_trees [ pt1 ; pt2 ] in 
		decls, 
		Latex.infer ["\\bot_i"] (latex_conclusion hs Term.False) trees
  
      | ABS_elim(hs,pt,c) ->
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\bot_e"] (latex_conclusion hs c) [ tree ]

      | NEGNEG_elim(hs,pt,c) ->
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\neg\\neg_e"] (latex_conclusion hs c) [ tree ]

      | DEF_apply(hs,name,_,pt,c) ->
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\textit{\\tiny def~" ; name ; "}"] (latex_conclusion hs c) [ tree ]

      | REC(hs,_,domain,_,pts,c) ->
	      let (decls,trees) = smart_trees pts in 
		decls, 
		Latex.infer ["\\textit{\\tiny rec~}" ; Term.latex domain] (latex_conclusion hs c) trees

      | QQ_intro(hs,p,x,x0,pt,c) -> 
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\forall_i (" ; Term.latex x0 ; "\\notin\\mathscr{H})" ] (latex_conclusion hs c) [ tree ]

      | QQ_elim(hs,p,x,e,pt,c) -> 
	      let (decls, tree) = smart_tree pt in 
		decls, 
		Latex.infer ["\\forall_e ("; Term.latex x; ":=" ; Term.latex e; ")"] (latex_conclusion hs c) [ tree ]

      | AXM_apply(name,c) ->
	      [],
	      Latex.infer ["\\textsc{\\tiny ax~$("; name ; ")$}"] (Term.latex c) []

  and (refine: (width * proof_tree) gender list -> (width * proof_tree) gender list) = fun individuals -> 
	let width   = List.fold_left (fun acc -> (function Mal(w,_) -> acc + w   | Fem _ -> acc)) 0 individuals 
	in
	  if width < !_screen_width
	  then begin debug 0 ["width:=" ; string_of_int width ] ; individuals end
	  else
	    let maximum = List.fold_left (fun acc -> (function Mal(w,_) -> max acc w | Fem _ -> acc)) 0 individuals 
	    in 
	      if maximum = 0 
	      then begin debug 0 ["width:=" ; string_of_int width ] ; individuals end
	      else 
		refine (List.map (function Mal(w,pt) when w=maximum -> Fem(w,pt) | g -> g) individuals)

  and (smart_trees: proof_tree list -> smart_trees) = fun proof_trees ->
	
	let individuals = List.map (fun pt -> Mal(width pt, pt)) proof_trees
	in let individuals = refine individuals
	in
	  List.fold_left 
	    (fun (decls,trees) -> 
		  function 
		    | Mal(_,pt) -> let (new_decls,tree) = smart_tree pt           in (decls @ new_decls, trees @ [ tree ])
		    | Fem(_,pt) -> let (new_decls,  id) = name_this_proof_tree pt in (decls @ new_decls, trees @ [  id  ])
	    )
	    ([],[])
	    individuals
	      
  and (name_this_proof_tree: proof_tree -> smart_tree) = fun proof_tree ->
	let (decls,tree) = smart_tree proof_tree
	in let proof_id = fresh_proof_id()
	in let new_decl = String.concat "" [ proof_id ; ":=" ; "\\left\\{\\begin{array}{c}" ; tree ; "\\end{array}\\right." ]
	in (decls @ [ new_decl ] , proof_id)
	    
  in fun proof_tree ->
	let (decls,main_tree) = smart_tree proof_tree in
	  String.concat "\n\\clearpage\n"
	    (List.map 
	       (fun tree -> String.concat "" [ "\\begin{center}\\begin{turn}{90}\\begin{math}" ; tree ; "\\end{math}\\end{turn}\\end{center}" ]) 
	       (decls @ [main_tree])
	    )
;;




(* USER FUNCTIONS *)

let (*USER*) (pretty_interactive_proof_tree_in: style -> theorem -> string) = fun style (proof_tree,expected_conclusion) ->
      match style with
      | Ascii | Html -> pretty (proof_tree, expected_conclusion)
      | Latex -> latex proof_tree 
;;

let (*USER*) (pretty_proof_tree_in: style -> proof_tree -> string) = fun style proof_tree ->
      match style with
      | Ascii | Html -> pretty (proof_tree,conclusion_of proof_tree)
      | Latex -> latex proof_tree 
;;


let (*USER*) (output_proof_tree_in_file: string -> style -> proof_tree -> unit) = fun filename style proof ->
      match style with
      | Ascii -> print_string (pretty_proof_tree_in style proof)
      | Html  -> File.output_in ("html/" ^ filename,"html") (String.concat "\n" [ "<PRE>" ; pretty_proof_tree_in style proof ; "</PRE>" ])
      | Latex -> 
	      File.output_in ("latex/" ^ filename,"tex") 
		(String.concat "" 
		   [ (* "\n\n\\clearpage" ; "\\section{Exercice " ; filename ; ": Démontrez en DN $" ; Term.latex formula ; "$}" ; *)
		     filename ; "=" ; pretty_proof_tree_in style proof
		   ]) 
		;;

let (*USER*) (pretty_proof_scheme_in: style -> proof_scheme -> string) = fun style ps -> 
      match style with
      |	Ocaml -> Output_in_ocaml.ocaml_proof_scheme ps
      |	Ascii | Html | Latex ->
	      pretty_proof_tree_in style (Convert.proof_scheme_to_proof_tree ps) 
;;

let (*USER*) (output_proof_scheme_in_file: string -> style -> proof_scheme -> unit) = fun filename style ps ->
      match style with
      | Ascii -> print_string (pretty_proof_scheme_in style ps)
      | Html  -> File.output_in ("html/" ^ filename,"html") (pretty_proof_scheme_in style ps)
      | Latex -> File.output_in ("latex/" ^ filename,"tex") (pretty_proof_scheme_in style ps)
      | Ocaml -> File.output_in ("ocaml/" ^ filename,"ml") (pretty_proof_scheme_in style ps)


(* UNUSED

(* proof_tree de plus petite taille *)

(* 2. COMBINATEUR *)


let rec (fold: 'r -> ('r -> 'r -> 'r) -> (proof_tree -> 'r) -> proof_tree -> 'r) = fun init add eval -> function prfi ->
      match prfi with
      | IMPL_elim(_,prf1,prf2,_)   
      |	ET_intro(_,prf1,prf2,_) ->
	      let r1 = fold init add eval prf1
	      in let r2 = fold r1 add eval prf2
	      in add r2 (eval prfi) 

      | IMPL_intro(_,_,prf,_)   
      |	ET_elim1(_,prf,_)
      |	ET_elim2(_,prf,_) -> let r = fold init add eval prf in add r (eval prfi)

      |	_ -> add init (eval prfi)
;;




(* taille *)

let (size: proof_tree ->int) = fold 0 (+) (fun _ -> 1) ;;


let (smallest: proof_tree list -> proof_tree) = 
      let minimal_proof = 
	fun (min_prf,min_size) prf -> 
	      let prf_size = size prf in if prf_size < min_size then (prf,prf_size) else (min_prf,min_size)
      in
	function
	  | [] -> NoProof ("",facts,c)
	  | prf::prfs -> fst (List.fold_left minimal_proof (prf,size prf) prfs)
;;
*)


