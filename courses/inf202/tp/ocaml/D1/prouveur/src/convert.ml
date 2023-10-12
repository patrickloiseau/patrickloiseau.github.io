
(* CONVERTION Proof_scheme -> Proof_tree *)

let rec (ps_to_pt: Proof_scheme.t -> Proof_tree.t) = 
  function
    | Proof_scheme.Error msg -> Proof_tree.Error msg
    | Proof_scheme.NoProof (hyps,conclusion,msg) -> Proof_tree.NoProof (hyps,conclusion,msg)
	      
    | Proof_scheme.A(i) -> Proof_tree.A(i)
    | Proof_scheme.ADP(i,conclusion) -> Proof_tree.ADP(i,conclusion)
	  
    | Proof_scheme.HYP_apply(h) -> Proof_tree.HYP_apply(Ens.singleton h, h, Proof_scheme.conclusion_of_hyp h) 
	      
    | Proof_scheme.IMPL_elim(ps1,ps2) ->
	    let pt1 = ps_to_pt ps1 and pt2 = ps_to_pt ps2
	    in let implication = Proof_tree.conclusion_of pt2
	    in let hyps = Ens.union (Proof_tree.hypotheses_of pt1) (Proof_tree.hypotheses_of pt2)  
	    in Proof_tree.IMPL_elim(hyps, pt1, pt2, Term.conclusion implication)
		
    | Proof_scheme.IMPL_intro(h,ps) -> 
	    let pt = ps_to_pt ps
	    in let hyps = Ens.minus (Proof_tree.hypotheses_of pt) (Ens.singleton h)
	    in Proof_tree.IMPL_intro(hyps, h, pt, Term.Impl (Proof_scheme.conclusion_of_hyp h, Proof_tree.conclusion_of pt))

    | Proof_scheme.ET_elim(i,ps) -> 
	    let pt = ps_to_pt ps 
	    in Proof_tree.ET_elim(Proof_tree.hypotheses_of pt, i, pt, Term.subterm i (Proof_tree.conclusion_of pt))

    | Proof_scheme.ET_intro(ps1,ps2) ->
	    let pt1 = ps_to_pt ps1 and pt2 = ps_to_pt ps2
	    in let hyps = Ens.union (Proof_tree.hypotheses_of pt1) (Proof_tree.hypotheses_of pt2)
	    in Proof_tree.ET_intro(hyps, pt1, pt2, Term.Et(Proof_tree.conclusion_of pt1, Proof_tree.conclusion_of pt2))

    | Proof_scheme.OU_intro(i,ps,f) ->
	    let pt = ps_to_pt ps
	    in let hyps = Proof_tree.hypotheses_of pt
	    in let c = (if i=1 then Term.Ou(Proof_tree.conclusion_of pt,f) else Term.Ou(f,Proof_tree.conclusion_of pt))
	    in Proof_tree.OU_intro(hyps, i, pt, f, c)

    | Proof_scheme.OU_elim(ps,ps1,ps2) ->
	    let pt = ps_to_pt ps and pt1 = ps_to_pt ps1 and pt2 = ps_to_pt ps2
	    in let hyps = Ens.big_union (List.map Proof_tree.hypotheses_of [pt;pt1;pt2])
               and c1 = Term.conclusion (Proof_tree.conclusion_of pt1)
	       and c2 = Term.conclusion (Proof_tree.conclusion_of pt2)
	    in let c = c1
	    in Proof_tree.OU_elim(hyps, pt, pt1, pt2, c)

    | Proof_scheme.EQ_trans(pss) ->
	    let pts = List.map ps_to_pt pss
	    in let hyps = Ens.big_union (List.map Proof_tree.hypotheses_of pts)
	    and conc = (Term.eq 
			  (Term.left (Proof_tree.conclusion_of (List.hd pts))) 
			  (Term.right (Proof_tree.conclusion_of (Mlist.last pts))) )
	    in Proof_tree.EQ_trans(hyps,pts,conc)

    | Proof_scheme.EQ_elim(prop,a,b,ps_a,ps_a_eq_b) ->
	    let pt_a = ps_to_pt ps_a and pt_a_eq_b = ps_to_pt ps_a_eq_b
	    in let hyps = Ens.union (Proof_tree.hypotheses_of pt_a) (Proof_tree.hypotheses_of pt_a_eq_b)
	    in let conc = prop b
	    in Proof_tree.EQ_elim(hyps,prop,a,b,pt_a,pt_a_eq_b,conc)

    | Proof_scheme.ABS_intro(ps1,ps2) ->
	    let pt1 = ps_to_pt ps1 and pt2 = ps_to_pt ps2
	    in let hyps = Ens.union (Proof_tree.hypotheses_of pt1) (Proof_tree.hypotheses_of pt2)
	    in Proof_tree.ABS_intro(hyps, pt1, pt2)

    | Proof_scheme.ABS_elim(ps,c) ->
	    let pt = ps_to_pt ps
	    in Proof_tree.ABS_elim(Proof_tree.hypotheses_of pt, pt, c)

    | Proof_scheme.NEGNEG_elim(ps) ->
	    let pt = ps_to_pt ps
	    in let conc = 
	      (match Proof_tree.conclusion_of pt with
(*	      | Term.Neg(Term.Neg(c))
	      | Term.Neg(Term.Impl(c,Term.False))
*)
	      |	Term.Impl(Term.Impl(c,Term.False),Term.False) -> c
	      |	c -> Term.error [ "convert.ps_to_pt:" ; Term.pretty c ]
	      )
	    in Proof_tree.NEGNEG_elim(Proof_tree.hypotheses_of pt, pt, conc)

    | Proof_scheme.DEF_apply(name,args,ps,c) ->
	    let pt = ps_to_pt ps
	    in Proof_tree.DEF_apply(Proof_tree.hypotheses_of pt, name, args, pt, c)

    | Proof_scheme.REC(var,domain,prop,pss) ->
	    let pts = List.map ps_to_pt pss
	    in let hyps = Ens.big_union (List.map Proof_tree.hypotheses_of pts)
	    in let c = Term.Qr(var,domain,prop var)
	    in Proof_tree.REC(hyps,var,domain,prop,pts,c)

    | Proof_scheme.QQ_elim(prop,e,ps) ->
	    let pt = ps_to_pt ps 
	    in let Term.Qq(u,_) = Proof_tree.conclusion_of pt
	    in let x = Term.V(Term.id u) 
	    in let c = prop e
	    in Proof_tree.QQ_elim(Proof_tree.hypotheses_of pt, prop, x, e, pt, c)

    | Proof_scheme.QQ_intro(prop,x,x0,ps) ->
	    let pt = ps_to_pt ps and c = Term.Qq(x,prop x)
	    in Proof_tree.QQ_intro(Proof_tree.hypotheses_of pt, prop, x, x0, pt, c)

    | Proof_scheme.EX_intro(prop,x,e,ps) ->
	    let pt = ps_to_pt ps and c = Term.Ex(x,prop x)
	    in Proof_tree.EX_intro(Proof_tree.hypotheses_of pt, prop, x, e, pt, c)

    | Proof_scheme.EX_elim(pse,psq) ->
	    let pte = ps_to_pt pse 
	    and ptq = ps_to_pt psq 
	    in let hyps = Ens.union (Proof_tree.hypotheses_of pte) (Proof_tree.hypotheses_of ptq)
	    and Term.Qq(_,Term.Impl(_,conc)) = Proof_tree.conclusion_of ptq
	    and Term.Ex(x,p_x) = Proof_tree.conclusion_of pte
	    in Proof_tree.EX_elim(hyps, x, p_x, pte, ptq, conc)

    | Proof_scheme.AXM_apply(name,c) -> Proof_tree.AXM_apply(name,c)

    | Proof_scheme.Gap(ps,c) -> 
	    let pt = ps_to_pt ps 
	    in Proof_tree.Gap(Proof_tree.hypotheses_of pt, pt,c)	
;;


let (proof_scheme_to_proof_tree: Proof_scheme.t -> Proof_tree.t) = fun ps ->
      let pt = ps_to_pt ps
      in 
	begin 
	  Proof_tree.is_valid pt ;
	  pt
	end






