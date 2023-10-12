module Formule = Term

open Formule
open Proof
open Proof_scheme

(* EXPLAINATION LEVEL *)

let _x_ = 1 ;;


(* The rule for application of a definition

   A definition is represented as a function d such that:  d [e1;...;en] = ( T1, T2 )   where T1 =def= T2

        proof_of
	---------
	    T1
	----------- def d [e1 ; ... ; en] 
	    T2


        proof_of
	---------
	    T2
	----------- def d [e1 ; ... ; en ]
	    T1
*)


type arguments = term list ;;

type def = name * (arguments -> (term * term)) ;;

exception Improper of string
 
let (=$=) x y = (x,y) ;;

let (inrel: Term.t -> Term.t -> Term.t -> Term.t) = fun x r y -> Op("",[x;r;y])

let (_definitions: (def list) ref) = ref
    [  ("neg" , function [a]   -> 
	  ( Neg a )
	    =$= 
	  ( Impl(a,False) )
       ) 
    ;  ("<=>" , function [a;b] -> 
	  ( Pred("<=>",[a;b]) ) 
	    =$= 
	  ( Et(Impl(a,b),Impl(b,a)) )
       )
    ; ("qq-in", function [x;ens;p] -> 
          Pred("QQ", [x;ens;p]),
	  Qq(x, Impl( Pred(":",[x;ens]) , p)) 
      )
    ]
;;

let (>>) = Proof.bind ;;

type usage = Exploit | Apply ;;

let (usedef: usage -> name -> arguments -> prover -> prover) = fun usage name args proof_of ->
      fun (facts,c) ->
	    Explain.starts _x_ [ Explain.rule [ "Def" ; Mstring.pretty name ; Term.prettys args] ] ; 
	    try 
	      let d = List.assoc name !_definitions
	      in let (t1,t2) = (d args)
	      in let (t_above,t_under) = 
		begin
	(* FIXME:	  if (Term.unifiable c t2) then Term.unify c t2 else [] ; *)
		  (match usage with
		  | Exploit -> if c=t2 then (t2,t1) else (t1,t2)
		  | Apply   -> if c=t2 then (t1,t2) else (t2,t1)
		  )
		end
	      in
		(match usage with
		| Exploit -> Explain.print _x_ [ Explain.leadsto 1 [ Term.pretty t_above ] ]  
		| Apply   -> Explain.print _x_ [ Explain.leadsto 1 [ Term.pretty t_above ] ]  
		) ;
		Explain.returns _x_
		  ( 
		    (proof_of (facts,t_above)) >> (fun p -> return (Proof_scheme.DEF_apply(name,args,p,t_under)) )
		  )
	    with Not_found -> 
		  let msg =  String.concat " " ["Def.apply: no def for" ; name]
		  in 
		    begin
		      Explain.print _x_ [ msg ] ;
		      Explain.returns _x_ 
			( return (Proof_scheme.NoProof(msg,Hyp.hyps_of facts,c)) )
		    end
;;

let   (apply: name -> arguments -> prover -> prover) = usedef Apply   ;;
let (exploit: name -> arguments -> prover -> prover) = usedef Exploit ;;




