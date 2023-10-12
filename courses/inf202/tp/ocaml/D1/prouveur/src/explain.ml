
let _explain_level = ref 0 (* must be >0 for more explanation *) ;;

let (print: int -> string list -> unit) = fun level strings -> 
      if level > !_explain_level
      then ()
      else print_string (String.concat "" ["<LI>" ; String.concat " " strings ; "</LI>"])
;;

let (starts: int -> string list -> unit) = fun level strings -> 
      if level > !_explain_level
      then ()
      else print_string (String.concat "" ["<UL><LI>" ; String.concat " " strings ])
;;

let (ends: int -> unit) = fun level ->
      if level > !_explain_level
      then ()
      else print_string ("</LI></UL>")
;;

let (returns: int -> 't -> 't) = fun level result ->
      begin
	if level > !_explain_level then () else print_string ("</LI></UL>") ;
	result
      end
;;


(* OUTPUT FORMAT *)

let (dec:int) = 2 ;;


type html = string

type text = string list 

let (html: text -> html) = String.concat " " ;;

let (color: string -> text -> html) = fun color text -> String.concat "" [ "<FONT color=" ; color ; ">" ; html text ; "</FONT>"]

let (balise: string -> text -> html) = fun balise text -> String.concat "" [ "<" ; balise ; ">" ; html text ; "</" ; balise ; ">" ] 

let (bold: text -> html) = balise "B" ;;

let (italic: text -> html) = balise "I" ;;

let ($) style1 style2 = fun text -> style1 [ style2 text ] ;;

(* STYLE *)

let (rule: text -> string) = fun text -> bold ("APPLY" :: text) ;;

let (hypothesis: text -> html) = bold $ (color "green") ;;

let (goal: text -> html) =  bold $ (color "blue") ;;

let (leadsto: int -> text -> html) = fun n text -> 
      let msg = if n=1 then "The new goal is" else "The new goals are" in
	html ( (bold [msg]) :: text) 

let (strategy: text -> html) = italic ;;

let (exploit: text -> html) = color "red" ;;

let (warning: text -> html) = color "red" ;;

let (failure: text -> html) = color "orange" ;;

let (success: text -> html) = color "green" ;;

let (prover: text -> html) = fun text -> bold (List.map String.capitalize text) ;;
