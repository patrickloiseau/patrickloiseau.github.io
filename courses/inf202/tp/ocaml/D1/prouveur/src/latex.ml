
type latex = string 

type t = latex

let (macro: string -> string list -> latex) = fun name args -> 
      String.concat "" [ "\\" ; name ; "{" ; String.concat "}{" args ; "}" ]

let (group: string list -> latex) = fun strings -> "{" ^ (String.concat " " strings) ^ "}"

let (math:string -> latex) = fun string -> macro "ensuremath" [ string ] ;;

let (par: string -> latex) = fun string -> "\\big(" ^ string ^ "\\big)"

let (bracket: string -> latex) = fun string -> group [ "[" ; string ; "]" ]

let (infer: string list -> string -> string list -> latex) = fun rule conclusion proofs ->
      let macro_infer = 
	match rule with
	| []      -> macro "infer"
	| strings -> macro ("infer[" ^ (String.concat "" strings) ^ "]")
      in
	macro_infer [conclusion ; String.concat " & " proofs ]
;;

let (subscript: string -> string -> latex) = fun str1 str2 -> str1 ^ "_" ^ (group [str2]) ;;
