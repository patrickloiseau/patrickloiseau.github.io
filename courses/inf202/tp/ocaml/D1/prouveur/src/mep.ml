let appliquer = List.map ;;

(* affichage d'un noeud *)

let (noeud_vers_ch : int -> string) = 
 function n -> "" ^ (string_of_int n) ^ ""
;;

(* affichage d'un arbre binaire *)

type colonne = string list

let rec (n_fois : int * string -> string) =  
  function (n,s) ->  
	if n<=0 then ""
	else s ^ (n_fois (n-1,s))          
;;                                 

let rec (largeur_max: colonne -> int) = 
  function
    | [] -> 0
    | ch::s -> max (String.length ch) (largeur_max s) 
;;


let (titrer : string * colonne -> colonne) = 
  function (titre,col) -> 
	let lc = largeur_max col        
	in let lt = String.length titre 
	in let ne = (lc - lt)/2         
	in ((n_fois (ne," ")) ^ titre) :: col 
;;

let (completer_chaine : int * string -> string) =
  function (larg,ch) -> 
	let lch = (String.length ch)
	in ch ^ (n_fois (larg-lch," ")) 
;;


(* justificaiton d'une colonne *)

type alignement = Gauche | Droite | Centre ;;

let (justifier_chaine: alignement -> int -> string -> string) = 
  function alignement -> function largeur -> function str -> 
	let espace = ' '
	and debug_mark = ""
	in let l = String.length str 
	in let d = abs (largeur-l)
	in let (q,r) = ( d / 2, d mod 2 )
	in let (decalage_g,decalage_d) = if r=0 then (q,q) else (q,q+r)
	in 
	  match alignement with
	  | Gauche -> str ^ debug_mark ^ (String.make (decalage_g+decalage_d) espace) 
	  | Droite -> (String.make (decalage_g+decalage_d) espace) ^ debug_mark ^ str 
	  | Centre -> (String.make decalage_g espace) ^ debug_mark ^ str ^ debug_mark ^ (String.make decalage_d espace) 
;;

let (centrer_chaine: int -> string -> string) = justifier_chaine Centre ;;

let (justifier_colonne: alignement -> colonne -> colonne) = 
  let rec (justifier_colonne_rec: alignement -> int -> colonne -> colonne) = 
    function alignement -> function largeur -> 
	  function
	    | [] -> []
	    | l::ls -> (justifier_chaine alignement largeur l) :: (justifier_colonne_rec alignement largeur ls)
  in
    function alignement -> function colonne ->
	  let largeur = largeur_max colonne
	  in justifier_colonne_rec alignement largeur colonne
;;

let (centrer_colonne: colonne -> colonne) = justifier_colonne Centre ;;
  

(* colonne avec taille *)

type colonne_ajustée = colonne * int

let (ajuster_colonne: colonne -> colonne_ajustée) = 
  function col ->                         
	let l = largeur_max col                    
	in let colaj =                         
	  (* appliquer (fun ch -> completer_chaine (l,ch)) *)
	    col 
	in (colaj, l)                          
;;



let rec (coller: colonne_ajustée * colonne_ajustée -> colonne) = 
  function ((col1,l1),(col2,l2)) -> 
	let sep = "  " 
	in let espace = " "
	in let limite = ""
	in
	  match (col1,col2) with          
	  | ([],[]) -> []                
	  | (ligneA::s1 , ligneB::s2) -> 
		  (limite ^ ligneA ^ sep ^ ligneB ^ limite) :: (coller ((s1,l1),(s2,l2)))
	  | ([],ch2::s2) ->           
		  (limite ^ (n_fois (l1,espace)) ^ sep ^ ch2 ^ limite) :: (coller (([],l1),(s2,l2)))
	  | (ch1::s1,[]) ->              
		  (limite ^ ch1 ^ (n_fois(l2,espace)) ^ limite) :: (coller ((s1,l1),([],l2)))
;;

let (coller_colonne: colonne * colonne -> colonne) = 
  function (col1,col2) ->
	match col1,col2 with
	| [],[] -> []
	| _,[] -> col1
	| [],_ -> col2
	| _,_ -> coller (ajuster_colonne (justifier_colonne Gauche col1), ajuster_colonne (justifier_colonne Gauche col2)) 
;;

let rec (fusionner: colonne list -> colonne) = 
  function
    | [] -> []
    | c::cs -> coller_colonne (c, fusionner cs)
;;


let rec (colonne_vers_chaine : colonne -> string) =
  function 
    | [] -> ""                          
    | ch::s -> ch ^ "\n" ^ (colonne_vers_chaine s)   
;;



type rcolonne = colonne (* colonne renversée *)

let (rcol: string -> rcolonne) = function str -> [str] ;;

let (largeur_base: rcolonne -> int) = 
  function
    | [] -> 0 
    | l::_ -> String.length l
;;


(* APPLICATION : affichage d'un arbre binaire *)

type 't abin = 
  | Av 
  | Ab of 't abin * 't * 't abin

let rec (arbre_vers_colonne : ('t -> string) -> 't abin -> colonne) = 
  function pretty -> 
	function 
	  | Av -> []
	  | Ab(Av,n,Av) -> [ noeud_vers_ch n ]
	  | Ab(ag,n,Av) -> titrer (noeud_vers_ch n, 
				   coller_colonne( titrer (" /\\", arbre_vers_colonne pretty ag),[" "])
							  )


	  | Ab(ag,n,ad) -> 
		  let    colG = arbre_vers_colonne pretty ag
		  in let colD = arbre_vers_colonne pretty ad
		  in let colGt = titrer ("/",colG)
		  in let colDt = titrer ("\\",colD)
		  in let colGD = coller_colonne (colGt , colDt)
		  in titrer (noeud_vers_ch n, colGD) 
;;


	      
let (* USER *) rec (arbre_vers_chaine : ('t -> string) -> 't abin -> string) =  
  function pretty -> function a ->                              
	colonne_vers_chaine (arbre_vers_colonne pretty a)
;;

let (* USER *) (print_abin : int abin -> unit) = 
  function a -> print_string (arbre_vers_chaine string_of_int a) 
;;
