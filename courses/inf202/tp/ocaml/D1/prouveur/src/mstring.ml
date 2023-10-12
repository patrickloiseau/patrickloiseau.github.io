let (pretty: string -> string) = fun string -> "\"" ^ string ^ "\"" ;;

let (int_of_digit: char -> int) = fun c -> (int_of_char c) - (int_of_char '0') ;;

let (is_digit: char -> bool) = fun c -> '0' <= c && c <= '9' ;;


let (string_to_list: string -> char list) = fun str -> 
      let lg = String.length str
      in
	let rec (get_chars_from: int -> char list) = fun i -> 
	      if i<0 
	      then []
	      else (String.get str i)::(get_chars_from (i-1))
	in 
	  get_chars_from (lg-1)
;;


let rec (list_to_string: char list -> string) = 
  function
    | [] -> ""
    | c::cs -> (String.make 1 c) ^ (list_to_string cs)
;;
