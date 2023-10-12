type 'elt ens = 'elt list ;;

type 'elt t = 'elt ens ;;

let empty = [] ;;

let (belongs: 'elt -> 'elt ens -> bool) = fun e ens -> List.mem e ens ;;

let rec (add: 'elt -> 'elt ens -> 'elt ens) = fun t ens ->
      if belongs t ens 
      then ens
      else t::ens
;;

let (union: 'elt ens -> 'elt ens -> 'elt ens) = fun ens1 ens2 ->
  List.fold_left (fun ens e -> add e ens) ens2 ens1
;;			

let (singleton: 'elt -> 'elt ens) = fun elt -> add elt empty ;;

let rec (elements: 'elt ens -> 'elt list) =  fun l -> l ;;

let rec (minus: 'elt ens -> 'elt ens -> 'elt ens) = fun e1 e2 -> 
      let (in_e2,others) = List.partition (fun elt -> belongs elt e2) e1
      in others
;;

let (big_union: ('elt ens) ens -> 'elt ens) = fun bigens ->
  List.fold_left (fun acc ens -> union ens acc) empty bigens
;;
