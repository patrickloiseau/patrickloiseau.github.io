
type 't some = 
  | None
  | Some of 't


type 't option = 
  | Fail of string
  | Succ of 't

type 't gender = 
  | Mal of 't 
  | Fem of 't 
