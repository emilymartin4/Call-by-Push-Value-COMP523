open List

(* define the types (computations and values) and terms) *)
(* i have omitted dependant types, but we could add them*)

type tpV = 
| Unit
| Bool
| Num
| U of tpC             (* type of thUnk x *)
| ECross of tpV * tpV   (* pattern matched product p43 *)
| Sum of tpV * tpV
and 
tpC = 
| F of tpV             (* type of Force x *)
| Arrow of tpV * tpC
| LCross of tpC * tpC  



(* terms/expressions (whats even the difference)*)
type tm = 
| Var of string
| True 
| False
| Int of int
| IfThEl of tm * tm * tm
| LetIn of string * tm * tm
| LazyPair of tm * tm 
(*
| Match... of tm
*)
| Fst of tm
| Snd of tm
| EagerPair of tm * tm
| Match of tm * string * string * tm
| Inl of tm
| Inr of tm
| Case of tm * string * tm * string * tm
| Lam of string * tpV * tm                  (* also called pop *)
| App of tm * tm                             (* also called push *)
| Produce of tm
| Force of tm
| Thunk of tm


(* type environment*)
type ctx = (string * tpV) list  


exception TypeBad of string 

(* p38 *)
(* TODO: refactor with a type of for values and a type of for computations following page 44*)
(* typechecker: typing rules, use options to catch failure... (then later extend with helpful stuff??) *)
(*todo: enforce anything added to environment is a value type*)
let rec typeofV (ctx : ctx) (t : tm) : tpV = match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) ctx with 
    | None -> raise (TypeBad ("variable " ^ x ^ " is free"))
    | Some x ->  snd x )
  | True | False -> Bool
  | Int x -> Num
  | IfThEl (t1, t2, t3) -> (match (typeofV ctx t1, typeofV ctx t2,  typeofV ctx t3) with 
    | (Bool, x , y ) -> if x = y then x else raise (TypeBad ("branches of if-then-else don't match"))
    | _ -> raise (TypeBad ("if then else bad")))
  | Thunk t -> U (typeofC ctx t)
  | Inl t -> (match typeofV ctx t with 
    | Sum (a1, a2) -> a1
    | _ -> raise (TypeBad "Inl isnt working:("))
  | Inr t ->(match typeofV ctx t with 
    | Sum (a1, a2) -> a2
    | _ -> raise (TypeBad "Inr isnt working:("))
  | Case (t,x,t1,y,t2) -> (match typeofV ctx t with        (* TODO: check that a is a value becaore putting in context!! (helper function that uses list module) *)
    | Sum (a1, a2) -> 
        let (b1,b2) = typeofV ((x, a1)::ctx) t1, typeofV ((y, a2)::ctx) t2 in 
        if b1 = b2 then b1 else raise (TypeBad "branches of sym type destructor don't type check")
    | _ -> raise (TypeBad "Case trying to match on non-sum type"))  (* TODO: need to define equality for types? *)
  | EagerPair (t1, t2) -> (let (x,y) = typeofV ctx t1, typeofV ctx t2 in ECross (x,y))  
  | Match (t1, x, y, t2) -> (match typeofV ctx t with 
    | ECross (v1,v2) -> typeofV ([(x, v1);(y, v2)]  @ ctx) t2                               (* TODO: check that a is a value becaore putting in context!! (helper function that uses list module) *)
    | _ -> raise (TypeBad ("match on eager pair bad")))
  | _ ->  raise (TypeBad ("supposed to be a value, but its not"))

and typeofC  (ctx : ctx) (t : tm) : tpC = match t with
  | Lam (x,a,t) -> Arrow( a, typeofC ((x,a)::ctx) t)                      (* TODO: check that a is a value becaore putting in context!! (helper function that uses list module) *)
  | LetIn (x, t1, t2) -> (let a = typeofV ctx t1 in                   (* type annotation needed? *)
      typeofC ((x, a) :: ctx) t2 )
  | Produce t -> F (typeofV ctx t)
  | Force t -> (match typeofV ctx t with 
    | U t' -> t'
    | _ ->  raise (TypeBad ("branches of if-then-else don't match")))
  | LazyPair (t1, t2) -> (let (x,y) = typeofC ctx t1, typeofC ctx t2 in LCross (x,y))  
  | Fst t -> (match typeofC ctx t with 
      | LCross (x,_) -> x
      | _ -> raise (TypeBad "issue in fst"))
  | Snd t -> (match typeofC ctx t with 
      | LCross (_,y) -> y
      | _ -> raise (TypeBad "issue in snd"))
  | _ ->  raise (TypeBad ("supposed to be a computation, but its not"))






(* interpreter\evaluater: evaluation rules*)