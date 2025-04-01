open List

(* define the types (computations and values) and terms) *)
(* i have omitted dependant types, but we could add them*)

type tpV = 
| Unit
| Bool
| Nat
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
| Zero
| Suc of tm
| IfThEl of tm * tm * tm
| LetIn of string * tm * tm
| LazyPair of tm * tm 
| Fst of tm
| Snd of tm
| EagerPair of tm * tm
| PMPair of tm * string * string * tm
| Inl of tm
| Inr of tm
| Case of tm * string * tm * string * tm
| Lam of string * tpV * tm                  (* also called pop *)
| App of tm * tm                             (* also called push *)
| Produce of tm
| Force of tm
| Thunk of tm
| Print of string * tm


(* type environment*)
type ctx = (string * tpV) list  

exception TypeBad of string 

(*there is no variable shadowing. new declarations with the same name just overwrite*)
(*TODO: enforce anything added to context is a value type (right now this is enforced by ocamls type checker, so we dont display an error message got it. )*)

(* our type checker, split in to two mutually recursive functions. one for values and one for computations. *)
let rec typeofV (ctx:ctx) (t : tm) : tpV = match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) ctx with 
    | None -> raise (TypeBad ("variable " ^ x ^ " is free"))
    | Some x ->  snd x )
  | True | False -> Bool
  | Zero -> Nat
  | Suc x -> typeofV ctx x
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
  | Case (t,x,t1,y,t2) -> (match typeofV ctx t with        
    | Sum (a1, a2) -> 
        let (b1,b2) = typeofV ((x, a1)::(List.filter (fun z -> fst z != x ) ctx)) t1, typeofV ((y, a2)::(List.filter (fun z -> fst z != y ) ctx)) t2 in 
        if b1 = b2 then b1 else raise (TypeBad "branches of sym type destructor don't type check")
    | _ -> raise (TypeBad "Case trying to match on non-sum type")) 
  | EagerPair (t1, t2) -> (let (x,y) = typeofV ctx t1, typeofV ctx t2 in ECross (x,y))  
  | PMPair (t1, x, y, t2) -> (match typeofV ctx t with 
    | ECross (v1,v2) -> typeofV ([(x, v1);(y, v2)]  @ ctx) t2                             
    | _ -> raise (TypeBad ("match on eager pair bad")))
  | _ ->  raise (TypeBad ("supposed to be a value, but its not"))

and typeofC  (ctx : ctx) (t : tm) : tpC = match t with
  | Lam (x,a,t) -> Arrow( a, typeofC ((x,a)::(List.filter (fun z -> fst z != x ) ctx)) t)            
  | LetIn (x, t1, t2) -> typeofC ((x, typeofV ctx t1) :: (List.filter (fun z -> fst z != x ) ctx)) t2 
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
  | App (v,t2) -> (match typeofC ctx t with 
      | Arrow (tv,tc) -> if tv = typeofV ctx v then tc else raise (TypeBad "arg being passed doesnt match input type")
      | _ -> raise (TypeBad "second arg of application needs to be Arrow type"))
  | Print (s,t) -> typeofC ctx t 
  | _ ->  raise (TypeBad ("supposed to be a computation, but its not"))

  (* application has arguments in the order A A->B *)




(* interpreter\evaluater: evaluation rules*)
(* big step rules on page 45 *)
(* how to use continuations is defined on page 47, page 51 for print*)






exception Crash
exception TODO

(* define substitution [M/x]N*)
let rec subst m x n = raise TODO


(* we are gonna do a big step evaluator*)
let rec eval t = match t with
| Produce v -> Produce v
| LetIn (x,v,t') -> subst v x t'
| Force (Thunk t') -> eval t'
| PMPair (v1, x, y, v2)-> (match v1 with 
    | EagerPair (t1,t2) -> subst t2 y (subst t1 x v2)
    | _ -> raise Crash)
| App (t1,t2) -> 
| _ -> raise Crash



(* what is M to x.N || T on page 45? *)