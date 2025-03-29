open List

(* define the types (computations and values) and terms) *)
(* i have omitted dependant types, but we could add them*)

type tpV = 
| Unit
| Bool
| Num
| U of tpC             (* type of thUnk x *)
| Cross of tpV * tpV   (* pattern matched product p43 *)
| Sum of tpV * tpV
and 
tpC = 
| F of tpV             (* type of Force x *)
| Arrow of tpV * tpC
| LCross of tpC * tpC  (* ughh uhh lazy pair?!??!? what is its constructor/destructor. please add a pattern mathcing destructor*)

type tm = 
| Var of string
| True 
| False
| Int of int
| IfThEl of tm * tm * tm
| LetIn of string * tm * tm
| Pair of tm * tm 
| Fst of tm
| Snd of tm
| Case of tm * string * tm * string * tm
| Inl of tm
| Inr of tm
| Lam of (string * tm) list                  (* also called pop *)
| App of tm * tm                             (* also called push *)
| Produce of tm
| Force of tm
| Thunk of tm


(* type environment*)
type typ = TypV of tpV | TypC of  tpC

type env = (string * typ) list  


exception TypeBad of string 

(* p38 *)
(* typechecker: typing rules, use options to catch failure... (then later extend with helpful stuff??) *)
let rec typeof (env : env) (t : tm) : typ = 
  match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) env with 
      | None -> raise (TypeBad ("variable " ^ x ^ " is free"))
      | Some x ->  snd x )
  | True | False -> TypV Bool
  | Int x -> TypV Num
  | IfThEl (t1, t2, t3) -> (match (typeof env t1, typeof env t2,  typeof env t3) with 
      | (TypV Bool, x , y ) -> if x == y then x else raise (TypeBad ("branches of if-then-else don't match"))
      | _ -> raise (TypeBad ("if then else bad")))
  | LetIn (x, t1, t2) -> let tipe = typeof env t1 in typeof ((x, tipe) :: env) t2
  | Pair (t1, t2) -> (match typeof env t1, typeof env t2 with 
      | TypV x, TypV y -> TypV (Cross (x,y))
      | _ -> raise (TypeBad "Cross needs both things in it to be values, not computations"))   
  | Fst t -> (match typeof env t with 
      | TypV (Cross (x,_)) -> TypV x
      | _ -> raise (TypeBad "issue in fst"))
  | Snd t -> (match typeof env t with 
      | TypV (Cross (_,y)) -> TypV y
      | _ -> raise (TypeBad "issue in snd"))
  | Case (t,x,t1,y,t2) -> (match typeof env t with 
      | TypV (Sum ( a1, a2)) -> 
          let (b1,b2) = typeof ((x,TypV a1)::env) t1, typeof ((y,TypV a2)::env) t2 in 
          if b1 = b2 then b1 else raise (TypeBad "branches of sym type destructor don't type check")
      | _ -> raise (TypeBad "Case trying to match on non-sum type"))  (* TODO: need to define equality for types? *)
  | Inl t -> (match typeof env t with 
        | TypV (Sum (a1, a2)) -> TypV a1
        | _ -> raise (TypeBad "Inl isnt working:("))
  | Inr t -> (match typeof env t with 
      | TypV (Sum (a1, a2)) -> TypV a2
      | _ -> raise (TypeBad "Inl isnt working:("))
  | Lam x t 
  | App 
  | Produce 
  | Force 
  | Thunk




(* interpreter\evaluater: evaluation rules*)