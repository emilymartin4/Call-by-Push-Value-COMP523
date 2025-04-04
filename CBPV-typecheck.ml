open List

(* define the types (computations and values) and terms) *)
(* i have omitted dependent types, but we could add them*)

type tpV = 
| Unit
| Bool
| Nat
| U of tpC    (* U B *)
| VCross of tpV * tpV  (* A x A' *)
| Sum of tpV * tpV (* A + A' *)
and 
tpC = 
| F of tpV     (* F A *)
| Arrow of tpV * tpC (* A -> B *)
| CCross of tpC * tpC   (* B x B'*)

(* terms with variables named using strings *)
type named_tm = 
| Var of string  
| Unit
| True 
| False
| Zero
| Succ of named_tm
| IfThEl of named_tm * named_tm * named_tm (* if t1 then t2 else t3*)
| LetIn of string * named_tm * named_tm (* let x = t1 in t2 *)
| CompPair of named_tm * named_tm  (* (t1, t2) *)
| Fst of named_tm (* fst t *)
| Snd of named_tm (* snd t *)
| ValPair of named_tm * named_tm (* (v1, v2) *)
| PMPair of named_tm * string * string * named_tm (* pm t1 as (x, y). t2 *)
| Inl of named_tm (* inl t *)
| Inr of named_tm (* inr t *)
| Case of named_tm * string * named_tm * string * named_tm (* pm V as inl x -> t1 | inl r -> t2 *)
| Lam of string * tpV * named_tm                (* also called pop *)
| App of named_tm * named_tm                           (* also called push *)
| Bind of named_tm * string * named_tm    (* t1 to x. t2 * <- check that what i added in the typechecker is correct *)
| Produce of named_tm (* produce t *)
| Force of named_tm (* force t *)
| Thunk of named_tm (* thunk t *)

type ctx = (string * tpV) list

exception TypeError of string 

(*there is no variable shadowing. new declarations with the same name just overwrite*)
(*TODO: enforce anything added to context is a value type (right now this is enforced by ocamls type checker, so we dont display an error message got it. )*)

(* our type checker, split in to two mutually recursive functions. one for values and one for computations. *)
let rec typeofV (ctx:ctx) (t : named_tm) : tpV = match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) ctx with 
    | None -> raise (TypeError ("variable " ^ x ^ " is free"))
    | Some x ->  snd x )
  | Unit -> Unit
  | True | False -> Bool
  | Zero -> Nat
  | Succ x -> typeofV ctx x
  | IfThEl (t1, t2, t3) -> (match (typeofV ctx t1, typeofV ctx t2,  typeofV ctx t3) with 
    | (Bool, x , y ) -> if x = y then x else raise (TypeError ("branches of if-then-else don't match"))
    | _ -> raise (TypeError ("if then else bad")))
  | Thunk t -> U (typeofC ctx t)
  | Inl t -> (match typeofV ctx t with 
    | Sum (a1, a2) -> a1
    | _ -> raise (TypeError "Inl isnt working:("))
  | Inr t ->(match typeofV ctx t with 
    | Sum (a1, a2) -> a2
    | _ -> raise (TypeError "Inr isnt working:("))
  | Case (t,x,t1,y,t2) -> (match typeofV ctx t with        
    | Sum (a1, a2) -> 
        let (b1,b2) = typeofV ((x, a1)::(List.filter (fun z -> fst z != x ) ctx)) t1, typeofV ((y, a2)::(List.filter (fun z -> fst z != y ) ctx)) t2 in 
        if b1 = b2 then b1 else raise (TypeError "branches of sym type destructor don't type check")
    | _ -> raise (TypeError "Case trying to match on non-sum type")) 
  | ValPair (t1, t2) -> (let (x,y) = typeofV ctx t1, typeofV ctx t2 in VCross (x,y))  
  | PMPair (t1, x, y, t2) -> (match typeofV ctx t with 
    | VCross (v1,v2) -> typeofV ([(x, v1);(y, v2)]  @ ctx) t2                             
    | _ -> raise (TypeError ("match on eager pair bad")))
  | _ ->  raise (TypeError ("supposed to be a value, but its not"))

and typeofC  (ctx : ctx) (t : named_tm) : tpC = match t with
  | Lam (x,a,t) -> Arrow( a, typeofC ((x,a)::(List.filter (fun z -> fst z != x ) ctx)) t)            
  | LetIn (x, v, t2) -> typeofC ((x, typeofV ctx v) :: (List.filter (fun z -> fst z != x ) ctx)) t2 
  | Produce t -> F (typeofV ctx t)
  | Force t -> (match typeofV ctx t with 
    | U t' -> t'
    | _ ->  raise (TypeError ("branches of if-then-else don't match")))
  | CompPair (t1, t2) -> (let (x,y) = typeofC ctx t1, typeofC ctx t2 in CCross (x,y))  
  | Fst t -> (match typeofC ctx t with 
      | CCross (x,_) -> x
      | _ -> raise (TypeError "issue in fst"))
  | Snd t -> (match typeofC ctx t with 
      | CCross (_,y) -> y
      | _ -> raise (TypeError "issue in snd"))
  | App (v,t2) -> (match typeofC ctx t with 
      | Arrow (tv,tc) -> if tv = typeofV ctx v then tc else raise (TypeError "arg being passed doesnt match input type")
      | _ -> raise (TypeError "second arg of application needs to be Arrow type"))
  | Bind (t1, x, t2) -> (match typeofC ctx t1 with
      | F a -> typeofC ((x, a) :: ctx) t2 
      | _ -> raise (TypeError "supposed to be a force, but it's not"))
  | _ -> raise (TypeError "Supposed to be a computation type but it's  not")
  (* application has arguments in the order A A->B *)




(* interpreter\evaluater: evaluation rules*)
(* big step rules on page 45 *)


(* terms with variables labeled using de bruijn indices (nameless representation)*)
type tm = 
| Var of int  
| Unit
| True 
| False
| Zero
| Succ of tm
| IfThEl of tm * tm * tm (* if t1 then t2 else t3*)
| LetIn of tm * tm (* let x = t1 in t2 *)
| CompPair of tm * tm  (* (t1, t2) *)
| Fst of tm (* fst t *)
| Snd of tm (* snd t *)
| ValPair of tm * tm (* (v1, v2) *)
| PMPair of tm * tm (* pm t1 as (x, y). t2 *)
| Inl of tm (* inl t *)
| Inr of tm (* inr t *)
| Case of tm * tm * tm (* pm t as inl x -> t1 | inl r -> t2 *)
| Lam of tpV * tm                (* also called pop *)
| App of tm * tm                           (* also called push *)
| Bind of tm * tm    (* t1 to x. t2 *)
| Produce of tm (* produce t *)
| Force of tm (* force t *)
| Thunk of tm (* thunk t *)

type name = string
type ctx = name list

(* convert from named representation to nameless representation *)
let rec debruijnify (context : ctx) (named_term : named_tm) : tm =
  match named_term with
  | Var x ->  (
        match List.find_index (fun y -> x = y) context with
        | Some i  -> Var i
        | None -> failwith ("Variable not found in context lookup"))
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> False
  | Succ t -> Succ (debruijnify context t)
  | IfThEl (t1, t2, t3) -> IfThEl (debruijnify context t1, debruijnify context t2, debruijnify context t3)
  | LetIn (x, t1, t2) -> LetIn (debruijnify context t1, debruijnify (x :: context) t2)
  | CompPair (t1, t2) -> CompPair (debruijnify context t1, debruijnify context t2)
  | Fst t -> Fst (debruijnify context t)
  | Snd t -> Snd (debruijnify context t)
  | ValPair (t1, t2) -> ValPair (debruijnify context t1, debruijnify context t2)
  | PMPair (t1, x, y, t2) -> PMPair (debruijnify context t1, debruijnify (x :: (y :: context)) t2) 
  | Inl t -> Inl (debruijnify context t)
  | Inr t -> Inr (debruijnify context t)
  | Case (t, x, t1, y, t2) -> Case (debruijnify context t, debruijnify (x :: context) t1, debruijnify (y :: context) t2) 
  | Lam (x, tp, t) -> Lam (tp, debruijnify (x :: context) t)              
  | App (t1, t2) -> App (debruijnify context t1, debruijnify context t2)
  | Bind (t1, x, t2) -> Bind (debruijnify context t1, debruijnify (x :: context) t2)  
  | Produce t -> Produce (debruijnify context t)
  | Force t -> Force (debruijnify context t)
  | Thunk t -> Thunk (debruijnify context t)

(* type environment*)

exception Crash
exception TODO

(* define shift up by d units with threshold c on a term t *)
let rec shift (c : int) (d : int) (t : tm) : tm = match t with
  | Var x -> if x < c then Var x else Var (x + d)
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> Zero
  | Succ t -> Succ (shift c d t)
  | IfThEl (t1, t2, t3) -> IfThEl (shift c d t1, shift c d t2, shift c d t3)
  | LetIn (t1, t2) -> LetIn (shift c d t1, shift (c + 1) d t2) 
  | CompPair (t1, t2) -> CompPair (shift c d t1, shift c d t2)
  | Fst t -> Fst (shift c d t)
  | Snd t -> Snd (shift c d t)
  | ValPair (t1, t2) -> ValPair (shift c d t1, shift c d t2)
  | PMPair (t1, t2) -> PMPair (shift c d t1, shift (c + 2) d t2)
  | Inl t -> Inl (shift c d t)
  | Inr t -> Inr (shift c d t)
  | Case (t, t1, t2) -> Case (shift c d t, shift (c + 1) d t1, shift (c + 1) d t2) (* pm t as inl x -> t1 | inl r -> t2 *)
  | Lam (tp, t) -> Lam (tp, shift (c + 1) d t)            (* also called pop *)
  | App (t1, t2) -> App (shift c d t1, shift c d t2)                         (* also called push *)
  | Bind (t1, t2) -> Bind (shift c d t1, shift (c + 1) d t2)   (* t1 to x. t2 *)
  | Produce t -> Produce (shift c d t)
  | Force t -> Force (shift c d t)
  | Thunk t -> Thunk (shift c d t)

(* substitute a term s for the variable j in t *)
let rec subst (s : tm) (j : int) (t : tm) : tm = match t with
  | Var x -> if x = j then s else Var x
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> Zero
  | Succ t -> Succ (subst s j t)
  | IfThEl (t1, t2, t3) -> IfThEl (subst s j t1, subst s j t2, subst s j t3)
  | LetIn (t1, t2) -> LetIn (subst s j t1, subst (shift 0 1 s) (j + 1) t2)
  | CompPair (t1, t2) -> CompPair (subst s j t1, subst s j t2)
  | Fst t -> Fst (subst s j t)
  | Snd t -> Snd (subst s j t)
  | ValPair (t1, t2) -> ValPair (subst s j t1, subst s j t2)
  | PMPair (t1, t2) -> PMPair (subst s j t1, subst (shift 0 2 s) (j + 2) t2) (* unsure about this case*)
  | Inl t -> Inl (subst s j t)
  | Inr t -> Inr (subst s j t)
  | Case (t, t1, t2) -> Case (subst s j t, subst (shift 0 1 s) (j + 1) t1, subst (shift 0 1 s) (j + 1) t2) (* pm t as inl x -> t1 | inl r -> t2 *)
  | Lam (tp, t) -> Lam (tp, subst (shift 0 1 s) (j + 1) t)            (* also called pop *)
  | App (t1, t2) -> App (subst s j t1, subst s j t2)                         (* also called push *)
  | Bind (t1, t2) -> Bind (subst s j t1, subst (shift 0 1 s) (j + 1) t2)   (* t1 to x. t2 *)
  | Produce t -> Produce (subst s j t)
  | Force t -> Force (subst s j t)
  | Thunk t -> Thunk (subst s j t)


(* we are gonna do a big step evaluator*)
let rec eval (t : tm) = match t with
| Var x -> raise Crash
| Unit -> Unit
| True -> True
| False -> False
| Zero -> Zero
| Succ t -> Succ (eval t)
| IfThEl (t1, t2, t3) -> IfThEl (eval t1, eval t2, eval t3)
| LetIn (v, t2) -> eval (subst v 0 t2)
| CompPair (t1, t2) -> CompPair (t1, t2) (* is this right ?? *)
| Fst t -> (match eval t with
  | CompPair (n1, n2) -> eval n1
  | _ -> raise Crash
)
| Snd t -> (match eval t with
| CompPair (n1, n2) -> eval n2
| _ -> raise Crash
)
| ValPair (t1, t2) -> ValPair (t1, t2)
| PMPair (v, t2) -> (match v with
    | ValPair (v1, v2) -> subst v2 0 (subst v1 0 t2)
    | _ -> raise Crash)
| Inl t -> Inl t (* is this right? is this guaranteed to be a value? *)
| Inr t -> Inr t
| Case (t, t1, t2) -> (match t with
  | Inl x -> eval (subst x 0 t1)
  | Inr y -> eval (subst y 0 t2)
  | _ -> raise Crash
)
| Lam (tp, t) -> Lam (tp, t)         
| App (v, t2) -> (match eval t2 with
  | Lam (tp, t) -> eval (subst v 0 t) (* how is it guaranteed that v is a value? i guess because it wouldn't have typechecked otherwise? *)
  | _ -> raise Crash
)                    (* also called push *)
| Bind (t1, t2) -> (match eval t1 with
  | Produce v -> eval (subst v 0 t2)
  | _ -> raise Crash
)
| Produce v -> Produce v
| Force t -> (match eval t with
  | Thunk t1 -> t1
  | _ -> raise Crash)
| Thunk t -> Thunk t


(* transpiler from CBN to CBPV p277
Wrap any arguments (things being applied to a lam) in thunks to delay evaluation.
*)

