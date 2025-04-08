open List

(* define the types (computations and values) and terms) *)
(* i have omitted dependent types, but we could add them*)

type tpV = 
| Unit
| Bool
| Nat
| U of tpC    (* U B *)
| VCross of tpV * tpV  (* A x A' *)
| Sum of tpV * tpV (* A + A' *) (* value, so just thunk it as so: thunk (inl (thunk t)) if you want it computation*)
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
| IsZero of named_tm
| IfThEl of named_tm * named_tm * named_tm (* if t1 then t2 else t3*)
| LetIn of string * named_tm * named_tm (* let x = t1 in t2 *)
| CompPair of named_tm * named_tm  (* (t1, t2) *)
| Fst of named_tm (* fst t *)
| Snd of named_tm (* snd t *)
| ValPair of named_tm * named_tm (* (v1, v2) *)
| PMPair of named_tm * string * string * named_tm (* pm t1 as (x, y). t2 *)
| Inl of named_tm * tpV (* inl t (the other type is a) *)
| Inr of named_tm * tpV (* inr t *)
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
(* check inl and inr - they are being used to destruct a sum type instead of construct one <- Emily*)
let rec typeofV (ctx:ctx) (t : named_tm) : tpV = match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) ctx with 
    | None -> raise (TypeError ("Variable " ^ x ^ " is free"))
    | Some x ->  snd x )
  | Unit -> Unit
  | True -> Bool
  | False -> Bool
  | Zero -> Nat
  | Succ x -> typeofV ctx x
  | IsZero n -> (match typeofV ctx n with 
    | Nat -> Bool
    | _ -> raise (TypeError ("IsZero must be applied to something of type Nat")))
  | IfThEl (t1, t2, t3) -> (match (typeofV ctx t1, typeofV ctx t2,  typeofV ctx t3) with 
    | (Bool, x, y) -> if x = y then x else raise (TypeError ("Types of branches of if-then-else don't match"))
    | _ -> raise (TypeError ("Either the scrutinee of if-then-else isn't a Bool, or the branches aren't value types")))
  | Thunk t -> U (typeofC ctx t)
  | Inl (t, a) -> Sum (typeofV ctx t, a) 
  | Inr (t, a) -> Sum (a, typeofV ctx t) 
  | Case (t,x,t1,y,t2) -> (match typeofV ctx t with        
    | Sum (a1, a2) -> 
        let (b1,b2) = typeofV ((x, a1)::(List.filter (fun z -> fst z != x ) ctx)) t1, typeofV ((y, a2)::(List.filter (fun z -> fst z != y ) ctx)) t2 in 
        if b1 = b2 then b1 else raise (TypeError "Types of branches of case don't match")
    | _ -> raise (TypeError "Case trying to match on something other than a Sum type")) 
  | ValPair (t1, t2) -> (let (x,y) = typeofV ctx t1, typeofV ctx t2 in VCross (x,y))  
  | PMPair (t1, x, y, t2) -> (match typeofV ctx t1 with 
    | VCross (v1,v2) -> typeofV ([(x, v1);(y, v2)]  @ ctx) t2                             
    | _ -> raise (TypeError ("Using PMPair on non-VCross type")))
  | _ ->  raise (TypeError ("Supposed to be a value, but it isn't"))


and typeofC  (ctx : ctx) (t : named_tm) : tpC = match t with
  | Lam (x,a,t) -> Arrow( a, typeofC ((x,a)::(List.filter (fun z -> fst z != x ) ctx)) t)            
  | LetIn (x, v, c) -> typeofC ((x, typeofV ctx v) ::  ctx) c 
  | Produce t -> F (typeofV ctx t)
  | Force t -> (match typeofV ctx t with 
    | U t' -> t'
    | _ -> raise (TypeError ("Must force a Thunk")))
  | CompPair (t1, t2) -> (let (x,y) = typeofC ctx t1, typeofC ctx t2 in CCross (x,y))  
  | Fst t -> (match typeofC ctx t with 
      | CCross (x,_) -> x
      | _ -> raise (TypeError "Fst needs to be applied to a computation pair"))
  | Snd t -> (match typeofC ctx t with 
      | CCross (_,y) -> y
      | _ -> raise (TypeError "Snd needs to be applied to a computation pair"))
  | App (v,t2) -> (match typeofC ctx t2 with 
      | Arrow (tv,tc) -> if tv = typeofV ctx v then tc else raise (TypeError "Argument passed doesn't match function's input type")
      | _ -> raise (TypeError "second arg of application needs to be Arrow type"))
  | Bind (t1, x, t2) -> (match typeofC ctx t1 with
      | F a -> typeofC ((x, a) :: (List.filter (fun z -> fst z != x ) ctx)) t2 
      | _ -> raise (TypeError "Can only bind a Force type"))
  | _ -> raise (TypeError "Supposed to be a computation type, but it's not")
  (* application has arguments in the order A A->B *)

(*
   

TODO: test typechecker

*)
let test_typeofC_success (context :ctx) (tm: named_tm) ( ty : tpC) = 
  try typeofC context tm = ty with
| TypeError x -> false

let test_typeofC_failure (context :ctx) (tm: named_tm) : string = 
  try let _ = typeofC context tm in "false" with 
| TypeError x -> x

let test_typeofV_success (context :ctx) (tm: named_tm) ( ty : tpV) = 
  try typeofV context tm = ty with
| TypeError _ -> false

let test_typeofV_failure (context :ctx) (tm: named_tm) : string = 
  try let _ = typeofV context tm in "false" with 
| TypeError x -> x


(* test cases for typeofV where the typechecker should succeed *)
let test_1 = test_typeofV_success [] (PMPair (ValPair (True, False), "x", "y", Var "x")) Bool
let test_2 = test_typeofV_success [("x", Nat)] (Succ (Var "x")) Nat
let test_3 = test_typeofV_success [("x", Nat)] (IsZero (Var "x")) Bool
let test_4 = test_typeofV_success [("x", Bool)] (IfThEl (Var "x", Succ Zero, Succ (Succ Zero))) Nat
let test_5 = test_typeofV_success [] (Thunk (Lam ("x", Nat, Produce (Succ (Var "x"))))) (U (Arrow (Nat, F Nat)))
let test_6 = test_typeofV_success [] (Inl (True, Nat)) (Sum (Bool, Nat))
let test_7 = test_typeofV_success [] (Case (Inl (True, Nat), "x", Var "x", "y", False)) Bool
let test_8 = test_typeofV_success [] (ValPair (True, False)) (VCross (Bool, Bool))
let test_9 = test_typeofV_success [("x", Nat)] (PMPair (ValPair (True, False), "x", "y", Var "x")) Bool (* var overwriting *)
let test_10 = test_typeofV_success [] (ValPair (True, Zero)) (VCross (Bool, Nat))
let test_11 =  test_typeofV_success [] (PMPair (ValPair (True, Zero), "x", "y", IfThEl (Var "x", Var "y", Zero))) Nat
let test_12 =  test_typeofV_success [] (Inl (Zero, Bool)) (Sum (Nat, Bool))
let test_13 =  test_typeofV_success [] (Thunk (Produce (Succ Zero))) (U (F Nat))

(* test cases for typeofV where the typechecker should fail *)
let testfail1 = test_typeofV_failure [] (Var "x")
let testfail2 = test_typeofV_failure [] (IsZero (True)) 
let testfail3 = test_typeofV_failure [] (IfThEl (True, False, Succ Zero))
let testfail4 = test_typeofV_failure [] (IfThEl (Zero, False, Succ Zero))
let testfail5 = test_typeofV_failure [] (IfThEl (True, False, Produce (Succ Zero)))
let testfail6 = test_typeofV_failure [] (Case (True, "x", Succ (Var "x"), "y", Zero))
let testfail7 = test_typeofV_failure [] (Case (Inl (True, Nat), "x", Var "x", "y", Zero))
let testfail8 = test_typeofV_failure [] (PMPair (True, "x", "y", Zero))
let testfail9 = test_typeofV_failure [] (Lam ("x", Nat, Produce (Succ (Var "x"))))


(* test cases for typeofC where the typechecker should succeed *)

let test2 =  test_typeofC_success [] (LetIn ("x", True, Produce (Var "x"))) (F Bool)

let test5 =  test_typeofC_success [] (App (True, Lam ("x", Bool, Produce(Var "x")))) (F Bool)

let test7 =  test_typeofC_success [] (Force (Thunk (Produce (Succ Zero)))) (F Nat)
let test8 =  test_typeofC_success [] (CompPair (Produce True, Force (Thunk (Produce (Succ Zero))))) (CCross (F Bool, F Nat))
let test9 =   test_typeofC_success [] (Bind (Produce Zero, "x", Produce (Var "x"))) (F Nat)


(* test cases for typeofC where the typechecker should fail *)

let test1_1 = test_typeofC_failure [] (Lam ("x", Nat, Force (Succ (Var "x"))))





(* terms with variables labeled using de bruijn indices (nameless representation)*)
type tm = 
| Var of int  
| Unit
| True 
| False
| Zero
| Succ of tm
| IsZero of tm
| IfThEl of tm * tm * tm (* if t1 then t2 else t3*)
| LetIn of tm * tm (* let x = t1 in t2 *)
| CompPair of tm * tm  (* (t1, t2) *)
| Fst of tm (* fst t *)
| Snd of tm (* snd t *)
| ValPair of tm * tm (* (v1, v2) *)
| PMPair of tm * tm (* pm t1 as (x, y). t2 *)
| Inl of tm * tpV (* inl t *)
| Inr of tm * tpV (* inr t *)
| Case of tm * tm * tm (* pm t as inl x -> t1 | inl r -> t2 *)
| Lam of tpV * tm                (* also called pop *)
| App of tm * tm                           (* also called push *)
| Bind of tm * tm    (* t1 to x. t2 *)
| Produce of tm (* produce t *)
| Force of tm (* force t *)
| Thunk of tm (* thunk t *)

type name = string
type ctx_debruijn = name list

(* convert from named representation to nameless representation *)
let rec debruijnify (context : ctx_debruijn) (named_term : named_tm) : tm =
  match named_term with
  | Var x ->  (
        match List.find_index (fun y -> x = y) context with
        | Some i  -> Var i
        | None -> failwith ("Variable not found in context lookup"))
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> Zero
  | Succ t -> Succ (debruijnify context t)
  | IsZero n -> IsZero (debruijnify context n)
  | IfThEl (t1, t2, t3) -> IfThEl (debruijnify context t1, debruijnify context t2, debruijnify context t3)
  | LetIn (x, t1, t2) -> LetIn (debruijnify context t1, debruijnify (x :: context) t2)
  | CompPair (t1, t2) -> CompPair (debruijnify context t1, debruijnify context t2)
  | Fst t -> Fst (debruijnify context t)
  | Snd t -> Snd (debruijnify context t)
  | ValPair (t1, t2) -> ValPair (debruijnify context t1, debruijnify context t2)
  | PMPair (t1, x, y, t2) -> PMPair (debruijnify context t1, debruijnify (y :: (x :: context)) t2) 
  | Inl (t,a) -> Inl (debruijnify context t, a)
  | Inr (t,a) -> Inr (debruijnify context t, a)
  | Case (t, x, t1, y, t2) -> Case (debruijnify context t, debruijnify (x :: context) t1, debruijnify (y :: context) t2) 
  | Lam (x, tp, t) -> Lam (tp, debruijnify (x :: context) t)              
  | App (t1, t2) -> App (debruijnify context t1, debruijnify context t2)
  | Bind (t1, x, t2) -> Bind (debruijnify context t1, debruijnify (x :: context) t2)  
  | Produce t -> Produce (debruijnify context t)
  | Force t -> Force (debruijnify context t)
  | Thunk t -> Thunk (debruijnify context t)



(*
   
TODO: test debruijinfy
let test_debruijnify () = 
PMPair (VarPair (Zero,Unit), "x","y", VarPair (Var "x",Var "y"))

*)

(* add more of these *)
let test_debruijnify () = 
 let test1 = debruijnify [] (PMPair (ValPair (Zero,Unit), "x","y", ValPair (Var "x",Var "y")))in
 let test2 = debruijnify [] (PMPair (ValPair (Thunk (Lam ("x", Nat, Produce (Var "x"))),Zero), "y","z", App(Var "z",Produce ( Var "y"))))in
 let test3 = debruijnify [] (PMPair (ValPair (Thunk (Lam ("x", Nat, Produce (Var "x"))),Zero), "y","z", App(Var "z", (Lam ("a", Nat, Produce (Var "a")))))) in
  test3
(* how do i make these test look useful i hate my way of doing this. *)


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
  | IsZero t -> IsZero (shift c d t)
  | IfThEl (t1, t2, t3) -> IfThEl (shift c d t1, shift c d t2, shift c d t3)
  | LetIn (t1, t2) -> LetIn (shift c d t1, shift (c + 1) d t2) 
  | CompPair (t1, t2) -> CompPair (shift c d t1, shift c d t2)
  | Fst t -> Fst (shift c d t)
  | Snd t -> Snd (shift c d t)
  | ValPair (t1, t2) -> ValPair (shift c d t1, shift c d t2)
  | PMPair (t1, t2) -> PMPair (shift c d t1, shift (c + 2) d t2)
  | Inl (t,a) -> Inl (shift c d t, a)
  | Inr (t,a) -> Inr (shift c d t, a)
  | Case (t, t1, t2) -> Case (shift c d t, shift (c + 1) d t1, shift (c + 1) d t2) (* pm t as inl x -> t1 | inl r -> t2 *)
  | Lam (tp, t) -> Lam (tp, shift (c + 1) d t)          
  | App (t1, t2) -> App (shift c d t1, shift c d t2)                     
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
  | IsZero t -> IsZero (subst s j t)
  | IfThEl (t1, t2, t3) -> IfThEl (subst s j t1, subst s j t2, subst s j t3)
  | LetIn (t1, t2) -> LetIn (subst s j t1, subst (shift 0 1 s) (j + 1) t2)
  | CompPair (t1, t2) -> CompPair (subst s j t1, subst s j t2)
  | Fst t -> Fst (subst s j t)
  | Snd t -> Snd (subst s j t)
  | ValPair (t1, t2) -> ValPair (subst s j t1, subst s j t2)
  | PMPair (t1, t2) -> PMPair (subst s j t1, subst (shift 0 2 s) (j + 2) t2) (* unsure about this case*)
  | Inl (t,a) -> Inl (subst s j t, a)
  | Inr (t,a) -> Inr (subst s j t, a)
  | Case (t, t1, t2) -> Case (subst s j t, subst (shift 0 1 s) (j + 1) t1, subst (shift 0 1 s) (j + 1) t2) (* pm t as inl x -> t1 | inl r -> t2 *)
  | Lam (tp, t) -> Lam (tp, subst (shift 0 1 s) (j + 1) t)           
  | App (t1, t2) -> App (subst s j t1, subst s j t2)                        
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
| IsZero t -> IsZero (eval t)
| IfThEl (t1, t2, t3) -> IfThEl (eval t1, eval t2, eval t3)
| LetIn (v, t2) -> eval (subst v 0 t2)
| CompPair (t1, t2) -> CompPair (t1, t2) (* is this right ??  yeah i think its a value*)
| Fst t -> (match eval t with
  | CompPair (n1, n2) -> eval n1
  | _ -> raise Crash)
| Snd t -> (match eval t with
  | CompPair (n1, n2) -> eval n2
  | _ -> raise Crash)
| ValPair (t1, t2) -> ValPair (t1, t2)
| PMPair (v, t2) -> (match v with
    | ValPair (v1, v2) -> let t2' = subst (shift 0 1 v1) 0 t2 in
    subst v2 0 t2' (* make sure this is the right order of shifts *)
    | _ -> raise Crash)
| Inl (t,a) -> Inl (eval t, a) (* is this right? is this guaranteed to be a value? hehhehehe my bad i had inl/inr all wrong. it is fixed now, also it is eager style*)
| Inr (t,a) -> Inr (eval t, a)
| Case (t, t1, t2) -> (match t with
  | Inl (x,a) -> eval (subst x 0 t1)
  | Inr (y,a) -> eval (subst y 0 t2)
  | _ -> raise Crash
)
| Lam (tp, t) -> Lam (tp, t)         
| App (v, t2) -> (match eval t2 with
  | Lam (tp, t) -> eval (subst v 0 t) (* how is it guaranteed that v is a value? i guess because it wouldn't have typechecked otherwise? yes i think so. App takes tpV * tpC *)
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
   prove translation on paper
*)

type tpN = 
| ArrowN of tpN * tpN
| CrossN of tpN * tpN
| SumN of  tpN * tpN
| UnitN
| BoolN

(* uses debruijn *)
type ntm = 
| UnitN
| TrueN
| FalseN
| VarN of int
| LamN of tpN * ntm
| AppN of ntm * ntm
| PairN of ntm * ntm
| FstN of ntm
| SndN of ntm
| CaseN of ntm * string * ntm * string * ntm
| InlN of ntm * tpN
| InrN of ntm * tpN
| IfThEl of ntm * ntm * ntm 
| LetInN of string * ntm * ntm

(* following p 59*)
(* translation on types *)
let rec trans_tp (tp:tpN) : tpC = match tp with 
| ArrowN (t1,t2) -> Arrow (U( trans_tp t1), trans_tp t2)
| CrossN (t1,t2) -> CCross (trans_tp t1, trans_tp t2)
| SumN (t1,t2) -> F (Sum (U (trans_tp t1),U (trans_tp t2)))
| UnitN -> F (Unit)
| BoolN -> F (Bool)


type ctxN = (string * tpN) list
let rec trans_ctx (ctx : ctxN): ctx = match ctx with
| [] -> []
| (x, tp)::xs -> (x, U (trans_tp tp) ) :: trans_ctx ctx 
                  (* ^ only value types can be in context so we thunk it. is this ok? *)

(* translation on terms *)
let rec trans (t : ntm) : tm = 
  (*parse t for all the variable names*)
  match t with 
| UnitN -> Produce (Unit)
| TrueN -> Produce (True)
| FalseN -> Produce (True)
| VarN i -> Force (Var i)
| LamN (tp, t) -> Lam ( U (trans_tp tp), trans t )
| AppN (t1,t2) -> App (Thunk (trans t1), trans t2)
| PairN (t1,t2) -> CompPair (trans t1, trans t2)
| FstN t -> Fst (trans t) 
| SndN t -> Snd (trans t)                 (* make a fresh variable somehow... *)
| CaseN (t, x, t1, y, t2) -> Bind (trans t , Case (Var 0 ,  (shift 0 1 (trans t1)) , (shift 0 1 (trans t2)) )) 
| InlN (t, a) -> Produce (Inl (Thunk (trans t), U (trans_tp a)))
| InrN (t, a) -> Produce (Inr (Thunk (trans t ), U (trans_tp a)))
| IfThEl (t1,t2,t3) -> Bind ( shift 0 1 (trans t1), IfThEl (Var 0,  (shift 0 1 (trans t2)),  (shift 0 1 (trans t3)) ))
| LetInN (x, t1, t2) -> LetIn (Thunk (trans t1), trans t2)


(* could we fix the naming issue by using debruijn indicies and shifting? emily help!!*)