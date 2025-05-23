open List

(* define the types (computations and values) and terms) *)
type tpV = 
| Unit
| Bool
| Nat
| U of tpC    (* U B *)
| VCross of tpV * tpV  (* A x A' *)
| Sum of tpV * tpV (* A + A' *) (* value type, if you want to use it with computations: produce (inl (thunk t, U tpC)) if you want sum types for computations *)
and 
tpC = 
| F of tpV     (* F A *)
| Arrow of tpV * tpC (* A -> B *)  (* thunk the argument to pass a term of computation type to a function *)
| CCross of tpC * tpC   (* B x B'*)

(* terms with variables named using strings *)
type named_tm = 
| Var of string  
| Unit
| True 
| False
| Zero
| Succ of named_tm
| Pred of named_tm
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
| Bind of named_tm * string * named_tm    (* t1 to x. t2. sequencing computations - t1 must be a producer type *)
| Produce of named_tm (* produce t *)
| Force of named_tm (* force t *)
| Thunk of named_tm (* thunk t *)
| Fix of string * tpC * named_tm


type ctx = (string * tpV) list

exception TypeError of string 

(*there is no variable shadowing. new declarations with the same name just overwrite*)

(* our type checker, split in to two mutually recursive functions. one for values and one for computations. *)
let rec typeofV (ctx:ctx) (t : named_tm) : tpV = match t with
  | Var x -> (match find_opt (fun y -> fst y = x ) ctx with 
    | None -> raise (TypeError ("Variable " ^ x ^ " is free"))
    | Some x ->  snd x )
  | Unit -> Unit
  | True -> Bool
  | False -> Bool
  | Zero -> Nat
  | Succ x -> typeofV ctx x
  | Pred x -> typeofV ctx x
  | IsZero n -> (match typeofV ctx n with 
    | Nat -> Bool
    | _ -> raise (TypeError ("IsZero must be applied to something of type Nat")))
  | Thunk t -> U (typeofC ctx t)
  | Inl (t, a) -> Sum (typeofV ctx t, a) 
  | Inr (t, a) -> Sum (a, typeofV ctx t) 
  | ValPair (t1, t2) -> (let (x,y) = (typeofV ctx t1, typeofV ctx t2) in VCross (x,y))  
  | _ ->  raise (TypeError ("Supposed to be a value, but it isn't " ^ (String.concat "" (List.map (fun x -> fst x ^ ", ") ctx))))
and typeofC (ctx : ctx) (t : named_tm) : tpC = match t with
  | Lam (x,a,t) -> Arrow( a, typeofC ((x,a)::(List.filter (fun z -> fst z <> x ) ctx)) t)            
  | LetIn (x, v, c) -> typeofC ((x, typeofV ctx v) ::  ctx) c 
  | Produce t -> F (typeofV ctx t)
  | Force t -> (match typeofV ctx t with 
    | U t' -> t'
    | _ -> raise (TypeError ("Must force a Thunk")))
  | IfThEl (t1, t2, t3) -> (match (typeofV ctx t1, typeofC ctx t2,  typeofC ctx t3) with 
    | (Bool, x, y) -> if x = y then x else raise (TypeError ("Types of branches of if-then-else don't match")) 
    | _ -> raise (TypeError ("Either the scrutinee of if-then-else isn't a Bool, or the branches aren't computation types")))
  | CompPair (t1, t2) -> (let (x,y) = typeofC ctx t1, typeofC ctx t2 in CCross (x,y)) 
  | PMPair (t1, x, y, t2) -> (match typeofV ctx t1 with 
    | VCross (v1,v2) -> typeofC ([(x, v1);(y, v2)]  @ ctx) t2                             
    | _ -> raise (TypeError ("Using PMPair on non-VCross type"))) 
  | Fst t -> (match typeofC ctx t with 
      | CCross (x,_) -> x
      | _ -> raise (TypeError "Fst needs to be applied to a computation pair"))
  | Snd t -> (match typeofC ctx t with 
      | CCross (_,y) -> y
      | _ -> raise (TypeError "Snd needs to be applied to a computation pair"))
  | Case (t,x,t1,y,t2) -> (match typeofV ctx t with        
      | Sum (a1, a2) -> 
          let (b1,b2) = typeofC ((x, a1)::(List.filter (fun z -> fst z <> x ) ctx)) t1, typeofC ((y, a2)::(List.filter (fun z -> fst z <> y ) ctx)) t2 in 
          if b1 = b2 then b1 else raise (TypeError "Types of branches of case don't match")
      | _ -> raise (TypeError "Case trying to match on something other than a Sum type")) 
  | App (v,t2) -> (match typeofC ctx t2 with 
      | Arrow (tv,tc) -> if tv = typeofV ctx v then tc else raise (TypeError "Argument passed doesn't match function's input type")
      | _ -> raise (TypeError "Second arg of application needs to be Arrow type"))
  | Bind (t1, x, t2) -> (match typeofC ctx t1 with
      | F a -> typeofC ((x, a) :: (List.filter (fun z -> fst z <> x ) ctx)) t2 
      | _ -> raise (TypeError "Can only bind something of the form F A"))
  | Fix (x,a,t) -> typeofC ((x,U a)::(List.filter (fun z -> fst z <> x ) ctx)) t
  | _ -> raise (TypeError ("Supposed to be a computation type, but it's not " ^ (String.concat "" (List.map (fun x -> fst x ^ ", ") ctx))))



let test_typeofC_success (context :ctx) (tm: named_tm) (ty : tpC) = 
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
let test_1 = test_typeofV_success [("x", Nat)] (Succ (Var "x")) Nat
let test_2 = test_typeofV_success [("x", Nat)] (IsZero (Var "x")) Bool
let test_3 = test_typeofC_success [("x", Bool)] (IfThEl (Var "x", Produce(Succ Zero),  Produce(Succ (Succ Zero)))) (F Nat)
let test_4 = test_typeofV_success [] (Thunk (Lam ("x", Nat, Produce (Succ (Var "x"))))) (U (Arrow (Nat, F Nat)))
let test_5 = test_typeofV_success [] (Inl (True, Nat)) (Sum (Bool, Nat))
let test_7 = test_typeofV_success [] (ValPair (True, False)) (VCross (Bool, Bool))
let test_8 = test_typeofV_success [] (ValPair (True, Zero)) (VCross (Bool, Nat))
let test_9 =  test_typeofV_success [] (Inl (Zero, Bool)) (Sum (Nat, Bool))
let test_10 =  test_typeofV_success [] (Thunk (Produce (Succ Zero))) (U (F Nat))

(* test cases for typeofV where the typechecker should fail *)
let testfail1 = test_typeofV_failure [] (Var "x")
let testfail2 = test_typeofV_failure [] (IsZero (True)) 
let testfail3 = test_typeofC_failure [] (IfThEl (True, Produce (False), Produce (Succ Zero)))
let testfail4 = test_typeofC_failure [] (IfThEl (Zero, Produce (False), Produce (Succ Zero)))
let testfail5 = test_typeofC_failure [] (IfThEl (True, Produce (False), Succ Zero))
let testfail8 = test_typeofV_failure [] (Lam ("x", Nat, Produce (Succ (Var "x"))))


(* test cases for typeofC where the typechecker should succeed *)
let test1 = test_typeofC_success [] (PMPair (ValPair (True, Zero), "x", "y", IfThEl (Var "x",Produce(Var "y"),Produce(Zero)))) (F Nat)
let test2 = test_typeofC_success [("x", Nat)] (PMPair (ValPair (True, False), "x", "y", Produce(Var "x"))) (F Bool) (* var overwriting *)
let test3 = test_typeofC_success [] (PMPair (ValPair (True, False), "x", "y", Produce (Var "x"))) (F Bool)
let test4 = test_typeofC_success [] (Lam ("x", Nat, Produce (Succ (Var "x")))) (Arrow (Nat, F Nat))
let test5 =  test_typeofC_success [] (LetIn ("x", True, Produce (Var "x"))) (F Bool)
let test6 = test_typeofC_success [] (Produce (Zero)) (F Nat)
let test7 = test_typeofC_success [] (Force (Thunk (App (Zero, Lam ("x", Nat, Produce (Succ (Var "x"))))))) (F Nat)
let test8 =  test_typeofC_success [] (Force (Thunk (Produce (Succ Zero)))) (F Nat)
let test9 =  test_typeofC_success [] (CompPair (Produce True, Force (Thunk (Produce (Succ Zero))))) (CCross (F Bool, F Nat))
let test10 = test_typeofC_success [] (Fst (CompPair (Lam ("x", Nat, Produce (Succ (Var "x"))), Lam ("x", Nat, Produce (Succ (Var "x")))))) (Arrow (Nat, F Nat))
let test11 =  test_typeofC_success [] (App (True, Lam ("x", Bool, Produce(Var "x")))) (F Bool)
let test12 = test_typeofC_success [] (Bind (Produce Zero, "x", Produce (Var "x"))) (F Nat)
let test13 = test_typeofC_success [] (Case (Inl (True, Nat), "x", Produce (Var "x"), "y", Produce(False))) (F Bool)
let test14 = test_typeofC_success [] (Fix ("x", F Bool, Fst (CompPair( Produce True , Produce (Var "x"))))) (F Bool)

(* test cases for typeofC where the typechecker should fail *)
let testfail_1 = test_typeofC_failure [] (Lam ("x", Nat, Force (Succ (Var "x"))))
let testfail_2 = test_typeofC_failure [] (Fst (ValPair (True, False)))
let testfail_3 = test_typeofC_failure [] (App (True, (Lam ("x", Nat, Produce (Succ (Var "x"))))))
let testfail_4 = test_typeofC_failure [] (App (True, Produce False))
let testfail_5 = test_typeofC_failure [] (Bind (Lam ("y", Nat, Produce (Var "y")), "x", Produce (Var "x")))
let testfail_6 = test_typeofC_failure [] (Thunk (Lam ("x", Nat, Produce (Var "x"))))
let testfail_7 = test_typeofC_failure [] (PMPair (True, "x", "y", Produce Zero))
let testfail_8 = test_typeofC_failure [] (Case (True, "x", Succ (Var "x"), "y", Zero))
let testfail_9 = test_typeofC_failure [] (Case (Inl (True, Nat), "x", Produce (Var "x"), "y", Produce(Zero)))



(* terms with variables labeled using de bruijn indices (nameless representation)*)
type tm = 
| Var of int  
| Unit
| True 
| False
| Zero
| Succ of tm
| Pred of tm
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
| App of tm * tm                 (* also called push *)
| Bind of tm * tm    (* t1 to x. t2 *)
| Produce of tm (* produce t *)
| Force of tm (* force t *)
| Thunk of tm (* thunk t *)
| Fix of tpC * tm (* fix x:B. t *)

type name = string
type ctx_debruijn = name list

(* convert from named representation to nameless representation *)
let rec debruijnify (context : ctx_debruijn) (named_term : named_tm) : tm =
  match named_term with
  | Var x ->  (
        match List.find_index (fun y -> x = y) context with
        | Some i  -> Var i
        | None -> failwith ("Variable " ^ x ^ " not found in context lookup"))
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> Zero
  | Succ t -> Succ (debruijnify context t)
  | Pred t -> Pred  (debruijnify context t)
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
  | Fix (x, tp, t) ->  Fix (tp, debruijnify (x :: context) t) 


let test_debruijnify (ctx : ctx_debruijn) (named_term : named_tm) (nameless_term : tm) : bool =
  debruijnify ctx named_term = nameless_term

(* debruijnify tests *)
let test1_db = test_debruijnify ["x"] (Var "x") (Var 0)
let test2_db = test_debruijnify ["y"; "x"] (Succ (Var "x")) (Succ (Var 1))
let test3_db = test_debruijnify [] (LetIn ("x", True, Var "x")) (LetIn (True, Var 0))
let test4_db = test_debruijnify [] (PMPair (ValPair (Zero, Unit), "x","y", Produce (ValPair (Var "x",Var "y")))) (PMPair (ValPair (Zero, Unit), Produce (ValPair (Var 1, Var 0))))
let test5_db = test_debruijnify [] (PMPair (ValPair (Thunk (Lam ("x", Nat, Produce (Var "x"))),Zero), "y","z", App(Var "z",Produce (Var "y")))) (PMPair (ValPair (Thunk (Lam (Nat, Produce (Var 0))),Zero), App (Var 0,Produce ( Var 1))))
let test6_db = test_debruijnify [] (PMPair (ValPair (Thunk (Lam ("x", Nat, Produce (Var "x"))),Zero), "y","z", App(Var "z", (Lam ("a", Nat, Produce (Var "a")))))) (PMPair (ValPair (Thunk (Lam (Nat, Produce (Var 0))),Zero), App(Var 0, (Lam (Nat, Produce (Var 0))))))
let test7_db = test_debruijnify [] (Case (Inl (True, Bool), "x", Var "x", "y", Var "y")) (Case (Inl (True, Bool), Var 0, Var 0))
let test8_db = test_debruijnify ["y"; "z"] (Lam ("x", Nat, Produce (Succ (Var "x")))) (Lam (Nat, Produce (Succ (Var 0))))
let test9_db = test_debruijnify [] (Bind (Produce Zero, "x", Produce (Var "x"))) (Bind (Produce Zero, Produce (Var 0)))

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
  | Pred t -> Pred (shift c d t)
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
  | Fix (tp, t) -> Fix (tp, shift (c + 1) d t)

let test_shift (input : tm) (c : int) (d : int) (res : tm) : bool = 
  shift c d input = res

let shift_test_1 = test_shift (Var 0) 0 1 (Var 1)
let shift_test_2 = test_shift (Succ (Var 0)) 0 1 (Succ (Var 1))
let shift_test_3 = test_shift (LetIn (Zero, Produce (ValPair (Var 0, Var 1)))) 0 1 (LetIn (Zero, Produce (ValPair (Var 0, Var 2))))
let shift_test_4 = test_shift (PMPair (ValPair (True, False), Produce (ValPair (Var 2, ValPair (Var 0, Var 1))))) 0 1 (PMPair (ValPair (True, False), Produce (ValPair (Var 3, ValPair (Var 0, Var 1)))))
let shift_test_5 = test_shift (Case (Inl (True, Nat), Var 0, Var 1)) 0 1 (Case (Inl (True, Nat), Var 0, Var 2))
let shift_test_6 = test_shift (Case (Inl (True, Bool), Var 0, Var 0)) 0 1 (Case (Inl (True, Bool), Var 0, Var 0))
let shift_test_7 = test_shift (Lam (Nat, Succ (Var 0))) 0 1 (Lam (Nat, Succ (Var 0)))
let shift_test_8 = test_shift (Bind (Produce Zero, Produce (Var 0))) 0 1 (Bind (Produce Zero, Produce (Var 0)))

(* substitute a term s for the variable j in t *)
let rec subst (s : tm) (j : int) (t : tm) : tm = match t with
  | Var x -> if x = j then s else Var x
  | Unit -> Unit
  | True -> True
  | False -> False
  | Zero -> Zero
  | Succ t -> Succ (subst s j t)
  | Pred t -> Pred (subst s j t)
  | IsZero t -> IsZero (subst s j t)
  | IfThEl (t1, t2, t3) -> IfThEl (subst s j t1, subst s j t2, subst s j t3)
  | LetIn (t1, t2) -> LetIn (subst s j t1, subst (shift 0 1 s) (j + 1) t2)
  | CompPair (t1, t2) -> CompPair (subst s j t1, subst s j t2)
  | Fst t -> Fst (subst s j t)
  | Snd t -> Snd (subst s j t)
  | ValPair (t1, t2) -> ValPair (subst s j t1, subst s j t2)
  | PMPair (t1, t2) -> PMPair (subst s j t1, subst (shift 0 2 s) (j + 2) t2) 
  | Inl (t,a) -> Inl (subst s j t, a)
  | Inr (t,a) -> Inr (subst s j t, a)
  | Case (t, t1, t2) -> Case (subst s j t, subst (shift 0 1 s) (j + 1) t1, subst (shift 0 1 s) (j + 1) t2) (* pm t as inl x -> t1 | inl r -> t2 *)
  | Lam (tp, t) -> Lam (tp, subst (shift 0 1 s) (j + 1) t)           
  | App (t1, t2) -> App (subst s j t1, subst s j t2)                        
  | Bind (t1, t2) -> Bind (subst s j t1, subst (shift 0 1 s) (j + 1) t2)   (* t1 to x. t2 *)
  | Produce t -> Produce (subst s j t)
  | Force t -> Force (subst s j t)
  | Thunk t -> Thunk (subst s j t)
  | Fix (tp, t) -> Fix (tp, subst (shift 0 1 s) (j + 1) t)     

let subst_test1 = subst (Var 1) 0 (Var 0) = Var 1
let subst_test2 = subst (Var 1) 0 (Succ (Var 0)) = Succ (Var 1)
let subst_test3 = subst (Var 2) 0 (IfThEl (Var 0, Var 1, Var 0)) = IfThEl (Var 2, Var 1, Var 2)
let subst_test4 = subst (Var 2) 0 (Succ (Succ (Var 0))) = Succ (Succ (Var 2))
let subst_test5 = subst (Var 2) 0 (LetIn (Var 0, Var 0)) = LetIn (Var 2, Var 0)
let subst_test6 = subst (Var 2) 0 (PMPair (Var 0, Var 1)) = PMPair (Var 2, Var 1)
let subst_test7 = subst (Var 2) 0 (Case (Var 0, Var 1, Var 2)) = Case (Var 2, Var 3, Var 2)
let subst_test8 = subst (Var 1) 0 (Var 2) = Var 2
let subst_test9 = subst (Var 2) 0 (Lam (Nat, Var 0)) = Lam (Nat, Var 0)
let subst_test10 = subst (Var 2) 0 (Force (Var 0)) = Force (Var 2)

(* big-step evaluator *)
let rec eval (t : tm) = match t with
| Var x -> raise Crash
| Unit -> Unit
| True -> True
| False -> False
| Zero -> Zero
| Succ t -> Succ (eval t)
| Pred t -> (match eval t with
  | Zero -> Zero
  | Succ x -> x
  | _ -> raise Crash)
| IsZero t -> (match eval t with 
  | Zero -> True 
  | Succ n -> False 
  | _ -> raise Crash )
| IfThEl (t1, t2, t3) -> (match eval t1 with 
  | True -> eval t2
  | False -> eval t3
  | _ -> raise Crash )
| LetIn (v, t2) -> let v' = shift 0 1 v in eval (shift 0 (-1) (subst v' 0 t2)) 
| CompPair (t1, t2) -> CompPair (t1, t2) 
| Fst t -> (match eval t with
  | CompPair (n1, n2) -> eval n1
  | _ -> raise Crash)
| Snd t -> (match eval t with
  | CompPair (n1, n2) -> eval n2
  | _ -> raise Crash)
| ValPair (t1, t2) -> ValPair (eval t1, eval t2)
| PMPair (v, t2) -> (match eval v with 
    | ValPair (v1, v2) -> let t2' = let v2' = shift 0 1 v2 in (shift 0 (-1) (subst v2' 0 t2)) in
    let v1' = shift 0 1 v1 in eval (shift 0 (-1) (subst v1' 0 t2')) 
    | _ -> raise Crash)
| Inl (t,a) -> Inl (eval t, a)
| Inr (t,a) -> Inr (eval t, a)
| Case (t, t1, t2) -> (match eval t with 
  | Inl (x,a) -> let x' = shift 0 1 x in eval (shift 0 (-1) (subst x' 0 t1))
  | Inr (y,a) -> let y' = shift 0 1 y in eval (shift 0 (-1) (subst y' 0 t2))
  | _ -> raise Crash
)
| Lam (tp, t) -> Lam (tp, t)         
| App (v, t2) -> (match eval t2 with
  | Fix (tp, t) -> let arg = shift 0 1 v in eval (shift 0 (-1) (subst arg 0 t))
  | Lam (tp, t) -> let arg = shift 0 1 v in eval (shift 0 (-1) (subst arg 0 t)) 
  | _ -> raise Crash
)                    (* also called push *)
| Bind (t1, t2) -> (match eval t1 with
  | Produce v -> eval (subst v 0 t2)
  | _ -> raise Crash
)
| Produce v -> Produce v
| Force t -> (match eval t with
  | Thunk t1 -> eval t1 
  | _ -> raise Crash)
| Thunk t -> Thunk t
| Fix (tp, t) -> eval (subst (Thunk (Fix (tp, t))) 0 t) 


let test_eval_success t goal : bool = 
  try eval t = goal  with
| Crash -> false

let test_eval_failure t : bool = 
  try eval t; false with 
| Crash -> true

let testeval1 = test_eval_success (Succ (Succ Zero)) (Succ (Succ Zero)) 
let testeval2 = test_eval_success (IsZero (Succ Zero)) False
let testeval3 = test_eval_success (IfThEl (False, Produce( Succ Zero), Produce(Zero))) (Produce(Zero))
let testeval4 = test_eval_success (App (Succ Zero, Lam ( Nat, Succ (Var 0)))) (Succ (Succ Zero)) 
let testeval5 = test_eval_success (LetIn ( Succ Zero, Succ (Var 0))) (Succ (Succ Zero)) 
let testeval6 = test_eval_success (Case (Inr (Zero, Nat),Produce (Succ (Var 0)), Produce (Var 0))) (Produce Zero)
let testeval7 = test_eval_success (Case (Inl (True, Bool), Produce(Var 0), Produce(Zero))) (Produce True)
let testeval8 = test_eval_success (Fst (CompPair (Succ Zero, False))) (Succ Zero)
let testeval9 = test_eval_success (Force (Thunk (IsZero Zero))) True

(* add test cases for fix *)

let testeval10 = test_eval_success (LetIn ( Succ Zero, LetIn ( Succ (Var 0), Var 0))) (Succ (Succ Zero)) 
let testeval11 = test_eval_failure (IsZero True)
let testeval12 = test_eval_failure (IfThEl (Zero, Produce(Zero), Produce(False)))
let testeval13 = test_eval_failure (Var 0)
let testeval14 = test_eval_success (App (Zero, Lam ( Nat, Succ (Var 0)))) (Succ Zero)
let testeval15 = test_eval_success (Force (Thunk (Succ Zero))) (Succ Zero)
let testeval16 = test_eval_success (PMPair (ValPair (True, False), Var 0)) False 
let testeval17 = test_eval_success (Case (Inl (True, Bool), Var 0, Var 0)) True
let testeval18 = test_eval_success (App (Zero, Lam ( Nat, Succ (Var 0)))) (Succ Zero)
let testeval19 = test_eval_failure (Force True)
let testeval20 = test_eval_failure (Case (Zero, Var 0, Zero))
let testeval21 = test_eval_success (App ( ValPair (True, False), Lam ( VCross (Bool, Bool), PMPair (Var 0, Var 0)))) False 
(* add test cases for fix *)



(* Here is where we will typecheck and run programs we write in CBPV *)

(* The programmer must specify for each function in a program if it is a computation type or a value type. 
   This makes things easier in typechecking and running because otherwise we need to recursively check if each function 
   is a comp or val type to make a choice based on this, but force thunk sequences make this more difficult than just 
   checking the outermost constructor so we've decided to not bother with it.  *)
type either = C | V 

(* name is the name of the function
   body is the body of the function
   whichtyp tells us if the body is a computation or a value type*)
type decl =
  {
    name: string;
    body: named_tm;
    whichtyp: either;
  }

type program = decl list

(* Typechecks a whole program 
   Returns unit upon success. 
   Otherwise the type inference above will throw some (helpful?) error *)
let check_program p : unit =
  let process_decl ctx { name; body; whichtyp } = 
  (match whichtyp with 
    | V ->  let x = typeofV ctx body in (name, x) :: ctx  
    | C ->  let x = typeofC ctx body in (name, U x) :: ctx )
  in
  ignore (List.fold_left process_decl [] p)


(* Runs programs that has functions that can refer to each other,
   outputs the result of the last function defined as a computation type.*)
let run_program p : tm  = 
  check_program p;
  let rec build p  = 
  match p with 
  | [] -> failwith "empty program"
  | [{ name; body; whichtyp }] -> (match whichtyp with 
    | C -> body
    | V -> Produce body)
  | { name; body; whichtyp } :: xs -> match whichtyp with 
    | C -> LetIn( name, Thunk body, build xs ) 
    | V -> LetIn( name, body, build xs ) 
  in
  eval (debruijnify [] (build p) )

(* Version where functions in a program cant see each other, 
   but each function's output is returned in a list according to its postition in the file *)
(*
let run_program p : tm list = 
  check_program p;
  let rec run p result = 
  match p with 
  | [] -> result
  | { name; body; whichtyp } :: xs -> 
    run xs (result @ [eval (debruijnify [] body)]) 
  in
  run p [] 
*)



(* Here are some example programs written in CBPV. The most interesting is factorial4 *)
let const1 =  [
  {name = "one";
  body = Succ Zero;
  whichtyp = V; 
  };
]

let zeropluszero =  [
  {name = "addval";
  body =  Fix("addval", Arrow (VCross(Nat,Nat), F Nat),
    Lam("xy1", VCross(Nat,Nat), 
    PMPair (Var "xy1", "x1", "y1", 
      IfThEl (IsZero (Var "x1"), Produce( Var "y1"), App ( ValPair(Pred (Var "x1"), Succ (Var "y1") ), Force( Var "addval" ))))));
  whichtyp = C; 
  };

  {name = "0plus0"; 
  body = App (ValPair(Zero, Zero), Force ( Var "addval"));
  whichtyp =  C;
  };
]  

let compzeropluszero =  [
{
  name = "addcomp";
  body =  Fix("addcomp", Arrow (U (CCross(F Nat,F Nat)), F Nat), 
  Lam("xy", U (CCross( F Nat, F Nat)), 
  Bind (Fst (Force (Var "xy")), "x" ,
  Bind (Snd (Force (Var "xy")), "y",
  IfThEl (IsZero (Var "x"), 
  Produce (Var "y"), 
  App (Thunk (CompPair(Produce (Pred (Var "x")), Produce (Succ (Var "y")))), Force (Var "addcomp" )))))));
 whichtyp = C;
};

{
  name = "0plus0";
  body = App (Thunk (CompPair( Produce Zero, Produce Zero)), Force ( Var "addcomp"));
  whichtyp =  C;
};
] 

let val3times2 = [
{name = "addcomp";
body =  Fix("addcomp", Arrow (U (CCross(F Nat,F Nat)), F Nat), 
  Lam("xy", U (CCross( F Nat, F Nat)), 
  Bind (Fst (Force (Var "xy")), "x" ,
  Bind (Snd (Force (Var "xy")), "y",
  IfThEl (IsZero (Var "x"), 
  Produce (Var "y"), 
  App (Thunk (CompPair(Produce (Pred (Var "x")), Produce (Succ (Var "y")))), Force (Var "addcomp" )))))));
whichtyp = C;
};

{name = "timesval"; 
body =  Fix ("timesval", Arrow (VCross(Nat,Nat), F Nat),
  Lam("ab1", VCross(Nat,Nat), 
  PMPair (Var "ab1", "a1", "b1", 
  IfThEl (IsZero (Var "a1"), 
    Produce Zero, 
    App ( Thunk (CompPair( Produce(Var "b1"), App (ValPair(Pred (Var "a1"), Var "b1"),Force (Var "timesval")))), Force (Var "addcomp"))))));
whichtyp = C;
};

{name = "val3times2";
body = App (ValPair( Succ(Succ(Succ Zero)), Succ(Succ Zero)), Force ( Var "timesval"));
whichtyp =  C;
};
]

let comp3times2 = [
  {name = "addcomp";
  body =  Fix("addcomp", Arrow (U (CCross(F Nat,F Nat)), F Nat), 
    Lam("xy", U (CCross( F Nat, F Nat)), 
    Bind (Fst (Force (Var "xy")), "x" ,
    Bind (Snd (Force (Var "xy")), "y",
    IfThEl (IsZero (Var "x"), 
    Produce (Var "y"), 
    App (Thunk (CompPair(Produce (Pred (Var "x")), Produce (Succ (Var "y")))), Force (Var "addcomp" )))))));
  whichtyp = C;
  };
  
  {name = "timescomp"; 
  body =  Fix ("timescomp", Arrow (U (CCross(F Nat,F Nat)), F Nat),
    Lam("ab",U (CCross( F Nat,F Nat)), 
    Bind (Fst (Force (Var "ab")), "a" ,
    Bind (Snd (Force (Var "ab")), "b",
    IfThEl (IsZero (Var "a"), 
      Produce Zero, 
      App ( Thunk (CompPair (Produce (Var "b"), App (Thunk (CompPair( Produce (Pred (Var "a")), Produce (Var "b"))), Force (Var "timescomp")))), Force (Var "addcomp")))))));
  whichtyp = C  
  };
  
  {
    name = "comp3times2";
    body = App (Thunk (CompPair( Produce (Succ( Succ (Succ Zero))), Produce ( Succ (Succ Zero)))), Force ( Var "timescomp"));
    whichtyp =  C;
  };
]


let factorial4 = [
{name = "addcomp";
body =  Fix("addcomp", Arrow (U (CCross(F Nat,F Nat)), F Nat), 
  Lam("xy", U (CCross( F Nat, F Nat)), 
  Bind (Fst (Force (Var "xy")), "x" ,
  Bind (Snd (Force (Var "xy")), "y",
  IfThEl (IsZero (Var "x"), 
  Produce (Var "y"), 
  App (Thunk (CompPair(Produce (Pred (Var "x")), Produce (Succ (Var "y")))), Force (Var "addcomp" )))))));
whichtyp = C;
};

{name = "timescomp";
body =  Fix ("timescomp", Arrow (U (CCross(F Nat,F Nat)), F Nat),
  Lam("ab",U (CCross( F Nat,F Nat)), 
  Bind (Fst (Force (Var "ab")), "a" ,
  Bind (Snd (Force (Var "ab")), "b",
  IfThEl (IsZero (Var "a"), 
    Produce Zero, 
    App ( Thunk (CompPair (Produce (Var "b"), App (Thunk (CompPair( Produce (Pred (Var "a")), Produce (Var "b"))), Force (Var "timescomp")))), Force (Var "addcomp")))))));
whichtyp = C  
};

{name = "factorial";
body = Fix ("factorial", Arrow (Nat, F Nat),
  Lam ("n", Nat, 
    IfThEl( IsZero (Var "n"), Produce (Succ Zero), App ( Thunk (CompPair( Produce (Var "n") , App( Pred (Var "n") ,Force (Var "factorial")))), Force (Var "timescomp")))));
whichtyp = C ;
};

{name = "fact4";
body = (App (Succ (Succ (Succ( Succ Zero))), Force (Var "factorial")));
whichtyp = C;
}
]

(* loops forever *)
let diverge = [{
  name = "diverge"; 
  body = Fix ("diverge", F Unit , Force (Var "diverge"));
  whichtyp = C;
  }]




(* Transpiler from CBN to CBPV *)

type tpN = 
| ArrowN of tpN * tpN
| CrossN of tpN * tpN
| SumN of  tpN * tpN
| UnitN
| BoolN

(* uses debruijn indices to avoid dealing with the need for fresh variable names *)
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
| FixN of tpN * ntm

(* following Levy p59*)
(* translation on types *)
let rec trans_tp (tp:tpN) : tpC = match tp with 
| ArrowN (t1,t2) -> Arrow (U( trans_tp t1), trans_tp t2)
| CrossN (t1,t2) -> CCross (trans_tp t1, trans_tp t2)
| SumN (t1,t2) -> F (Sum (U (trans_tp t1),U (trans_tp t2)))
| UnitN -> F (Unit)
| BoolN -> F (Bool)

(* translation on contexts *)
type ctxN = (string * tpN) list
let rec trans_ctx (ctx : ctxN): ctx = match ctx with
| [] -> []
| (x, tp)::xs -> (x, U (trans_tp tp) ) :: trans_ctx ctx 
                  (* ^ only value types can be in context so we thunk it. Levy p.56 *)

(* translation on terms *)
let rec trans (t : ntm) : tm = 
  match t with 
| UnitN -> Produce (Unit)
| TrueN -> Produce (True)
| FalseN -> Produce (True)
| VarN i -> Force (Var i)
| LamN (tp, t) -> Lam (U (trans_tp tp), trans t ) 
| AppN (t1,t2) -> App (Thunk (trans t1), trans t2)
| PairN (t1,t2) -> CompPair (trans t1, trans t2)
| FstN t -> Fst (trans t) 
| SndN t -> Snd (trans t)                
| CaseN (t, x, t1, y, t2) -> Bind (trans t , Case (Var 0 ,  (shift 0 1 (trans t1)) , (shift 0 1 (trans t2)) )) 
| InlN (t, a) -> Produce (Inl (Thunk (trans t), U (trans_tp a)))
| InrN (t, a) -> Produce (Inr (Thunk (trans t ), U (trans_tp a)))
| IfThEl (t1,t2,t3) -> Bind ( shift 0 1 (trans t1), IfThEl (Var 0,  (shift 0 1 (trans t2)),  (shift 0 1 (trans t3)) ))
| LetInN (x, t1, t2) -> LetIn (Thunk (trans t1), trans t2)
| FixN (tp, t) -> Fix ( trans_tp tp , trans t ) 

(* proof for true, pair, app, lam, case (easiest ot hardest) can be found in the report *)
