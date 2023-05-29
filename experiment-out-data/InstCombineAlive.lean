
import SSA.Core.WellTypedFramework
import SSA.Projects.InstCombine.InstCombineBase

open SSA InstCombine


-- Name:AddSub:1043
-- precondition: true
/-
  %Y = and %Z, C1
  %X = xor %Y, C1
  %LHS = add %X, 1
  %r = add %LHS, %RHS

=>
  %or = or %Z, ~C1
  %Y = and %Z, C1
  %X = xor %Y, C1
  %LHS = add %X, 1
  %r = sub %RHS, %or

-/
open SSA EDSL in
example : forall (w : Nat) (Z C1 RHS Z C1 RHS : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Z)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:xor w %v5;
  %v7 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v8 := pair:%v6 %v7;
  %v9 := op:add w %v8;
  %v10 := op:const (Bitvec.ofInt' w (RHS)) %v9999;
  %v11 := pair:%v9 %v10;
  %v12 := op:add w %v11
  dsl_ret %v12
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Z)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := op:not w %v2;
  %v4 := pair:%v1 %v3;
  %v5 := op:or w %v4;
  %v6 := pair:%v1 %v2;
  %v7 := op:and w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:xor w %v8;
  %v10 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v11 := pair:%v9 %v10;
  %v12 := op:add w %v11;
  %v13 := op:const (Bitvec.ofInt' w (RHS)) %v9999;
  %v14 := pair:%v13 %v5;
  %v15 := op:sub w %v14
  dsl_ret %v15
  ]
  := by sorry

-- Name:AddSub:1152
-- precondition: true
/-
  %r = add i1 %x, %y

=>
  %r = xor %x, %y

-/
open SSA EDSL in
example : forall (w : Nat) (x y x y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1156
-- precondition: true
/-
  %a = add %b, %b

=>
  %a = shl %b, 1

-/
open SSA EDSL in
example : forall (w : Nat) (b b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := pair:%v1 %v1;
  %v3 := op:add w %v2
  dsl_ret %v3
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1156-2
-- precondition: true
/-
  %a = add nsw %b, %b

=>
  %a = shl nsw %b, 1

-/
open SSA EDSL in
example : forall (w : Nat) (b b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := pair:%v1 %v1;
  %v3 := op:add w %v2
  dsl_ret %v3
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1156-3
-- precondition: true
/-
  %a = add nuw %b, %b

=>
  %a = shl nuw %b, 1

-/
open SSA EDSL in
example : forall (w : Nat) (b b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := pair:%v1 %v1;
  %v3 := op:add w %v2
  dsl_ret %v3
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1164
-- precondition: true
/-
  %na = sub 0, %a
  %c = add %na, %b

=>
  %na = sub 0, %a
  %c = sub %b, %a

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:add w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1165
-- precondition: true
/-
  %na = sub 0, %a
  %nb = sub 0, %b
  %c = add %na, %nb

=>
  %ab = add %a, %b
  %na = sub 0, %a
  %nb = sub 0, %b
  %c = sub 0, %ab

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:sub w %v7;
  %v9 := pair:%v4 %v8;
  %v10 := op:add w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v1;
  %v7 := op:sub w %v6;
  %v8 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v9 := pair:%v8 %v2;
  %v10 := op:sub w %v9;
  %v11 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v12 := pair:%v11 %v4;
  %v13 := op:sub w %v12
  dsl_ret %v13
  ]
  := by sorry

-- Name:AddSub:1176
-- precondition: true
/-
  %nb = sub 0, %b
  %c = add %a, %nb

=>
  %nb = sub 0, %b
  %c = sub %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (b a b a : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:add w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1295
-- precondition: true
/-
  %aab = and %a, %b
  %aob = xor %a, %b
  %c = add %aab, %aob

=>
  %aab = and %a, %b
  %aob = xor %a, %b
  %c = or %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:or w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AddSub:1309
-- precondition: true
/-
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add %lhs, %rhs

=>
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AddSub:1309-2
-- precondition: true
/-
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add nsw %lhs, %rhs

=>
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add nsw %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AddSub:1309-3
-- precondition: true
/-
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add nuw %lhs, %rhs

=>
  %lhs = and %a, %b
  %rhs = or %a, %b
  %c = add nuw %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:add w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AddSub:1539
-- precondition: true
/-
  %na = sub 0, %a
  %r = sub %x, %na

=>
  %na = sub 0, %a
  %r = add %x, %a

-/
open SSA EDSL in
example : forall (w : Nat) (a x a x : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:add w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1546
-- precondition: true
/-
  %na = sub nsw 0, %a
  %r = sub nsw %x, %na

=>
  %na = sub nsw 0, %a
  %r = add nsw %x, %a

-/
open SSA EDSL in
example : forall (w : Nat) (a x a x : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:add w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1556
-- precondition: true
/-
  %r = sub i1 %x, %y

=>
  %r = xor %x, %y

-/
open SSA EDSL in
example : forall (w : Nat) (x y x y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1560
-- precondition: true
/-
  %r = sub -1, %a

=>
  %r = xor %a, -1

-/
open SSA EDSL in
example : forall (w : Nat) (a a : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:AddSub:1614
-- precondition: true
/-
  %Op1 = add %X, %Y
  %r = sub %X, %Op1

=>
  %Op1 = add %X, %Y
  %r = sub 0, %Y

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:sub w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1619
-- precondition: true
/-
  %Op0 = sub %X, %Y
  %r = sub %Op0, %X

=>
  %Op0 = sub %X, %Y
  %r = sub 0, %Y

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := pair:%v4 %v1;
  %v6 := op:sub w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:AddSub:1624
-- precondition: true
/-
  %Op0 = or %A, %B
  %Op1 = xor %A, %B
  %r = sub %Op0, %Op1

=>
  %Op0 = or %A, %B
  %Op1 = xor %A, %B
  %r = and %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:sub w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:and w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AndOrXor:1230  ~A & ~B -> ~(A | B)
-- precondition: true
/-
  %op0 = xor %notOp0, -1
  %op1 = xor %notOp1, -1
  %r = and %op0, %op1

=>
  %or = or %notOp0, %notOp1
  %op0 = xor %notOp0, -1
  %op1 = xor %notOp1, -1
  %r = xor %or, -1

-/
open SSA EDSL in
example : forall (w : Nat) (notOp0 notOp1 notOp0 notOp1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (notOp0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (notOp1)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v4 %v8;
  %v10 := op:and w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (notOp0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (notOp1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:xor w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v2 %v8;
  %v10 := op:xor w %v9;
  %v11 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v12 := pair:%v4 %v11;
  %v13 := op:xor w %v12
  dsl_ret %v13
  ]
  := by sorry

-- Name:AndOrXor:1241 (A|B) & ~(A&B) => A^B
-- precondition: true
/-
  %op0 = or %A, %B
  %notOp1 = and %A, %B
  %op1 = xor %notOp1, -1
  %r = and %op0, %op1

=>
  %op0 = or %A, %B
  %notOp1 = and %A, %B
  %op1 = xor %notOp1, -1
  %r = xor %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:and w %v5;
  %v7 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v8 := pair:%v6 %v7;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:and w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:and w %v5;
  %v7 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v8 := pair:%v6 %v7;
  %v9 := op:xor w %v8;
  %v10 := pair:%v1 %v2;
  %v11 := op:xor w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:1247 ~(A&B) & (A|B) => A^B
-- precondition: true
/-
  %notOp0 = and %A, %B
  %op0 = xor %notOp0, -1
  %op1 = or %A, %B
  %r = and %op0, %op1

=>
  %notOp0 = and %A, %B
  %op0 = xor %notOp0, -1
  %op1 = or %A, %B
  %r = xor %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v2;
  %v9 := op:or w %v8;
  %v10 := pair:%v7 %v9;
  %v11 := op:and w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v2;
  %v9 := op:or w %v8;
  %v10 := pair:%v1 %v2;
  %v11 := op:xor w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:1253 A & (A^B) -> A & ~B
-- precondition: true
/-
  %op0 = xor %A, %B
  %r = and %op0, %A

=>
  %notB = xor %B, -1
  %op0 = xor %A, %B
  %r = and %A, %notB

-/
open SSA EDSL in
example : forall (w : Nat) (A B B A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := pair:%v4 %v1;
  %v6 := op:and w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v5 %v1;
  %v7 := op:xor w %v6;
  %v8 := pair:%v5 %v4;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:1280 (~A|B)&A -> A&B
-- precondition: true
/-
  %nA = xor %A, -1
  %op0 = or %nA, %B
  %r = and %op0, %A

=>
  %nA = xor %A, -1
  %op0 = or %nA, %B
  %r = and %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6;
  %v8 := pair:%v1 %v5;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:1288 (A ^ B) & ((B ^ C) ^ A) -> (A ^ B) & ~C
-- precondition: true
/-
  %op0 = xor %A, %B
  %x = xor %B, %C
  %op1 = xor %x, %A
  %r = and %op0, %op1

=>
  %op0 = xor %A, %B
  %negC = xor %C, -1
  %x = xor %B, %C
  %op1 = xor %x, %A
  %r = and %op0, %negC

-/
open SSA EDSL in
example : forall (w : Nat) (A B C A B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v2 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:and w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v2 %v5;
  %v10 := op:xor w %v9;
  %v11 := pair:%v10 %v1;
  %v12 := op:xor w %v11;
  %v13 := pair:%v4 %v8;
  %v14 := op:and w %v13
  dsl_ret %v14
  ]
  := by sorry

-- Name:AndOrXor:1294 (A | B) & ((~A) ^ B) -> (A & B)
-- precondition: true
/-
  %op0 = or %A, %B
  %x = xor %A, -1
  %op1 = xor %x, %B
  %r = and %op0, %op1

=>
  %op0 = or %A, %B
  %x = xor %A, -1
  %op1 = xor %x, %B
  %r = and %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:and w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:xor w %v8;
  %v10 := pair:%v1 %v2;
  %v11 := op:and w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:2113   ((~A & B) | A) -> (A | B)
-- precondition: true
/-
  %negA = xor %A, -1
  %op0 = and %negA, %B
  %r = or %op0, %A

=>
  %negA = xor %A, -1
  %op0 = and %negA, %B
  %r = or %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v1 %v5;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2118   ((A & B) | ~A) -> (~A | B)
-- precondition: true
/-
  %negA = xor %A, -1
  %op0 = and %A, %B
  %r = or %op0, %negA

=>
  %negA = xor %A, -1
  %op0 = and %A, %B
  %r = or %negA, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v7 %v4;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v4 %v5;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2123   (A & (~B)) | (A ^ B) -> (A ^ B)
-- precondition: true
/-
  %negB = xor %B, -1
  %op0 = and %A, %negB
  %op1 = xor %A, %B
  %r = or %op0, %op1

=>
  %negB = xor %B, -1
  %op0 = and %A, %negB
  %op1 = xor %A, %B
  %r = xor %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (B A B A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:and w %v6;
  %v8 := pair:%v5 %v1;
  %v9 := op:xor w %v8;
  %v10 := pair:%v7 %v9;
  %v11 := op:or w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:and w %v6;
  %v8 := pair:%v5 %v1;
  %v9 := op:xor w %v8;
  %v10 := pair:%v5 %v1;
  %v11 := op:xor w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:2188
-- precondition: true
/-
  %C = xor %D, -1
  %B = xor %A, -1
  %op0 = and %A, %C
  %op1 = and %B, %D
  %r = or %op0, %op1

=>
  %C = xor %D, -1
  %B = xor %A, -1
  %op0 = and %A, %C
  %op1 = and %B, %D
  %r = xor %A, %D

-/
open SSA EDSL in
example : forall (w : Nat) (D A D A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (D)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v5 %v4;
  %v10 := op:and w %v9;
  %v11 := pair:%v8 %v1;
  %v12 := op:and w %v11;
  %v13 := pair:%v10 %v12;
  %v14 := op:or w %v13
  dsl_ret %v14
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (D)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v5 %v4;
  %v10 := op:and w %v9;
  %v11 := pair:%v8 %v1;
  %v12 := op:and w %v11;
  %v13 := pair:%v5 %v1;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]
  := by sorry

-- Name:AndOrXor:2231  (A ^ B) | ((B ^ C) ^ A) -> (A ^ B) | C
-- precondition: true
/-
  %op0 = xor %A, %B
  %x = xor %B, %C
  %op1 = xor %x, %A
  %r = or %op0, %op1

=>
  %op0 = xor %A, %B
  %x = xor %B, %C
  %op1 = xor %x, %A
  %r = or %op0, %C

-/
open SSA EDSL in
example : forall (w : Nat) (A B C A B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v2 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:or w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v2 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v5;
  %v11 := op:or w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:2243  ((B | C) & A) | B -> B | (A & C)
-- precondition: true
/-
  %o = or %B, %C
  %op0 = and %o, %A
  %r = or %op0, %B

=>
  %a = and %A, %C
  %o = or %B, %C
  %op0 = and %o, %A
  %r = or %B, %a

-/
open SSA EDSL in
example : forall (w : Nat) (B C A A C B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:or w %v6;
  %v8 := pair:%v7 %v1;
  %v9 := op:and w %v8;
  %v10 := pair:%v5 %v4;
  %v11 := op:or w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:2247  (~A | ~B) == (~(A & B))
-- precondition: true
/-
  %na = xor %A, -1
  %nb = xor %B, -1
  %r = or %na, %nb

=>
  %a = and %A, %B
  %na = xor %A, -1
  %nb = xor %B, -1
  %r = xor %a, -1

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v4 %v8;
  %v10 := op:or w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:xor w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v2 %v8;
  %v10 := op:xor w %v9;
  %v11 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v12 := pair:%v4 %v11;
  %v13 := op:xor w %v12
  dsl_ret %v13
  ]
  := by sorry

-- Name:AndOrXor:2263
-- precondition: true
/-
  %op1 = xor %op0, %B
  %r = or %op0, %op1

=>
  %op1 = xor %op0, %B
  %r = or %op0, %B

-/
open SSA EDSL in
example : forall (w : Nat) (op0 B op0 B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (op0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:or w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (op0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5
  dsl_ret %v6
  ]
  := by sorry

-- Name:AndOrXor:2264
-- precondition: true
/-
  %na = xor %A, -1
  %op1 = xor %na, %B
  %r = or %A, %op1

=>
  %nb = xor %B, -1
  %na = xor %A, -1
  %op1 = xor %na, %B
  %r = or %A, %nb

-/
open SSA EDSL in
example : forall (w : Nat) (A B B A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v8 %v1;
  %v10 := op:xor w %v9;
  %v11 := pair:%v5 %v4;
  %v12 := op:or w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2265
-- precondition: true
/-
  %op0 = and %A, %B
  %op1 = xor %A, %B
  %r = or %op0, %op1

=>
  %op0 = and %A, %B
  %op1 = xor %A, %B
  %r = or %A, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:or w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:or w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AndOrXor:2284
-- precondition: true
/-
  %o = or %A, %B
  %op1 = xor %o, -1
  %r = or %A, %op1

=>
  %not = xor %B, -1
  %o = or %A, %B
  %op1 = xor %o, -1
  %r = or %A, %not

-/
open SSA EDSL in
example : forall (w : Nat) (A B B A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v5 %v1;
  %v7 := op:or w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:xor w %v9;
  %v11 := pair:%v5 %v4;
  %v12 := op:or w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2285
-- precondition: true
/-
  %o = xor %A, %B
  %op1 = xor %o, -1
  %r = or %A, %op1

=>
  %not = xor %B, -1
  %o = xor %A, %B
  %op1 = xor %o, -1
  %r = or %A, %not

-/
open SSA EDSL in
example : forall (w : Nat) (A B B A : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v6 := pair:%v5 %v1;
  %v7 := op:xor w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:xor w %v9;
  %v11 := pair:%v5 %v4;
  %v12 := op:or w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2297
-- precondition: true
/-
  %op0 = and %A, %B
  %na = xor %A, -1
  %op1 = xor %na, %B
  %r = or %op0, %op1

=>
  %na = xor %A, -1
  %op0 = and %A, %B
  %op1 = xor %na, %B
  %r = xor %na, %B

-/
open SSA EDSL in
example : forall (w : Nat) (A B A B : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:or w %v10
  dsl_ret %v11
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v4 %v5;
  %v9 := op:xor w %v8;
  %v10 := pair:%v4 %v5;
  %v11 := op:xor w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:AndOrXor:2367
-- precondition: true
/-
  %op0 = or %A, C1
  %r = or %op0, %op1

=>
  %i = or %A, %op1
  %op0 = or %A, C1
  %r = or %i, C1

-/
open SSA EDSL in
example : forall (w : Nat) (A C1 op1 A op1 C1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:or w %v6;
  %v8 := pair:%v4 %v5;
  %v9 := op:or w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2416
-- precondition: true
/-
  %x = xor %nx, -1
  %op0 = and %x, %y
  %r = xor %op0, -1

=>
  %ny = xor %y, -1
  %x = xor %nx, -1
  %op0 = and %x, %y
  %r = or %nx, %ny

-/
open SSA EDSL in
example : forall (w : Nat) (nx y y nx : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (nx)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:xor w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (nx)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v8 %v1;
  %v10 := op:and w %v9;
  %v11 := pair:%v5 %v4;
  %v12 := op:or w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2417
-- precondition: true
/-
  %x = xor %nx, -1
  %op0 = or %x, %y
  %r = xor %op0, -1

=>
  %ny = xor %y, -1
  %x = xor %nx, -1
  %op0 = or %x, %y
  %r = and %nx, %ny

-/
open SSA EDSL in
example : forall (w : Nat) (nx y y nx : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (nx)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:xor w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (nx)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v8 %v1;
  %v10 := op:or w %v9;
  %v11 := pair:%v5 %v4;
  %v12 := op:and w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2429
-- precondition: true
/-
  %op0 = and %x, %y
  %r = xor %op0, -1

=>
  %nx = xor %x, -1
  %ny = xor %y, -1
  %op0 = and %x, %y
  %r = or %nx, %ny

-/
open SSA EDSL in
example : forall (w : Nat) (x y x y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v5;
  %v10 := op:and w %v9;
  %v11 := pair:%v4 %v8;
  %v12 := op:or w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2430
-- precondition: true
/-
  %op0 = or %x, %y
  %r = xor %op0, -1

=>
  %nx = xor %x, -1
  %ny = xor %y, -1
  %op0 = or %x, %y
  %r = and %nx, %ny

-/
open SSA EDSL in
example : forall (w : Nat) (x y x y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v5;
  %v10 := op:or w %v9;
  %v11 := pair:%v4 %v8;
  %v12 := op:and w %v11
  dsl_ret %v12
  ]
  := by sorry

-- Name:AndOrXor:2443
-- precondition: true
/-
  %nx = xor %x, -1
  %op0 = ashr %nx, %y
  %r = xor %op0, -1

=>
  %nx = xor %x, -1
  %op0 = ashr %nx, %y
  %r = ashr %x, %y

-/
open SSA EDSL in
example : forall (w : Nat) (x y x y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:ashr w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:xor w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (y)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:ashr w %v6;
  %v8 := pair:%v1 %v5;
  %v9 := op:ashr w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2581  (B|A)^B -> A & ~B
-- precondition: true
/-
  %op0 = or %a, %op1
  %r = xor %op0, %op1

=>
  %nop1 = xor %op1, -1
  %op0 = or %a, %op1
  %r = and %a, %nop1

-/
open SSA EDSL in
example : forall (w : Nat) (a op1 op1 a : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:xor w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v6 := pair:%v5 %v1;
  %v7 := op:or w %v6;
  %v8 := pair:%v5 %v4;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2587  (B&A)^A -> ~B & A
-- precondition: true
/-
  %op0 = and %a, %op1
  %r = xor %op0, %op1

=>
  %na = xor %a, -1
  %op0 = and %a, %op1
  %r = and %na, %op1

-/
open SSA EDSL in
example : forall (w : Nat) (a op1 a op1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:xor w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (op1)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:and w %v6;
  %v8 := pair:%v4 %v5;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:AndOrXor:2595
-- precondition: true
/-
  %op0 = and %a, %b
  %op1 = or %a, %b
  %r = xor %op0, %op1

=>
  %op0 = and %a, %b
  %op1 = or %a, %b
  %r = xor %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:xor w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:or w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:xor w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AndOrXor:2607
-- precondition: true
/-
  %na = xor %a, -1
  %nb = xor %b, -1
  %op0 = or %a, %nb
  %op1 = or %na, %b
  %r = xor %op0, %op1

=>
  %na = xor %a, -1
  %nb = xor %b, -1
  %op0 = or %a, %nb
  %op1 = or %na, %b
  %r = xor %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v8;
  %v10 := op:or w %v9;
  %v11 := pair:%v4 %v5;
  %v12 := op:or w %v11;
  %v13 := pair:%v10 %v12;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v8;
  %v10 := op:or w %v9;
  %v11 := pair:%v4 %v5;
  %v12 := op:or w %v11;
  %v13 := pair:%v1 %v5;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]
  := by sorry

-- Name:AndOrXor:2617
-- precondition: true
/-
  %na = xor %a, -1
  %nb = xor %b, -1
  %op0 = and %a, %nb
  %op1 = and %na, %b
  %r = xor %op0, %op1

=>
  %na = xor %a, -1
  %nb = xor %b, -1
  %op0 = and %a, %nb
  %op1 = and %na, %b
  %r = xor %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v8;
  %v10 := op:and w %v9;
  %v11 := pair:%v4 %v5;
  %v12 := op:and w %v11;
  %v13 := pair:%v10 %v12;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:xor w %v7;
  %v9 := pair:%v1 %v8;
  %v10 := op:and w %v9;
  %v11 := pair:%v4 %v5;
  %v12 := op:and w %v11;
  %v13 := pair:%v1 %v5;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]
  := by sorry

-- Name:AndOrXor:2627
-- precondition: true
/-
  %op0 = xor %a, %c
  %op1 = or %a, %b
  %r = xor %op0, %op1

=>
  %na = xor %a, -1
  %and = and %na, %b
  %op0 = xor %a, %c
  %op1 = or %a, %b
  %r = xor %and, %c

-/
open SSA EDSL in
example : forall (w : Nat) (a c b a b c : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (c)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:or w %v6;
  %v8 := pair:%v4 %v7;
  %v9 := op:xor w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (c)) %v9999;
  %v9 := pair:%v1 %v8;
  %v10 := op:xor w %v9;
  %v11 := pair:%v1 %v5;
  %v12 := op:or w %v11;
  %v13 := pair:%v7 %v8;
  %v14 := op:xor w %v13
  dsl_ret %v14
  ]
  := by sorry

-- Name:AndOrXor:2647
-- precondition: true
/-
  %op0 = and %a, %b
  %op1 = xor %a, %b
  %r = xor %op0, %op1

=>
  %op0 = and %a, %b
  %op1 = xor %a, %b
  %r = or %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v4 %v6;
  %v8 := op:xor w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:xor w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:or w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:AndOrXor:2658
-- precondition: true
/-
  %nb = xor %b, -1
  %op0 = and %a, %nb
  %na = xor %a, -1
  %r = xor %op0, %na

=>
  %and = and %a, %b
  %nb = xor %b, -1
  %op0 = and %a, %nb
  %na = xor %a, -1
  %r = xor %and, -1

-/
open SSA EDSL in
example : forall (w : Nat) (b a a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v9 := pair:%v5 %v8;
  %v10 := op:xor w %v9;
  %v11 := pair:%v7 %v10;
  %v12 := op:xor w %v11
  dsl_ret %v12
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v2 %v5;
  %v7 := op:xor w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:and w %v8;
  %v10 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v11 := pair:%v1 %v10;
  %v12 := op:xor w %v11;
  %v13 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v14 := pair:%v4 %v13;
  %v15 := op:xor w %v14
  dsl_ret %v15
  ]
  := by sorry

-- Name:152
-- precondition: true
/-
  %r = mul %x, -1

=>
  %r = sub 0, %x

-/
open SSA EDSL in
example : forall (w : Nat) (x x : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:mul w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:160
-- precondition: true
/-
  %sh = shl i7 %x, C2
  %r = mul %sh, C1

=>
  %sh = shl i7 %x, C2
  %r = mul %x, (C1 << C2)

-/
open SSA EDSL in
example : forall (w : Nat) (x C2 C1 x C2 C1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:mul w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:shl w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:229
-- precondition: true
/-
  %Op0 = add %X, C1
  %r = mul %Op0, %Op1

=>
  %mul = mul C1, %Op1
  %tmp = mul %X, %Op1
  %Op0 = add %X, C1
  %r = add %tmp, %mul

-/
open SSA EDSL in
example : forall (w : Nat) (X C1 Op1 C1 Op1 X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:mul w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:mul w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:mul w %v6;
  %v8 := pair:%v5 %v1;
  %v9 := op:add w %v8;
  %v10 := pair:%v7 %v4;
  %v11 := op:add w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:239
-- precondition: true
/-
  %a = sub 0, %X
  %b = sub 0, %Y
  %r = mul %a, %b

=>
  %a = sub 0, %X
  %b = sub 0, %Y
  %r = mul %X, %Y

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:sub w %v7;
  %v9 := pair:%v4 %v8;
  %v10 := op:mul w %v9
  dsl_ret %v10
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v7 := pair:%v5 %v6;
  %v8 := op:sub w %v7;
  %v9 := pair:%v2 %v6;
  %v10 := op:mul w %v9
  dsl_ret %v10
  ]
  := by sorry

-- Name:266
-- precondition: true
/-
  %div = udiv exact %X, %Y
  %negY = sub 0, %Y
  %r = mul %div, %negY

=>
  %div = udiv exact %X, %Y
  %negY = sub 0, %Y
  %r = sub 0, %X

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:udiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := pair:%v4 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:udiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v9 := pair:%v8 %v1;
  %v10 := op:sub w %v9
  dsl_ret %v10
  ]
  := by sorry

-- Name:266-2
-- precondition: true
/-
  %div = sdiv exact %X, %Y
  %negY = sub 0, %Y
  %r = mul %div, %negY

=>
  %div = sdiv exact %X, %Y
  %negY = sub 0, %Y
  %r = sub 0, %X

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sdiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := pair:%v4 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sdiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v9 := pair:%v8 %v1;
  %v10 := op:sub w %v9
  dsl_ret %v10
  ]
  := by sorry

-- Name:275
-- precondition: true
/-
  %div = udiv i5 %X, %Y
  %r = mul %div, %Y

=>
  %rem = urem %X, %Y
  %div = udiv i5 %X, %Y
  %r = sub %X, %rem

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:udiv w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:mul w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:urem w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:udiv w %v5;
  %v7 := pair:%v1 %v4;
  %v8 := op:sub w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:275-2
-- precondition: true
/-
  %div = sdiv i5 %X, %Y
  %r = mul %div, %Y

=>
  %rem = srem %X, %Y
  %div = sdiv i5 %X, %Y
  %r = sub %X, %rem

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sdiv w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:mul w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:srem w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:sdiv w %v5;
  %v7 := pair:%v1 %v4;
  %v8 := op:sub w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:276
-- precondition: true
/-
  %div = sdiv i5 %X, %Y
  %negY = sub 0, %Y
  %r = mul %div, %negY

=>
  %rem = srem %X, %Y
  %div = sdiv i5 %X, %Y
  %negY = sub 0, %Y
  %r = sub %rem, %X

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sdiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := pair:%v4 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:srem w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:sdiv w %v5;
  %v7 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v8 := pair:%v7 %v2;
  %v9 := op:sub w %v8;
  %v10 := pair:%v4 %v1;
  %v11 := op:sub w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:276-2
-- precondition: true
/-
  %div = udiv i5 %X, %Y
  %negY = sub 0, %Y
  %r = mul %div, %negY

=>
  %rem = urem %X, %Y
  %div = udiv i5 %X, %Y
  %negY = sub 0, %Y
  %r = sub %rem, %X

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:udiv w %v3;
  %v5 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:sub w %v6;
  %v8 := pair:%v4 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:urem w %v3;
  %v5 := pair:%v1 %v2;
  %v6 := op:udiv w %v5;
  %v7 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v8 := pair:%v7 %v2;
  %v9 := op:sub w %v8;
  %v10 := pair:%v4 %v1;
  %v11 := op:sub w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:283
-- precondition: true
/-
  %r = mul i1 %X, %Y

=>
  %r = and %X, %Y

-/
open SSA EDSL in
example : forall (w : Nat) (X Y X Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:mul w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:290 & 292
-- precondition: true
/-
  %Op0 = shl 1, %Y
  %r = mul %Op0, %Op1

=>
  %Op0 = shl 1, %Y
  %r = shl %Op1, %Y

-/
open SSA EDSL in
example : forall (w : Nat) (Y Op1 Y Op1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:mul w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:shl w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:820
-- precondition: true
/-
  %Z = srem i9 %X, %Op1
  %Op0 = sub %X, %Z
  %r = sdiv %Op0, %Op1

=>
  %Z = srem i9 %X, %Op1
  %Op0 = sub %X, %Z
  %r = sdiv %X, %Op1

-/
open SSA EDSL in
example : forall (w : Nat) (X Op1 X Op1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:srem w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:sub w %v5;
  %v7 := pair:%v6 %v2;
  %v8 := op:sdiv w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:srem w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:sub w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:sdiv w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:820
-- precondition: true
/-
  %Z = urem i9 %X, %Op1
  %Op0 = sub %X, %Z
  %r = udiv %Op0, %Op1

=>
  %Z = urem i9 %X, %Op1
  %Op0 = sub %X, %Z
  %r = udiv %X, %Op1

-/
open SSA EDSL in
example : forall (w : Nat) (X Op1 X Op1 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:urem w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:sub w %v5;
  %v7 := pair:%v6 %v2;
  %v8 := op:udiv w %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (Op1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:urem w %v3;
  %v5 := pair:%v1 %v4;
  %v6 := op:sub w %v5;
  %v7 := pair:%v1 %v2;
  %v8 := op:udiv w %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:891
-- precondition: true
/-
  %s = shl i13 1, %N
  %r = udiv %x, %s

=>
  %s = shl i13 1, %N
  %r = lshr %x, %N

-/
open SSA EDSL in
example : forall (w : Nat) (N x N x : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (N)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:udiv w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (N)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:lhsr w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:891-exact
-- precondition: true
/-
  %s = shl i13 1, %N
  %r = udiv exact %x, %s

=>
  %s = shl i13 1, %N
  %r = lshr exact %x, %N

-/
open SSA EDSL in
example : forall (w : Nat) (N x N x : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (N)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:udiv w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (N)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (x)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:lhsr w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:1030
-- precondition: true
/-
  %r = sdiv %X, -1

=>
  %r = sub 0, %X

-/
open SSA EDSL in
example : forall (w : Nat) (X X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sdiv w %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (0)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:sub w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:Select:846
-- precondition: true
/-
  %A = select i1 %B, true, %C

=>
  %A = or %B, %C

-/
open SSA EDSL in
example : forall (w : Nat) (B C B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v3 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v4 := triple:%v1 %v2 %v3;
  %v5 := op:select %v4
  dsl_ret %v5
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:Select:850
-- precondition: true
/-
  %A = select i1 %B, false, %C

=>
  %notb = xor i1 %B, true
  %A = and %notb, %C

-/
open SSA EDSL in
example : forall (w : Nat) (B C B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (false)) %v9999;
  %v3 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v4 := triple:%v1 %v2 %v3;
  %v5 := op:select %v4
  dsl_ret %v5
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:Select:855
-- precondition: true
/-
  %A = select i1 %B, %C, false

=>
  %A = and %B, %C

-/
open SSA EDSL in
example : forall (w : Nat) (B C B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := op:const (Bitvec.ofInt' w (false)) %v9999;
  %v4 := triple:%v1 %v2 %v3;
  %v5 := op:select %v4
  dsl_ret %v5
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:Select:859
-- precondition: true
/-
  %A = select i1 %B, %C, true

=>
  %notb = xor i1 %B, true
  %A = or %notb, %C

-/
open SSA EDSL in
example : forall (w : Nat) (B C B C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v4 := triple:%v1 %v2 %v3;
  %v5 := op:select %v4
  dsl_ret %v5
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (B)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:Select:851
-- precondition: true
/-
  %r = select i1 %a, %b, %a

=>
  %r = and %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := triple:%v1 %v2 %v1;
  %v4 := op:select %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:and w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:Select:852
-- precondition: true
/-
  %r = select i1 %a, %a, %b

=>
  %r = or %a, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := triple:%v1 %v1 %v2;
  %v4 := op:select %v3
  dsl_ret %v4
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:or w %v3
  dsl_ret %v4
  ]
  := by sorry

-- Name:Select:858
-- precondition: true
/-
  %nota = xor %a, -1
  %r = select i1 %a, %nota, %b

=>
  %nota = xor %a, -1
  %r = and %nota, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := triple:%v1 %v4 %v5;
  %v7 := op:select %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:Select:859
-- precondition: true
/-
  %nota = xor %a, -1
  %r = select i1 %a, %b, %nota

=>
  %nota = xor %a, -1
  %r = or %nota, %b

-/
open SSA EDSL in
example : forall (w : Nat) (a b a b : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := triple:%v1 %v5 %v4;
  %v7 := op:select %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (a)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (b)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:or w %v6
  dsl_ret %v7
  ]
  := by sorry

-- Name:Select:1087
-- precondition: true
/-
  %c = xor i1 %val, true
  %r = select i1 %c, %X, %Y

=>
  %c = xor i1 %val, true
  %r = select i1 %val, %Y, %X

-/
open SSA EDSL in
example : forall (w : Nat) (val X Y val Y X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (val)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v7 := triple:%v4 %v5 %v6;
  %v8 := op:select %v7
  dsl_ret %v8
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (val)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (true)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:xor w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v7 := triple:%v1 %v5 %v6;
  %v8 := op:select %v7
  dsl_ret %v8
  ]
  := by sorry

-- Name:InstCombineShift: 279
-- precondition: true
/-
  %Op0 = lshr %X, C
  %r = shl %Op0, C

=>
  %Op0 = lshr %X, C
  %r = and %X, (-1 << C)

-/
open SSA EDSL in
example : forall (w : Nat) (X C X C : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:lhsr w %v3;
  %v5 := pair:%v4 %v2;
  %v6 := op:shl w %v5
  dsl_ret %v6
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:lhsr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v6 := pair:%v5 %v2;
  %v7 := op:shl w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:and w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:InstCombineShift: 351
-- precondition: true
/-
  %Op0 = mul i7 %X, C1
  %r = shl %Op0, C2

=>
  %Op0 = mul i7 %X, C1
  %r = mul %X, (C1 << C2)

-/
open SSA EDSL in
example : forall (w : Nat) (X C1 C2 X C1 C2 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:mul w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:shl w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:mul w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v2 %v5;
  %v7 := op:shl w %v6;
  %v8 := pair:%v1 %v7;
  %v9 := op:mul w %v8
  dsl_ret %v9
  ]
  := by sorry

-- Name:InstCombineShift: 422-1
-- precondition: true
/-
  %Op1 = lshr i31 %X, C
  %Op0 = add %Y, %Op1
  %r = shl %Op0, C

=>
  %s = shl %Y, C
  %a = add %s, %X
  %Op1 = lshr i31 %X, C
  %Op0 = add %Y, %Op1
  %r = and %a, (-1 << C)

-/
open SSA EDSL in
example : forall (w : Nat) (X C Y Y C X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:lhsr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:add w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:shl w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:add w %v6;
  %v8 := pair:%v5 %v2;
  %v9 := op:lhsr w %v8;
  %v10 := pair:%v1 %v9;
  %v11 := op:add w %v10;
  %v12 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v13 := pair:%v12 %v2;
  %v14 := op:shl w %v13;
  %v15 := pair:%v7 %v14;
  %v16 := op:and w %v15
  dsl_ret %v16
  ]
  := by sorry

-- Name:InstCombineShift: 422-2
-- precondition: true
/-
  %Op1 = ashr i31 %X, C
  %Op0 = add %Y, %Op1
  %r = shl %Op0, C

=>
  %s = shl %Y, C
  %a = add %s, %X
  %Op1 = ashr i31 %X, C
  %Op0 = add %Y, %Op1
  %r = and %a, (-1 << C)

-/
open SSA EDSL in
example : forall (w : Nat) (X C Y Y C X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:ashr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:add w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:shl w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:add w %v6;
  %v8 := pair:%v5 %v2;
  %v9 := op:ashr w %v8;
  %v10 := pair:%v1 %v9;
  %v11 := op:add w %v10;
  %v12 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v13 := pair:%v12 %v2;
  %v14 := op:shl w %v13;
  %v15 := pair:%v7 %v14;
  %v16 := op:and w %v15
  dsl_ret %v16
  ]
  := by sorry

-- Name:InstCombineShift: 440
-- precondition: true
/-
  %s = lshr %X, C
  %Op1 = and %s, C2
  %Op0 = xor %Y, %Op1
  %r = shl %Op0, C

=>
  %a = and %X, (C2 << C)
  %y2 = shl %Y, C
  %s = lshr %X, C
  %Op1 = and %s, C2
  %Op0 = xor %Y, %Op1
  %r = xor %a, %y2

-/
open SSA EDSL in
example : forall (w : Nat) (X C C2 Y X C2 C Y : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:lhsr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v9 := pair:%v8 %v7;
  %v10 := op:xor w %v9;
  %v11 := pair:%v10 %v2;
  %v12 := op:shl w %v11
  dsl_ret %v12
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v3 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v4 := pair:%v2 %v3;
  %v5 := op:shl w %v4;
  %v6 := pair:%v1 %v5;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v9 := pair:%v8 %v3;
  %v10 := op:shl w %v9;
  %v11 := pair:%v1 %v3;
  %v12 := op:lhsr w %v11;
  %v13 := pair:%v12 %v2;
  %v14 := op:and w %v13;
  %v15 := pair:%v8 %v14;
  %v16 := op:xor w %v15;
  %v17 := pair:%v7 %v10;
  %v18 := op:xor w %v17
  dsl_ret %v18
  ]
  := by sorry

-- Name:InstCombineShift: 458
-- precondition: true
/-
  %s = ashr i31 %X, C
  %Op0 = sub %s, %Y
  %r = shl %Op0, C

=>
  %s2 = shl %Y, C
  %a = sub %X, %s2
  %s = ashr i31 %X, C
  %Op0 = sub %s, %Y
  %r = and %a, (-1 << C)

-/
open SSA EDSL in
example : forall (w : Nat) (X C Y Y C X : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:ashr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:sub w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:shl w %v8
  dsl_ret %v9
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := pair:%v5 %v4;
  %v7 := op:sub w %v6;
  %v8 := pair:%v5 %v2;
  %v9 := op:ashr w %v8;
  %v10 := pair:%v9 %v1;
  %v11 := op:sub w %v10;
  %v12 := op:const (Bitvec.ofInt' w (-1)) %v9999;
  %v13 := pair:%v12 %v2;
  %v14 := op:shl w %v13;
  %v15 := pair:%v7 %v14;
  %v16 := op:and w %v15
  dsl_ret %v16
  ]
  := by sorry

-- Name:InstCombineShift: 476
-- precondition: true
/-
  %shr = lshr %X, C
  %s = and %shr, C2
  %Op0 = or %s, %Y
  %r = shl %Op0, C

=>
  %s2 = shl %Y, C
  %a = and %X, (C2 << C)
  %shr = lshr %X, C
  %s = and %shr, C2
  %Op0 = or %s, %Y
  %r = or %a, %s2

-/
open SSA EDSL in
example : forall (w : Nat) (X C C2 Y Y C X C2 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:lhsr w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:and w %v6;
  %v8 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v9 := pair:%v7 %v8;
  %v10 := op:or w %v9;
  %v11 := pair:%v10 %v2;
  %v12 := op:shl w %v11
  dsl_ret %v12
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (Y)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v6 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v7 := pair:%v6 %v2;
  %v8 := op:shl w %v7;
  %v9 := pair:%v5 %v8;
  %v10 := op:and w %v9;
  %v11 := pair:%v5 %v2;
  %v12 := op:lhsr w %v11;
  %v13 := pair:%v12 %v6;
  %v14 := op:and w %v13;
  %v15 := pair:%v14 %v1;
  %v16 := op:or w %v15;
  %v17 := pair:%v10 %v4;
  %v18 := op:or w %v17
  dsl_ret %v18
  ]
  := by sorry

-- Name:InstCombineShift: 497
-- precondition: true
/-
  %Op0 = add %X, C2
  %r = shl %Op0, C

=>
  %s2 = shl %X, C
  %Op0 = add %X, C2
  %r = add %s2, (C2 << C)

-/
open SSA EDSL in
example : forall (w : Nat) (X C2 C X C C2 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:add w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:shl w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (X)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (C)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:add w %v6;
  %v8 := pair:%v5 %v2;
  %v9 := op:shl w %v8;
  %v10 := pair:%v4 %v9;
  %v11 := op:add w %v10
  dsl_ret %v11
  ]
  := by sorry

-- Name:InstCombineShift: 724
-- precondition: true
/-
  %Op0 = shl i31 C1, %A
  %r = shl %Op0, C2

=>
  %Op0 = shl i31 C1, %A
  %r = shl (C1 << C2), %A

-/
open SSA EDSL in
example : forall (w : Nat) (C1 A C2 C1 A C2 : Nat),TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v4 %v5;
  %v7 := op:shl w %v6
  dsl_ret %v7
  ]  = 
  TSSA.eval
  (Op := Op) (e := e)
  (i := TSSAIndex.TERMINATOR (UserType.base (BaseType.bitvec w)))
  [dsl_bb|
  ^bb
  %v9999 := unit: ;
  %v1 := op:const (Bitvec.ofInt' w (C1)) %v9999;
  %v2 := op:const (Bitvec.ofInt' w (A)) %v9999;
  %v3 := pair:%v1 %v2;
  %v4 := op:shl w %v3;
  %v5 := op:const (Bitvec.ofInt' w (C2)) %v9999;
  %v6 := pair:%v1 %v5;
  %v7 := op:shl w %v6;
  %v8 := pair:%v7 %v2;
  %v9 := op:shl w %v8
  dsl_ret %v9
  ]
  := by sorry