
import SSA.Core.WellTypedFramework
import SSA.Projects.InstCombine.InstCombineBase

open SSA InstCombine


-- Name:AddSub:1040
-- precondition: (C2 == ~C1)
/-
  %Y = or %Z, C2
  %X = xor %Y, C1
  %LHS = add %X, 1
  %r = add %LHS, %RHS

=>
  %and = and %Z, C1
  %Y = or %Z, C2
  %X = xor %Y, C1
  %LHS = add %X, 1
  %r = sub %RHS, %and

-/
example : TSSA.eval (Op := op) (Val := val) e re  [dsl_bb|
  ^bb
  %v3 := pair:%v1 %v2;
  %v4 := op:or %v3;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor %v6;
  %v8 := unit: ;
  %v9 := op:const 1 %v8;
  %v10 := pair:%v7 %v9;
  %v11 := op:add %v10;
  %v13 := pair:%v11 %v12;
  %v14 := op:add %v13
  dsl_ret %v14
  ]  = 
  TSSA.eval (Op := op) (Val := val) e re [dsl_bb|
  ^bb
  %v3 := pair:%v1 %v2;
  %v4 := op:and %v3;
  %v7 := pair:%v5 %v6;
  %v8 := op:or %v7;
  %v10 := pair:%v8 %v9;
  %v11 := op:xor %v10;
  %v12 := unit: ;
  %v13 := op:const 1 %v12;
  %v14 := pair:%v11 %v13;
  %v15 := op:add %v14;
  %v17 := pair:%v16 %v4;
  %v18 := op:sub %v17
  dsl_ret %v18
  ]
  := by sorry