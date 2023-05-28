

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
  %v3 := pair:%v1 %v2;
  %v4 := op:or %v3;
  %v6 := pair:%v4 %v5;
  %v7 := op:xor %v6;
  %v9 := pair:%v7 %v8;
  %v10 := op:add %v9;
  %v12 := pair:%v10 %v11;
  %v13 := op:add %v12
  return %v13
  ]  = 
  TSSA.eval (Op := op) (Val := val) e re [dsl_bb|
  %v3 := pair:%v1 %v2;
  %v4 := op:and %v3;
  %v7 := pair:%v5 %v6;
  %v8 := op:or %v7;
  %v10 := pair:%v8 %v9;
  %v11 := op:xor %v10;
  %v13 := pair:%v11 %v12;
  %v14 := op:add %v13;
  %v16 := pair:%v15 %v4;
  %v17 := op:sub %v16
  return %v17
  ]
  := by sorry