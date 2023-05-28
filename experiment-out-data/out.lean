

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

  ]  = 
  TSSA.eval (Op := op) (Val := val) e re [dsl_bb|

  ]
  := by sorry