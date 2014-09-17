bool runOnInstruction(Instruction *I) {

  { // Test1
    Value *V_0;
    ConstantInt *C2;
    Value *x;
    ConstantInt *C1;

    if (match(I, m_Add(m_Value(V_0), m_ConstantInt(C2)))
          && match(V_0, m_Add(m_Value(x), m_ConstantInt(C1))))
    {
        Value *V_1 =
            BinaryOperator::Create(Instruction::Add,
                x,
                ConstantInt::get(I->getType(), C1->getValue() + C2->getValue()),
                "",
                I);
        I->replaceAllUsesWith(V_1);
        return true;
    }
  }
{ // Select:1031
    Value *c2;
    Value *a;
    Value *r1;
    Value *c1;
    Value *b;
    CmpInst::Predicate P_cmp;
    CmpInst::Predicate P_c2;
    
    if (match(I, m_Select(m_Value(c2), m_Value(a), m_Value(r1)))
          && match(r1, m_Select(m_Value(c1), m_Specific(a), m_Value(b)))
          && match(c1, m_ICmp(P_cmp, m_Specific(a), m_Specific(b)))
          && match(c2, m_ICmp(P_c2, m_Specific(a), m_Specific(r1)))
          && P_c2 == P_cmp)
    {
        Value *c = new ICmpInst(I, P_cmp, a, b, "");
        Value *r2 = SelectInst::Create(c, a, b, "", I);
        I->replaceAllUsesWith(r2);
        return true;
    }
}

  return false;
}
