theory idempotency imports Main begin 

text {*
  Proving idempotency of disjunction and conjunction in propositional calculus
*}

lemma "(P\<or>P) = P"
  apply(rule iffI)
   apply(erule disjE)
    apply assumption+
  apply(rule disjI1)
  apply assumption
  done

lemma"(P\<and>P) = P"
  apply (rule iffI)
  apply(erule conjE)
  apply assumption
  apply(rule conjI)
   apply assumption+
  done