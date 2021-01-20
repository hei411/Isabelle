theory absorption imports Main begin 

text {*
  Proving the absorption rule in propositional calculus
*}

lemma "(P\<longrightarrow>Q) = (P\<longrightarrow> (P\<and>Q))"
  apply (rule iffI)
   apply(rule impI)
   apply(rule conjI)
    apply(assumption)
   apply(erule mp)
   apply assumption
  apply(rule impI)
  apply(erule impE)
   apply assumption
  apply(erule conjE)
  apply assumption
  done
