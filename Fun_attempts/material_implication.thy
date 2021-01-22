theory material_implication imports Main begin 

text {*
  Proving Material Implication in propositional calculus
*}

lemma "(P\<longrightarrow>Q) = (\<not>P\<or>Q)" 
  apply (rule iffI)
   apply(rule classical)
   apply(erule impE)
    apply(rule classical)
    apply(erule notE)
  apply(rule disjI1)
    apply assumption
   apply(rule disjI2)
   apply assumption
  apply(erule disjE)
   apply(rule impI)
   apply (erule notE)
  apply assumption
  apply(rule impI)
  apply assumption
  done