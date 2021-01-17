theory negation_introduction imports Main begin 

text {*
  Proving the negation introduction in propositional calculus
*}

lemma "((P\<longrightarrow>Q)\<and>(P\<longrightarrow>\<not>Q) )= (\<not>P)"
  apply (rule iffI)
   apply(erule conjE)
   apply(rule notI)
   apply(erule impE)
    apply assumption
   apply(erule impE)
    apply assumption
   apply(erule notE)
   apply assumption
  apply(rule conjI)
   apply(rule impI)
   apply(erule notE)
   apply assumption
  apply(rule impI)
  apply (erule notE)
  apply assumption
  done