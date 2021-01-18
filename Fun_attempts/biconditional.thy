theory biconditional imports Main begin 

text {*
  Proving the biconditional rule in propositional calculus
*}

lemma "((P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P)) = (P=Q)" 
  apply(rule iffI)
   apply(rule iffI)
    apply(erule conjE)
    apply(erule impE)
     apply assumption
    apply assumption
   apply(erule conjE)
   apply(erule impE)+
     apply assumption+
   apply(erule impE)
    apply assumption+
  apply (erule iffE)
  apply(rule conjI)
   apply assumption+
  done
     
