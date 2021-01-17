theory exportation imports Main begin 

text {*
  Proving the exportation rule in propositional calculus
*}

lemma "((P\<and>Q)\<longrightarrow>R) = (P\<longrightarrow>(Q\<longrightarrow>R))" 
  apply(rule iffI)
   apply(rule impI)+
   apply(erule impE)
    apply(rule conjI)
     apply assumption+
  apply(rule impI)+
  apply(erule impE)
   apply (erule conjE)
   apply assumption
  apply(erule conjE)
  apply (erule impE)
   apply assumption+
  done