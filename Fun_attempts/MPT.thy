theory MPT imports Main begin 

text {*
  Proving Modus ponendo tollens in propositional calculus
*}

lemma "\<not>(A\<and>B) \<Longrightarrow> A \<Longrightarrow> \<not>B" 
  apply(rule notI)
  apply(erule notE)
  apply(rule conjI)
   apply assumption+
  done