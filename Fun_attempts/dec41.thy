theory dec41 imports Main begin 

text {*
  Proving two exercises in dec41 Proof Theory notes in propositional calculus
*}

lemma "A  \<longrightarrow>((((A \<longrightarrow> B) \<longrightarrow> B) \<longrightarrow> C) \<longrightarrow> C)"
  apply (rule impI)+
  apply (erule impE)
   apply (rule impI)
   apply (erule mp)
   apply assumption+
  done

lemma "((((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P) \<longrightarrow> Q) \<longrightarrow> Q"
  apply (rule impI)+
  apply(erule impE)
   apply (rule impI)+
   apply(rule classical)
   apply(erule mp)
  apply(rule impI)
  apply (erule notE)
   apply assumption+
  done
 