(*<*) theory SV2 imports Main begin (*>*)

text {* 2005 Paper 5 Question 9 *}

lemma "((\<forall>x. (P(x) \<or> Q \<longrightarrow> \<not>R(x)) )\<and> (\<forall>x. ((Q \<longrightarrow> \<not>S(x)) \<longrightarrow> (P(x) \<and> R(x))))) \<longrightarrow> (\<forall>x. S(x))"
  apply(rule impI)
  apply(rule allI)
  apply(erule conjE)
  apply(erule allE)+
  apply (erule impE)
   apply (rule classical)
   apply(rule disjI1)
   apply(erule impE)
    apply (rule impI)
    apply (erule notE)
    apply (rule disjI2)
    apply assumption
   apply(erule conjE)
   apply assumption
  apply(rule classical)
  apply(erule impE)
  apply (rule impI)
   apply assumption
  apply(erule notE)
  apply (erule conjE)
  apply assumption
  done

lemma "\<not>( (\<not>P a)\<and> (Q a) \<and> (R b) \<and> (S b) \<and>(\<forall> x y. \<not>(Q x) \<or> (P x ) \<or> (\<not>R y) \<or>(\<not>Q y)) \<and> (\<forall>x . (\<not>S x) \<or> (\<not>R x) \<or> (Q x)) )"
  apply (rule notI)
  apply(erule conjE)+
  apply (erule notE)
  apply (erule allE)+
  apply (erule disjE)+
    apply (erule notE)
    apply assumption
   apply(erule notE)
   apply assumption
  apply (erule disjE)+
  apply (erule notE)
    apply assumption
  apply(erule notE)
   apply assumption
  apply(erule disjE)+
    apply assumption
   apply(erule notE)
   apply assumption
  apply (erule disjE)
   apply assumption
  apply (erule disjE)
  apply (erule notE)
   apply assumption
  apply(erule notE)
  apply assumption
  done
