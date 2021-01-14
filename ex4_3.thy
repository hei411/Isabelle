
header {* Predicate Logic *}

(*<*) theory ex4_3 imports Main begin (*>*)

text {*
We are again talking about proofs in the calculus of Natural Deduction.  In
addition to the rules given in the exercise ``Propositional Logic'', you may
now also use

  @{text "exI:"}~@{thm exI[no_vars]}\\
  @{text "exE:"}~@{thm exE[no_vars]}\\
  @{text "allI:"}~@{thm allI[no_vars]}\\
  @{text "allE:"}~@{thm allE[no_vars]}\\

Give a proof of the following propositions or an argument why the formula is
not valid:
*}

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  apply(rule impI)
  apply (erule exE)
  apply (rule allI)
  apply (erule allE)
  apply(rule exI)
  apply assumption
  done
lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  apply (rule iffI)
   apply (rule impI)+
   apply(erule exE)
   apply(erule allE)
   apply(rule impE)
     apply assumption+

  apply (rule allI)
  apply(rule impI)
  apply (erule impE)
   apply (rule exI)
   apply assumption
  apply assumption
  done
  


lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
  apply (rule iffI)
   apply(rule allI)
   apply (rule conjI)
    apply(erule conjE)
    apply (erule allE)+
    apply assumption
   apply(erule conjE)
   apply (erule allE)+
   apply assumption

  apply(rule conjI)
   apply (rule allI)
   apply (erule allE)
   apply(erule conjE)
   apply assumption
  apply(rule allI)
  apply (erule allE)
  apply(erule conjE)
  apply assumption
  done

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
  quickcheck
  oops

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
  apply(rule iffI)
   apply (erule disjE)
apply (erule exE)
apply (rule exI)
    apply (rule disjI1)
    apply assumption

   apply (erule exE)
   apply (rule exI)
   apply (erule disjI2)
  apply (erule exE)
  apply (erule disjE)
   apply(rule disjI1)
   apply (rule exI)
   apply assumption
  apply(rule disjI2)
  apply (rule exI)
  apply assumption
  done
   

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  quickcheck oops

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply(rule iffI)
   apply(rule classical)
   apply(erule notE)
   apply(rule allI)
   apply(rule classical)
   apply(erule notE)
  apply(rule exI)
   apply assumption

  apply(erule exE)
  apply(rule notI)
  apply(erule allE)
  apply(erule notE)
  apply assumption
  done


(*<*) end (*>*)