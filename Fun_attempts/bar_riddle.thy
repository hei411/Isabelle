
(*<*) theory bar_riddle imports Main begin (*>*)

text {*
  Prove the following statement

  {\it There exists a person in the bar s.t. \\
   if he sits down, everyone else is sitting down}
*}

theorem
  "\<exists>x. (sit x \<longrightarrow> (\<forall>y. sit y))"
proof cases
  fix y
  assume a: "\<forall>x. sit x"
  then have b: "sit y" by simp
  then show ?thesis by simp
next
  assume c: "\<not>(\<forall>x. sit x)"
  then have d:"\<exists>x. \<not>sit x" by simp
  then obtain s where s:"\<not>sit s" by auto
  then show ?thesis by auto
qed

text {*
  Proof by applying rules
*}
theorem
  "\<exists>x. (P x \<longrightarrow> (\<forall>y. P y))"
  apply (rule classical)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply(rule classical)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply(erule notE)
  apply assumption
done

