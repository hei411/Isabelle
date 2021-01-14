
(*<*) theory ex4_1 imports Main begin (*>*)

text {* In classical propositional logic, the connectives @{text "=, \<or>,
\<not>"} can be replaced by @{text "\<longrightarrow>, \<and>, False"}.  Define
corresponding simplification rules as lemmas and prove their correctness.  (You
may use automated proof tactics.) *}
lemma one: "(A=B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow>A))" 
  apply auto
  done
lemma two: " (A \<or> B) = (\<not>(\<not>A \<and> \<not>B))"
  apply auto
  done
lemma three:"(\<not> A) = (A \<longrightarrow> False)"
  apply auto
  done


text {* What is the result of your translation for the formula @{text "A \<or>
(B \<and> C) = A"}?  (You can use Isabelle's simplifier to compute the result
by using the simplifier's @{text "only"} option.) *}
lemma "A \<or> (B \<and> C) = A"
  apply (simp only: one two three)
  oops
  

(*<*) end (*>*)