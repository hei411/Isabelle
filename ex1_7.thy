

(*<*) theory ex1_7 imports Main begin (*>*)

text {* Finite sets can obviously be implemented by lists.  In the
following, you will be asked to implement the set operations union,
intersection and difference and to show that these implementations are
correct.  Thus, for a function *}
primrec exists ::"'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "exists x [] = False"|
"exists x (y#ys) = ((x=y) \<or>exists x ys)"


primrec  list_union :: "['a list, 'a list] \<Rightarrow> 'a list"
  where "list_union [] y = y"
  |"list_union (x#xs) y = (if x: set y then list_union xs y else x#(list_union xs y))"

text {* to be defined by you it has to be shown that *}


lemma "set (list_union xs ys) = set xs \<union> set ys"
  apply (induct xs)
  apply auto
done
  
  

text {* In addition, the functions should be space efficient in the
sense that one obtains lists without duplicates (@{text "distinct"})
whenever the parameters of the functions are duplicate-free.  Thus, for
example, *}
lemma l1:"\<lbrakk>a \<notin> set ys; a \<notin> set xs\<rbrakk> \<Longrightarrow>  a \<notin> set (list_union xs ys)"
  apply(induct xs)
   apply auto
  done
lemma [rule_format]: 
  "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))"
  apply (induct xs)
   apply (auto simp add: l1)
  done

text {* \emph{Hint:} @{text "distinct"} is defined in @{text List.thy}. *}


subsubsection {* Quantification over Sets *}

text {* Define a (non-trivial) set @{text S} such that the following
proposition holds: *}

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> (A \<union> B). P x)"
  apply auto
  done

text {* Define a (non-trivial) predicate @{text P} such that *}

lemma "\<forall> x \<in> A. Q (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
  apply auto
  done

(*<*) end (*>*)