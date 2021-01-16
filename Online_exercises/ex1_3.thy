
(*<*) theory ex1_3 imports Main begin (*>*)

text {* Define a universal and an existential quantifier on lists
using primitive recursion.  Expression @{term "alls P xs"} should
be true iff @{term "P x"} holds for every element @{term x} of
@{term xs}, and @{term "exs P xs"} should be true iff @{term "P x"}
holds for some element @{term x} of @{term xs}.
*}

primrec   alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where "alls f [] = True"
  |"alls f (x#xs) = (f x \<and> alls f xs)"

primrec   exs  :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where "exs f [] = False"
  |"exs f (x#xs) = (f x \<or> exs f xs)"

text {*
Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.

Use the @{text "[simp]"}-attribute only if the equation is truly a
simplification and is necessary for some later proof.
*}

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  apply (induct xs)
   apply auto
  done

lemma alls_1[simp]: "alls P (x@xs) = (alls P x \<and> (alls P xs))"
  apply (induct x)
  apply auto
  done

lemma "alls P (rev xs) = alls P xs"
  apply (induct xs)
  apply (auto)
  oops

lemma "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
  quickcheck oops


lemma "exs P (map f xs) = exs (P o f) xs"
  apply (induct xs)
   apply auto
  done

lemma exs_1 [simp]:"exs P (x @ y) = (exs P x \<or> exs P y)"
  apply (induct x)
   apply auto
  done

lemma "exs P (rev xs) = exs P xs"
  apply (induct xs)
   apply auto
  done

text {* Find a (non-trivial) term @{text Z} such that the following equation holds: *}

lemma "exs (\<lambda>x. P x \<or> Q x) xs =(exs (\<lambda>x. P x) xs  \<or> exs (\<lambda>x. Q x) xs )"
  apply (induct xs)
   apply auto
  done


text {* Express the existential via the universal quantifier --
@{text exs} should not occur on the right-hand side: *}

lemma "exs P xs = (\<not> alls (\<lambda>x. \<not> P x) xs)"
  apply(induct xs)
   apply auto
  done

text {*
Define a primitive-recursive function @{term "is_in x xs"} that
checks if @{term x} occurs in @{term xs}. Now express
@{text is_in} via @{term exs}:
*}
primrec is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where "is_in a [] = False"
  |"is_in a (x#xs) = (a=x \<or> is_in a xs)"

lemma "is_in a xs = exs (\<lambda> y. y=a) xs"
  apply(induct xs)
   apply auto
  done

text {* Define a primitive-recursive function @{term "nodups xs"}
that is true iff @{term xs} does not contain duplicates, and a
function @{term "deldups xs"} that removes all duplicates.  Note
that @{term "deldups[x,y,x]"} (where @{term x} and @{term y} are
distinct) can be either @{term "[x,y]"} or @{term "[y,x]"}.

Prove or disprove (by counterexample) the following theorems.
*}
primrec nodups::" 'a list \<Rightarrow> bool"
  where "nodups [] = True"
  |"nodups (x#xs) = (nodups xs \<and> (\<not> is_in x xs))" 
primrec deldups::" 'a list \<Rightarrow> 'a list"
  where "deldups [] = []"
  |"deldups (x#xs) = (if (is_in x xs) then deldups xs else (x# (deldups xs)))" 

lemma "length (deldups xs) <= length xs"
  apply (induct xs)
   apply auto
  done

lemma prop1[simp]:
  "(is_in a (deldups xs)) = is_in a xs"
  apply (induct xs)
   apply auto
  done

lemma "nodups (deldups xs)"
  apply(induct xs)
   apply auto
  done

lemma "deldups (rev xs) = rev (deldups xs)"
  quickcheck
  oops

(*<*) end (*>*)