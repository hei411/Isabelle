 (*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
*)


(*<*) theory ex1_2 imports Main begin (*>*)

text{*
Define a function @{term replace}, such that @{term"replace x y zs"}
yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.
*}

fun  replace :: "'a => 'a => 'a list => 'a list" where
"replace x y [] = []"
|" replace x y (Cons a as) = (if a = x then y # replace x y as else a # replace x y as)"

text {*
Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.
*}
lemma extend_1: "replace x y (z@[x]) = (replace x y z) @ [y]"
  apply (induct z)
   apply auto
  done

lemma extend_2: "a \<noteq> x \<longrightarrow> replace x y (z@[a]) = (replace x y z)@[a]"
  apply (induct z)
  apply auto
  done

theorem "rev(replace x y zs) = replace x y (rev zs)"
  apply (induct zs)
   apply (auto simp add: extend_1 extend_2)
  done

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  quickcheck
  oops

theorem "replace y z (replace x y zs) = replace x z zs"
  quickcheck
  oops

text{* Define two functions for removing elements from a list:
@{term"del1 x xs"} deletes the first occurrence (from the left) of
@{term x} in @{term xs}, @{term"delall x xs"} all of them. *}

fun del1   :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "del1 a [] = []"
  | "del1 a (x#y) = (if a \<noteq> x then x#del1 a y else y)"

fun delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "delall a []= []"
  |"delall a (x#y) = (if a \<noteq> x then x#delall a y else delall a y)"

text {*
Prove or disprove (by counterexample) the following theorems.
*}

theorem "del1 x (delall x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

theorem "delall x (delall x xs) = delall x xs"
  apply (induct xs)
  apply auto
  done


theorem "delall x (del1 x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  apply (induct zs)
  apply auto
  done

lemma del_1:"  del1 x (delall x zs)=delall x zs "
  apply (induct zs)
  apply auto
  done

lemma del_2: "delall x (del1 x zs) = del1 x (delall x zs)"
  apply (induct zs)
   apply (auto simp add:del_1)
  done

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  apply (induct zs)
   apply (auto simp add: del_1)
  done

theorem "delall x (delall y zs) = delall y (delall x zs)"
 apply (induct zs)
  apply auto
  done

theorem "del1 y (replace x y xs) = del1 x xs"
  quickcheck
  oops

theorem "delall y (replace x y xs) = delall x xs"
  quickcheck
  oops

theorem "replace x y (delall x zs) = delall x zs"
  apply (induct zs)
   apply auto
  done

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
  quickcheck
  oops

theorem "rev(del1 x xs) = del1 x (rev xs)"
  quickcheck
  oops

lemma rev_del_1 : " delall x( y @ [x]) = delall x y "
  apply(induct y)
   apply auto
  done

lemma rev_del_2: "x  \<noteq>a  \<longrightarrow>  delall x y@ [a] = delall x (y @ [a])"
  apply(induct y)
   apply auto
  done


theorem "rev(delall x xs) = delall x (rev xs)"
  apply(induct xs)
   apply (auto simp add:rev_del_1 rev_del_2)
  oops

(*<*)
end
(*>*)