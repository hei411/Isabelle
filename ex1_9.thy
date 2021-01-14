

(*<*) theory ex1_9 imports Main begin (*>*)

text {*
Read the chapter about total recursive functions in the ``Tutorial on
Isabelle/HOL'' (@{text fun}, Chapter 3.5).
*}

text {*
In this exercise you will define a function @{text Zip} that merges two lists
by interleaving.
 Examples:
@{text "Zip [a1, a2, a3]  [b1, b2, b3] = [a1, b1, a2, b2, a3, b3]"} 
 and
@{text "Zip [a1] [b1, b2, b3] = [a1, b1, b2, b3]"}.

Use three different approaches to define @{text Zip}:
\begin{enumerate}
\item by primitive recursion on the first list,
\item by primitive recursion on the second list,
\item by total recursion (using @{text fun}).
\end{enumerate}
*}

primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "zip1 [] x =x"
  |"zip1 (x#xs) ys = (case ys of [] \<Rightarrow> x#xs | y#ys \<Rightarrow> (x#y#(zip1 xs ys)))" 
primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where " zip2 x [] = x"
  | "zip2 x (y#ys) = (case x of [] \<Rightarrow> y#ys|x#xs \<Rightarrow>(x#y#(zip2 xs ys)))" 
fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zipr [] ys = ys"
| "zipr xs [] = xs"
| "zipr (x#xs) (y#ys) = x # y # zipr xs ys"

text {*
Show that all three versions of @{text Zip} are equivalent.
*}
lemma "zip1 x y = zip2 x y"
  apply(induct x arbitrary :y)
   apply (case_tac y)
    apply auto
  apply(case_tac y)
   apply auto
  done

lemma "zip1 x y = zipr x y"
  apply (induct x arbitrary:y)
  apply (case_tac y)
    apply auto
  apply (case_tac y)
   apply auto
  done

lemma "zip2 x y = zipr x y"
  apply (induct x arbitrary:y)
  apply (case_tac y)
    apply auto
  apply (case_tac y)
   apply auto
  done


text {*
Show that @{text zipr} distributes over @{text append}.
*}

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> 
  zipr (p@q) (u@v) = zipr p u @ zipr q v"
  apply(induct p arbitrary:q u v)
   apply auto
  apply(case_tac u)
   apply auto
  done
 


text {*
{\bf Note:} For @{text fun}, the order of your equations is relevant.
If equations overlap, they will be disambiguated before they are added
to the logic.  You can have a look at these equations using @{text
"thm zipr.simps"}.
*}

(*<*) end (*>*)