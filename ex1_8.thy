
(*<*) theory ex1_8 imports Main begin (*>*)

text {*
\begin{description}
\item[\bf (a)] Define a primitive recursive function @{term ListSum} that
computes the sum of all elements of a list of natural numbers.

Prove the following equations.  Note that @{term  "[0..n]"} und @{term
"replicate n a"} are already defined in a theory {\tt List.thy}.
\end{description}
*}

primrec ListSum :: "nat list \<Rightarrow> nat" where
"ListSum [] =0"
|"ListSum (x#xs) = x + (ListSum xs)" 
lemma [simp]:"ListSum (a@b) = ListSum a + ListSum b"
  apply (induct a)
   apply auto
  done

theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
  apply (induct n)
   apply auto
  done

theorem "ListSum (replicate n a) = n * a" 
  apply (induct n)
   apply auto
  done


text {* 
\begin{description}
\item[\bf (b)] Define an equivalent function @{term ListSumT} using a
tail-recursive function @{term ListSumTAux}.  Prove that @{term ListSum}
and @{term ListSumT} are in fact equivalent.
\end{description}
*}

fun  ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"ListSumTAux [] now = now"|"ListSumTAux (x#xs) now = ListSumTAux xs (now+x)" 

fun ListSumT :: "nat list \<Rightarrow> nat" where
"ListSumT x = ListSumTAux x 0" 


lemma [simp]:" \<forall>a. ListSumTAux xs a = a+ListSum xs"
  apply (induct xs)
   apply auto
  done

theorem " ListSumT xs=ListSum xs " 
  apply(induct xs)
   apply (auto )
  done

(*<*) end (*>*)