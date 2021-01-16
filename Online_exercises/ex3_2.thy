

(*<*) theory ex3_2 imports Main begin (*>*)

text{*
A book about Vedic mathematics describes three methods to make the calculation of squares of natural numbers easier:

\begin{itemize}
\item {\em MM1}: Numbers whose predecessors have squares that are known or can easily be calculated. For example:
\\ Needed: $61^2$  
\\ Given: $60^2 = 3600$
\\ Observe: $61^2 = 3600 + 60 + 61 = 3721$

\item {\em MM2}: Numbers greater than, but near 100. For example:
\\ Needed: $102^2$
\\ Let $h = 102 - 100 = 2$ , $h^2 = 4$
\\ Observe: $102^2 = (102+h)$ shifted two places to the left $ + h^2 = 10404$
 
\item {\em MM3}: Numbers ending in $5$. For example:
\\ Needed: $85^2$
\\ Observe: $85^2 = (8 * 9)$ appended to $ 25 = 7225$
\\ Needed: $995^2$
\\ Observe: $995^2 = (99 * 100)$ appended to $ 25 = 990025 $
\end{itemize}

In this exercise we will show that these methods are not so magical after all!

\begin{itemize}
\item Based on {\em MM1} define a function @{term "sq"} that calculates the square of a natural number.

\item Prove the correctness of @{term "sq"} (i.e.\ @{term "sq n = n * n"}).
\item Formulate and prove the correctness of {\em MM2}.\\ Hints:
  \begin{itemize}
  \item Generalise {\em MM2} for an arbitrary constant (instead of $100$).
  \item Universally quantify all variables other than the induction variable.
  \end{itemize}
\item Formulate and prove the correctness of {\em MM3}.\\ Hints:
  \begin{itemize}
  \item Try to formulate the property `numbers ending in $5$' such that it is easy to get to the rest of the number.
  \item Proving the binomial formula for $(a+b)^2$ can be of some help.
  \end{itemize}
\end{itemize}
*}
fun sq ::"nat \<Rightarrow> nat" where
"sq 0 =0"
|"sq x = sq(x-1) +x-1 +x"

lemma [simp]:"sq x =x*x"
  apply (induct x)
   apply auto
  done

lemma aux[rule_format]: "!m. m <= n \<longrightarrow> sq n = ((n + (n-m))* m) + sq (n-m)"
  apply (induct_tac n, auto)
  apply (case_tac m, auto)
done

lemma "\<forall>y.(y<x \<longrightarrow> (sq x  = ((x+(x-y))*y)+sq (x-y)))"
  apply (induct_tac x )
   apply auto
  apply(case_tac y)
   apply auto
  done
lemma [simp]:"(sq (a+b) = sq a + sq b + 2*a*b)" 
  apply(induct b)
   apply auto
  done

lemma [simp]:"(sq (a*b) = (sq a) * (sq b) )" 

  by (simp add: add_mult_distrib2 mult.commute)



lemma "sq((a*10)+5) =a*(a+1)*100+ 25"

  by (simp add: add_mult_distrib2 mult.commute)


  

(*<*) end (*>*)