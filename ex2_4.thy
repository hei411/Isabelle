

(*<*) theory ex2_4 imports Main begin (*>*)

text {*
Boolean functions (in finitely many variables) can be represented by so-called
{\it binary decision diagrams} (BDDs), which are given by the following data
type:
*}

datatype bdd = Leaf bool | Branch bdd bdd



primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool"
  where "eval f i (Leaf b) = b"
  |"eval f i (Branch x y) = (if (f i) then (eval f (Suc i) y) else ( eval f (Suc i ) x))"


text {*
that evaluates a BDD under a given variable assignment, beginning at a variable
with a given index.
*}


text {*
{\bf Exercise 2:} Define two functions
*}

primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd" where
  "bdd_unop f (Leaf x) = Leaf (f x)"
| "bdd_unop f (Branch b1 b2) = Branch (bdd_unop f b1) (bdd_unop f b2)"

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
  "bdd_binop f (Leaf x) b = bdd_unop (f x) b"
| "bdd_binop f (Branch b1 b2) b = (case b of
       Leaf x \<Rightarrow> Branch (bdd_binop f b1 (Leaf x)) (bdd_binop f b2 (Leaf x))
     | Branch b1' b2' \<Rightarrow> Branch (bdd_binop f b1 b1') (bdd_binop f b2 b2'))"

text {*
for the application of unary and binary operators to BDDs, and prove their
correctness.
*}
theorem bdd_unop_correct:
  "\<forall>i. eval e i (bdd_unop f b) = f (eval e i b)"
  apply (induct b)
   apply auto
  done
theorem bdd_binop_correct:
  "\<forall>i b2. eval e i (bdd_binop f b1 b2) = f (eval e i b1) (eval e i b2)"
  apply (induct b1 )
   apply (auto simp add :bdd_unop_correct)
     apply (case_tac b2)
      apply auto
 apply (case_tac b2)
     apply auto 
   apply (case_tac b2)
    apply auto 
  apply (case_tac b2)
  apply auto
  done

text {*
Now use @{term "bdd_unop"} and @{term "bdd_binop"} to define
*}

fun
  bdd_and :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd" where 
"bdd_and x y = (bdd_binop (\<lambda> x y. x\<and>y) x y)" 
fun  bdd_or :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"where 
"bdd_or x y = (bdd_binop (\<lambda> x y. x\<or>y) x y)" 
fun  bdd_not :: "bdd \<Rightarrow> bdd"where 
"bdd_not x  = (bdd_unop (\<lambda> x . (\<not>x)) x )" 
fun  bdd_xor :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"where 
"bdd_xor x y = (bdd_or (bdd_and (bdd_not x) y) (bdd_and x (bdd_not y)))"

text {*
and show correctness.
*}
theorem bdd_and_correct:
  "eval e i (bdd_and b1 b2) = (eval e i b1 \<and> eval e i b2)"
  apply (auto simp add:  bdd_binop_correct)
  done
 theorem bdd_or_correct:
  "eval e i (bdd_or b1 b2) = (eval e i b1 \<or> eval e i b2)"
  apply (auto simp add:  bdd_binop_correct)
  done
  theorem bdd_not_correct:
  "eval e i (bdd_not b) = (\<not>(eval e i b))"
  apply (auto simp add:  bdd_unop_correct)
  done

text {*
Finally, define a function
*}



text {*
to create a BDD that evaluates to @{term "True"} if and only if the variable
with the given index evaluates to @{term "True"}.  Again prove a suitable
correctness theorem.

{\bf Hint:} If a lemma cannot be proven by induction because in the inductive
step a different value is used for a (non-induction) variable than in the
induction hypothesis, it may be necessary to strengthen the lemma by universal
quantification over that variable (cf.\ Section 3.2 in the Tutorial on
Isabelle/HOL).
*}

text_raw {* \begin{minipage}[t]{0.45\textwidth} *}
 
text{*
{\bf Example:} instead of
*}

lemma "P (b::bdd) x" 
apply (induct b) (*<*) oops (*>*)

text_raw {* \end{minipage} *}
text_raw {* \begin{minipage}[t]{0.45\textwidth} *}   

text {* Strengthening: *}

lemma "\<forall>x. P (b::bdd) x"
apply (induct b) (*<*) oops (*>*)  

text_raw {* \end{minipage} \\[0.5cm]*} 
primrec bdd_var :: "nat \<Rightarrow> bdd" where
  "bdd_var 0 = Branch (Leaf False) (Leaf True)"
| "bdd_var (Suc i) = Branch (bdd_var i) (bdd_var i)"

theorem bdd_var_correct: "\<forall>j. eval e j (bdd_var i) = e (i+j)"
  apply (induct i)
  apply auto
done

text {*
{\bf Exercise 3:} Recall the following data type of propositional formulae
(cf.\ the exercise on ``Representation of Propositional Formulae by
Polynomials'')
*}

datatype form = T | Var nat | And form form | Xor form form

text {*
together with the evaluation function @{text "evalf"}:
*}

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<equiv>  (x \<and> \<not> y) \<or> (\<not> x \<and> y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
  "evalf e T = True"
| "evalf e (Var i) = e i"
| "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"
| "evalf e (Xor f1 f2) = xor (evalf e f1) (evalf e f2)"

text {*
Define a function
*}

primrec  mk_bdd :: "form \<Rightarrow> bdd" where
"mk_bdd T = (Leaf True)"
|"mk_bdd (Var i) = (bdd_var i)"
|"mk_bdd (And f1 f2) = bdd_and (mk_bdd f1) (mk_bdd f2)" 
|"mk_bdd(Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)" 

text {*
that transforms a propositional formula of type @{typ "form"} into a BDD.
Prove the correctness theorem
*}

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
  apply (induct f)
 apply (auto simp add: bdd_var_correct
    bdd_and_correct bdd_or_correct bdd_not_correct  xor_def)
       oops


(*<*) end (*>*)