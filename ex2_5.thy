
(*<*) theory ex2_5 imports Main begin (*>*)

text {*
Let the following data type for propositional formulae be given:
*}

datatype form = T | Var nat | And form form | Xor form form

text {*
Here @{term "T"} denotes a formula that is always true, @{term "Var n"} denotes
a propositional variable, its name given by a natural number, @{term "And f1
f2"} denotes the AND combination, and @{term "Xor f1 f2"} the XOR (exclusive or)
combination of two formulae.  A constructor @{term "F"} for a formula that is
always false is not necessary, since @{term "F"} can be expressed by @{term "Xor
T T"}.

{\bf Exercise 1:} Define a function
*}
definition
xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor x y \<equiv> (x \<and> \<not> y) \<or> (\<not> x \<and> y)"
primrec  evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
"evalf f T=True"
|"evalf f (Var n) = f n"
|"evalf f (And e1 e2) = ((evalf f e1)\<and>(evalf f e2))"
|"evalf f (Xor e1 e2) = (xor (evalf f e1)  (evalf f e2))" 

text {*
that evaluates a formula under a given variable assignment.
*}


text {*
Propositional formulae can be represented by so-called {\it polynomials}.  A
polynomial is a list of lists of propositional variables, i.e.\ an element of
type @{typ "nat list list"}.  The inner lists (the so-called {\it monomials})
are interpreted as conjunctive combination of variables, whereas the outer list
is interpreted as exclusive-or combination of the inner lists.

{\bf Exercise 2:} Define two functions
*}

(*<*)(*>*)
primrec  evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where
"evalm f [] = True"
|"evalm f (x#xs) = ((f x)\<and>evalm f xs)"

primrec  evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool" where
"evalp f [] = False"
|"evalp f (x#xs) = (xor (evalm f x)  (evalp f xs))" 

text {*
for evaluation of monomials and polynomials under a given variable assignment.
In particular think about how empty lists have to be evaluated.
*}


text {*
{\bf Exercise 3:} Define a function
*}
(*<*)primrec(*>*)  mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
"mulpp [] y = []"
|"mulpp (x#xs) y = map (\<lambda>z. x@z) y @ (mulpp xs y)"
(*<*)primrec(*>*)  poly :: "form \<Rightarrow> nat list list" where
"poly T = [[]]"
|"poly (Var n) = [[n]]"
|"poly (And a b) = mulpp (poly a) (poly b)" 
|"poly (Xor a b) = (poly a )@(poly b)" 

text {*
that turns a formula into a polynomial.  You will need an auxiliary function
*}


text {*
to ``multiply'' two polynomials, i.e.\ to compute
\[
((v^1_1 \mathbin{\odot} \cdots \mathbin{\odot} v^1_{m_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (v^k_1 \mathbin{\odot} \cdots \mathbin{\odot} v^k_{m_k})) \mathbin{\odot}
((w^1_1 \mathbin{\odot} \cdots \mathbin{\odot} w^1_{n_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (w^l_1 \mathbin{\odot} \cdots \mathbin{\odot} w^l_{n_l}))
\]
where $\mathbin{\oplus}$ denotes ``exclusive or'', and $\mathbin{\odot}$ denotes
``and''.  This is done using the usual calculation rules for addition and
multiplication.
*}


text {*
{\bf Exercise 4:} Now show correctness of your function @{term "poly"}:
*}

lemma evalm_app: "evalm e (xs @ ys) = (evalm e xs \<and> evalm e ys)"
apply (induct xs)
apply auto
  done


lemma evalp_app: "evalp e (xs @ ys) = ( xor (evalp e xs) (evalp e ys))"
apply (induct xs)
   apply (auto simp add:xor_def)
  done

theorem mulmp_correct: "evalp e (map (\<lambda>z. m@z) p) = (evalm e m \<and> evalp e p)"
apply (induct p)
apply (auto simp add:  evalm_app xor_def)
  done

theorem mulpp_correct: "evalp e (mulpp p q) = (evalp e p \<and> evalp e q)"
  apply (induct p )
apply (auto simp add:xor_def  mulmp_correct evalp_app )
  done

theorem poly_correct: "evalf e f = evalp e (poly f)"
  apply (induct f)
     apply (auto simp add:xor_def mulpp_correct evalp_app)
  done

text {*
It is useful to prove a similar correctness theorem for @{term "mulpp"} first.
*}


(*<*) end (*>*)