(*
    $Id: ex.thy,v 1.3 2005/06/29 07:38:01 kleing Exp $
    Author: Tobias Nipkow
*)


(*<*) theory ex3_1 imports Main begin (*>*)

subsubsection {* Power *}

text {* Define a primitive recursive function $pow~x~n$ that
computes $x^n$ on natural numbers. *}


fun  pow :: "nat => nat => nat" where
"pow x 0 = Suc 0"
|"pow x y = x * pow x (y-1)"


text {* Prove the well known equation $x^{m \cdot n} = (x^m)^n$: *}

lemma pow_1: " pow x (y+z) = pow x y * pow x z " 
  apply( induct z)
   apply auto
  done

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  apply (induct n)
   apply (auto simp add: pow_1)
  done
 

text {* Hint: prove a suitable lemma first.  If you need to appeal to
associativity and commutativity of multiplication: the corresponding
simplification rules are named @{text mult_ac}. *}


subsubsection {* Summation *}

text {* Define a (primitive recursive) function $sum~ns$ that sums a list
of natural numbers: $sum [n_1, \dots, n_k] = n_1 + \cdots + n_k$. *}


fun  sum :: "nat list => nat" where
"sum [] = 0"
| "sum (x#xs) = x + sum xs"


text {* Show that $sum$ is compatible with $rev$. You may need a lemma. *}

lemma sum_1:" sum (x@[y]) =sum x + y "
  apply (induct x)
   apply auto
  done


theorem sum_rev: "sum (rev ns) = sum ns"
  apply (induct ns)
   apply (auto simp add:sum_1)
  done


text {* Define a function $Sum~f~k$ that sums $f$ from $0$ up to $k-1$:
$Sum~f~k = f~0 + \cdots + f(k - 1)$. *}


fun  Sum :: "(nat => nat) => nat => nat" where
"Sum f 0 = 0"
| "Sum f (Suc(k)) = f k + Sum f k"


text {* Show the following equations for the pointwise summation of functions.
Determine first what the expression @{text whatever} should be. *}

theorem "Sum (%i. f i + g i) k = Sum f k + Sum g k"
  apply (induct k)
   apply auto
  done

theorem "Sum f (k + l) = Sum f k + Sum (%i. f(k+i)) l"
  apply (induct l)
   apply auto
  done


text {* What is the relationship between @{term sum} and @{text Sum}?
Prove the following equation, suitably instantiated. *}

theorem "Sum f k = sum (map f [0..<k])"
  apply (induct k)
   apply (auto simp add:sum_1)
  oops

text {* Hint: familiarize yourself with the predefined functions @{term map}
and @{text"[i..<j]"} on lists in theory List. *}


(*<*) end (*>*)