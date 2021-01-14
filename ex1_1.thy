(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
*)


(*<*) theory ex1_1 imports Main begin (*>*)

text {*
Define a primitive recursive function @{text snoc} that appends an element
at the \emph{right} end of a list. Do not use @{text"@"} itself.
*}

fun  snoc :: "'a list => 'a => 'a list" where
"snoc Nil x = Cons x Nil"
|"snoc (Cons a b) c = Cons a (snoc b c)" 

text {*
Prove the following theorem:
*}
lemma [simp]: "x @ [y,z] = snoc (x @ [y]) z"
  apply (induct x)
   apply auto
  done

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  apply (induct xs)
  apply auto
done

text {*
Hint: you need to prove a suitable lemma first.
*}

(*<*) end (*>*)