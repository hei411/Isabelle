

(*<*) theory ex1_6 imports Main begin (*>*)

text{* Define a function @{text sum}, which computes the sum of
elements of a list of natural numbers. *}

primrec  sum :: "nat list \<Rightarrow> nat" where
"sum [] =0"
|"sum (x#xs) = x + sum xs" 


text{* Then, define a function @{text flatten} which flattens a list
of lists by appending the member lists. *}


primrec  flatten :: "'a list list \<Rightarrow> 'a list" where
"flatten [] = []"
|" flatten (x#xs) = x@ (flatten xs)"


text{* Test your functions by applying them to the following example lists: *}

lemma "sum [2::nat, 4, 8] = 14"
  apply auto
  done

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = [2,3,4,5,7,9]"
  apply auto
  done


text{* Prove the following statements, or give a counterexample: *}

lemma "length (flatten xs) = sum (map length xs)"
  apply (induct xs)
   apply auto
  done

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
   apply auto
  done

lemma flatten_append[simp]: "flatten (xs @ ys) = flatten xs @ flatten ys"
  apply (induct xs)
  apply auto
  done

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
  apply (induct xs)
   apply (auto )

  oops

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
  apply(induct xs)
   apply auto
  done

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
  apply (induct xs)
   apply auto
  done

lemma "flatten (rev xs) = flatten xs"
  quickcheck oops

lemma [simp] :"sum (x@xs) = sum x + sum xs"
  apply (induct x)
   apply auto
  done
lemma "sum (rev xs) = sum xs"
  apply (induct xs)
   apply auto
  done

text{* Find a (non-trivial) predicate @{text P} which satisfies *}

lemma "list_all (\<lambda>x. 0<x) xs \<longrightarrow> length xs \<le> sum xs"
  apply(induct xs)
   apply auto
  done


text{* Define, by means of primitive recursion, a function @{text
list_exists} which checks whether an element satisfying a given property
is contained in the list: *}

primrec
  list_exists :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)" where
"list_exists f [] = False"
|"list_exists f (x#xs) = (f x \<or> list_exists f xs)"  


text{* Test your function on the following examples: *}

lemma "list_exists (\<lambda> n. n < 3) [4::nat, 3, 7] = False"
  apply auto
done

lemma "list_exists (\<lambda> n. n < 4) [4::nat, 3, 7] = True"
  apply auto done


text{* Prove the following statements: *}

lemma list_exists_append[simp]: 
  "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)"
  apply (induct xs)
   apply auto
  done

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
  apply (induct xs)
   apply auto
  done

text{* You could have defined @{text list_exists} only with the aid of
@{text list_all}.  Do this now, i.e. define a function @{text
list_exists2} and show that it is equivalent to @{text list_exists}. *}

fun list_exists2 :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)" where
"list_exists2 f xs =(\<not> ((list_all (\<lambda>x. \<not>(f x)) xs )))"

lemma "list_exists2 f xs = list_exists f xs"
  apply (induct xs)
   apply auto
  done


(*<*) end (*>*)