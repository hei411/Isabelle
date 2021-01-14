

(*<*) theory ex1_5 imports Main begin (*>*)

text{*
Define a function @{term occurs}, such that @{term"occurs x xs"} is
the number of occurrences of the element @{term x} in the list @{term
xs}.
*}

primrec  occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"occurs x [] = 0"
|"occurs a (x#xs) = (if a=x then Suc (occurs a xs) else occurs a xs)"


text {*
Prove (or let Isabelle disprove) the lemmas that follow. You may have
to prove additional lemmas first.  Use the @{text "[simp]"}-attribute
only if the equation is truly a simplification and is necessary for
some later proof.
*}
lemma occur_1 :"occurs a (a#xs) =Suc (occurs a xs) "
  apply (induct xs)
   apply auto
  done

lemma "occurs a xs = occurs a (rev xs)"
  apply (induct xs)
   apply (auto simp add:occur_1)
  oops

lemma "occurs a xs <= length xs"
  apply(induct xs)
   apply auto
  done


text{* Function @{text map} applies a function to all elements of a list:
@{text"map f [x\<^isub>1,\<dots>,x\<^isub>n] = [f x\<^isub>1,\<dots>,f x\<^isub>n]"}. *}
primrec map ::"('a\<Rightarrow>'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"map f [] = []"
|"map f (x#xs) = (f x) # map f xs" 


lemma "occurs a (map f xs) = occurs (f a) xs"
  quickcheck
(*<*)oops(*>*)

text{*
Function @{text"filter :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"} is defined
by @{thm[display]filter.simps[no_vars]} Find an expression @{text e}
not containing @{text filter} such that the following becomes a true
lemma, and prove it:
*}

lemma "occurs a (filter P xs) = (if P a then occurs a xs else 0)"
  apply (induct xs)
   apply auto
done


text{*
With the help of @{term occurs}, define a function @{term remDups}
that removes all duplicates from a list.
*}

primrec remDups :: "'a list \<Rightarrow> 'a list" where
"remDups [] = []"
|" remDups (x#xs) = (if occurs x xs =0 then ( x# (remDups xs) )else remDups xs)" 


text{*
Find an expression @{text e} not containing @{text remDups} such that
the following becomes a true lemma, and prove it:
*}


lemma "occurs x (remDups xs) = (if (occurs x xs) =0 then 0 else 1)"
  apply (induct xs)
   apply auto
  oops


text{*
With the help of @{term occurs} define a function @{term unique}, such
that @{term "unique xs"} is true iff every element in @{term xs}
occurs only once.
*}

primrec unique :: "'a list \<Rightarrow> bool"
  where "unique [] = True" 
  |"unique (x#xs) = (if occurs x xs \<noteq>0 then False else unique xs)"


text{* Show that the result of @{term remDups} is @{term unique}. *}

lemma remDups_1: " occurs x (remDups xs) = min 1 (occurs x xs)"
  apply (induct xs)
   apply auto
  done

lemma "unique (remDups xs)"
  apply (induct xs)
   apply (auto simp add: remDups_1)
  oops

(*<*) end (*>*)