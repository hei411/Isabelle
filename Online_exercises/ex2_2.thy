
(*<*) theory ex2_2 imports Main begin (*>*)

subsubsection {* Some more list functions *}

text {* Recall the summation function *}

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

text {* In the Isabelle library, you will find (in the theory {\tt List.thy})
the functions @{text foldr} and @{text foldl}, which allow you to define some
list functions, among them @{text sum} and @{text length}.  Show the following:
*}

lemma sum_foldr: "sum xs = foldr (+) xs 0"
  apply (induct xs)
   apply auto
  done

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  apply(induct xs)
   apply auto
  done


text {* Repeated application of @{text foldr} and @{text map} has the
disadvantage that a list is traversed several times.  A single traversal is
sufficient, as illustrated by the following example: *}

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda> x res. x+res+3) xs 0"
  apply(induct xs)
   apply auto
done

text {* Find terms @{text h} and @{text b} which solve this equation. *}


text {* Generalize this result, i.e.\ show for appropriate @{text h} and @{text
b}: *}

lemma "foldr g (map f xs) a = foldr (\<lambda> x res. g (f x) res) xs a"
  apply(induct xs)
   apply auto
  done

text {* Hint: Isabelle can help you find the solution if you use the equalities
arising during a proof attempt. *}


text {* The following function @{text rev_acc} reverses a list in linear time:
*}

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

text {* Show that @{text rev_acc} can be defined by means of @{text foldl}. *}

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  apply(induct xs arbitrary:a)
   apply auto
  done


text {* Prove the following distributivity property for @{text sum}: *}

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply(induct xs arbitrary:ys)
   apply auto
  done


text {* Prove a similar property for @{text foldr}, i.e.\ something like @{text
"foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"}.  However, you will
have to strengthen the premises by taking into account algebraic properties of
@{text f} and @{text a}. *}

definition
  left_neutral :: "['a \<Rightarrow> 'b \<Rightarrow> 'b, 'a] \<Rightarrow> bool" where
  "left_neutral f a == (\<forall> x. (f a x = x))"

definition
  assoc :: "['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> bool" where
  "assoc f == (\<forall> x y z. f (f x y) z = f x (f y z))" 
lemma foldr_append: "\<lbrakk>  left_neutral f a; assoc f \<rbrakk> \<Longrightarrow> foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
  apply(induct xs arbitrary:ys)
    apply (simp add: left_neutral_def)
  apply (simp add: assoc_def)
  done


text {* Now, define the function @{text prod}, which computes the product of
all list elements *}

definition  prod :: "nat list \<Rightarrow> nat" where
"prod xs == foldr (*) xs 1"


text {* directly with the aid of a fold and prove the following: *}

lemma "prod (xs @ ys) = prod xs * prod ys"
 apply (simp only: prod_def)
  apply (rule foldr_append)
   apply (simp add:left_neutral_def )
  apply (simp add:assoc_def )
  done


subsubsection {* Functions on Trees *}

text {* Consider the following type of binary trees: *}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text {* Define functions which convert a tree into a list by traversing it in
pre-, resp.\ postorder: *}

(*<*) consts (*>*)
primrec  preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder Tip = []"
|"preorder (Node a b c) = b#(preorder a)@(preorder c)"

primrec  postorder :: "'a tree \<Rightarrow> 'a list" where
"postorder Tip = []"
|"postorder (Node a b c) = (postorder a)@(postorder c)@[b]"



text {* You have certainly realized that computation of postorder traversal can
be efficiently realized with an accumulator, in analogy to @{text rev_acc}: *}

primrec
  postorder_acc :: "['a tree, 'a list] \<Rightarrow> 'a list" where
"postorder_acc Tip x = x"
|"postorder_acc (Node a b c) x = (postorder_acc a (postorder_acc c (b#x)))"



text {* Define this function and show: *}

lemma "postorder_acc t xs = (postorder t) @ xs"
  apply(induct t arbitrary: xs)
   apply auto
  done


text {* @{text postorder_acc} is the instance of a function @{text foldl_tree},
which is similar to @{text foldl}. *}

primrec  foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b" where
"foldl_tree f a Tip =a"
|"foldl_tree f acc (Node a b c) = foldl_tree f  (foldl_tree f (f acc b) c)   a"


text {* Show the following: *}

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
  apply(induct t)
   apply auto

  done


text {* Define a function @{text tree_sum} that computes the sum of the
elements of a tree of natural numbers: *}

primrec
  tree_sum :: "nat tree \<Rightarrow> nat" where
"tree_sum Tip = 0"
|"tree_sum (Node a b c) = b +(tree_sum a) + (tree_sum c)"  


text {* and show that this function satisfies *}

lemma "tree_sum t = sum (preorder t)"
  apply(induct t)
   apply auto
  done


(*<*) end (*>*)