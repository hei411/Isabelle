(*<*) theory SV3 imports Main begin (*>*)

text {* 2000 Paper 6 Question 11 *}

lemma"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))\<longrightarrow> ( \<exists> y . \<not>P(y))"
  apply auto
  done

lemma"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))\<longrightarrow> ( \<exists> y . \<not>P(y))"
proof (rule impI)
  fix a
  assume condition:"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))"
  then have "(P(a) \<longleftrightarrow> (Q(a) \<and> \<not>Q(f(a))))" by simp
  from condition have "\<exists> y . \<not>P(y)"
  proof cases
    assume  "\<not> P(a)"
    then show ?thesis by auto
  next 
    assume q:" \<not> \<not> P a"
    assume w: "P a = (Q a \<and> \<not> Q (f a))"
    from q have e:"P a" by simp
    from w e have "(Q a \<and> \<not> Q (f a))" by auto
    then have "\<not> Q (f a)" by simp
    then have t:"\<not> ( Q (f a)\<and>\<not>Q(f(f(a))))" by auto
    from condition t have y:"\<not>P(f(a))" by auto
    finally show ?thesis
  qed
  oops
    


