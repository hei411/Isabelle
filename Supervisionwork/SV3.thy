(*<*) theory SV3 imports Main begin (*>*)

text {* 2000 Paper 6 Question 11 *}

lemma"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))\<longrightarrow> ( \<exists> y . \<not>P(y))"
  apply auto
  done

lemma"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))\<longrightarrow> ( \<exists> y . \<not>P(y))"
proof 
  assume condition:"(\<forall>x. (P(x) \<longleftrightarrow> (Q(x) \<and> \<not>Q(f(x)))))"
  fix a
  from condition have "(P(a) \<longleftrightarrow> (Q(a) \<and> \<not>Q(f(a))))" by simp
  from condition show result:"( \<exists> y . \<not>P(y))"
  proof cases
    assume  "\<not> P(a)"
    thus ?thesis by auto
  next 
    assume q:" \<not> \<not> P a"
    from condition have  w: "P a = (Q a \<and> \<not> Q (f a))" by simp
    from q have e:"P a" by simp
    from w e have "(Q a \<and> \<not> Q (f a))" by auto
    then have "\<not> Q (f a)" by simp
    then have t:"\<not> ( Q (f a)\<and>\<not>Q(f(f(a))))" by auto
    from condition t have y:"\<not>P(f(a))" by auto
    then show ?thesis by auto
  qed
qed
  
  
    


