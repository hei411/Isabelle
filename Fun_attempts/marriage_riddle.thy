
(*<*) theory marriage_riddle imports Main begin (*>*)

text {*
  Prove the following statement

  {\it Jack is looking at Anne, but Anne is looking at George.\\
   Jack is married, but George is not. \\
   Is a married person looking at an unmarried person? \\
   if he sits down, everyone else is sitting down}
*}

theorem
  "\<exists>j a g. looking (j, a) \<and> looking (a, g)\<and>(married j) \<and> (\<not>married g) \<Longrightarrow>  \<exists>x y. married x \<and> (\<not>married y) \<and>looking(x,y)"
proof -
  assume assmpt:"\<exists>j a g. looking (j, a) \<and> looking (a, g)\<and>(married j) \<and> (\<not>married g)" 
  then obtain j a g where t:"looking (j, a) \<and> looking (a, g)\<and>(married j) \<and> (\<not>married g)" by auto
  show ?thesis 
  proof cases
  assume anne_married:"married a" 
  with t have "married a \<and> (\<not>married g) \<and>looking(a,g)" by simp
  then have con:"\<exists>x y. married x \<and> (\<not>married y) \<and>looking(x,y)" by auto
  then show ?thesis by auto
next
  assume anne_married:"\<not>(married a)" 
  with t have "married j \<and> (\<not>married a) \<and>looking(j,a)" by simp
  then have con:"\<exists>x y. married x \<and> (\<not>married y) \<and>looking(x,y)" by auto
  then show ?thesis by auto
qed
qed


