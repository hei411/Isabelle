theory lec8 imports Main begin 

text {*
  Proving two examples from Logic and Proof lecture 8
*}

lemma " \<forall>x.\<exists>y. \<not>(P(y,x) \<longleftrightarrow> \<not>P(y,y))" 
  apply(rule allI)
  apply(rule exI)
  apply(rule notI)
  apply(erule iffE)
  apply (erule impE)
   apply (rule classical)
   apply (erule mp)
   apply assumption
  apply (erule impE)
   apply assumption
  apply(erule notE)
  apply assumption
  done
  

  done
lemma "(((\<exists>x. P \<longrightarrow> Q x) \<and> ((\<exists>x. Q x \<longrightarrow> P)) \<longrightarrow> ( \<exists>x. (P = Q x)))) " 
  apply(rule impI)
  apply(erule conjE)
  apply(erule exE)+
  apply blast
  done
  
  
  
   
  
