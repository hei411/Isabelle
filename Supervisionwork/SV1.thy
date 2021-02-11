(*<*) theory SV1 imports Main begin (*>*)

text {* 2001 Paper 5 Question 11 part b *}

lemma "(P\<and>(Q\<longrightarrow>R))\<longrightarrow>S=(\<not>P\<or>\<not>Q\<or>S)\<and>(\<not>P\<or>\<not>R\<or>S)" 
  quickcheck
  oops

lemma "((P\<longrightarrow>Q)\<longrightarrow>(Q\<longrightarrow>P)) \<longleftrightarrow> (Q\<longrightarrow>P)"
  apply (rule iffI)
   apply (rule impI)
   apply(erule impE)
    apply(rule impI)
    apply assumption
   apply(erule impE)
    apply assumption+
  apply (rule impI)+
  apply(erule impE)
   apply assumption+
  done

lemma "(\<forall>x y. P x\<or> \<not>P y) \<longleftrightarrow> (\<forall>x y. (P x \<longleftrightarrow> P y))"
  apply (rule iffI)
   apply(rule allI)+
   apply(rule iffI)
    apply(rule classical)
    apply (erule allE)+
    apply (erule disjE)
     apply assumption
    apply (erule notE)+
    apply assumption
   apply(rule classical)
   apply (erule allE)+
    apply (erule disjE)
     apply assumption
    apply (erule notE)+
   apply assumption
  apply(rule allI)+
  apply (rule classical)
  apply (rule disjI1)
  apply (erule allE)+
  apply(erule notE)
  apply (erule iffE)
  apply(rule classical)
  apply(erule impE)
   apply (erule notE)
   apply(rule classical)
   apply(rule disjI1)
   apply (erule impE)
    apply (rule classical)
    apply(erule notE)
  apply(rule disjI2)
    apply assumption+
  apply(rule disjI1)
  apply (erule impE)
  apply assumption+
  done

  


text {* 2002 Paper 5 Question 11 part a *}

lemma "\<not>(((Q\<longrightarrow>R)\<longrightarrow>Q)\<and>\<not>Q)"
  apply(rule notI)
  apply(erule conjE)
  apply (erule impE)
   apply (rule impI)
  apply (erule notE)
   apply assumption
  apply(erule notE)
  apply assumption
  done

lemma "((P\<longleftrightarrow>Q)\<longleftrightarrow>P)\<longleftrightarrow>Q"
  apply(rule iffI)
   apply(erule iffE)
   apply (rule classical)
   apply (erule impE)
    apply (rule iffI)
     apply(erule notE)
     apply(erule impE)
      apply assumption
  apply(erule iffE)
     apply (erule impE)
      apply assumption+
    apply(erule notE)
    apply assumption
   apply(erule impE)
    apply assumption
  apply(erule iffE)
   apply (erule impE)
    apply assumption+
  apply(rule iffI)
  apply(erule iffE)
   apply(erule impE)+
     apply assumption+
  apply(erule impE)
    apply assumption+
  apply(rule iffI)
   apply assumption+
  done

lemma "\<exists>x y. P x y \<longrightarrow> (\<forall>x y. P x y)"
  apply (rule classical)
  apply(rule exI)+
  apply(rule impI)
  apply (rule allI)+
  apply (rule classical)
  apply(erule notE)
  apply (rule exI)+
  apply (rule impI)
  apply(rule allI)+
  apply (erule notE)
  apply assumption
  done
  

lemma "(\<forall>x. (P x \<longrightarrow>Q x)\<and>(\<exists>x. P x))\<longrightarrow>(\<forall>x. Q x)"
  quickcheck
  oops

lemma "\<not>((\<forall>x. (P x \<longrightarrow>Q x)\<and>(\<exists>x. P x))\<longrightarrow>(\<forall>x. Q x))"
  quickcheck
  oops
