theory condes_dilemmas imports Main begin 

text {*
  Proving the constructive and destructive dilemmas in propositional calculus
*}

lemma "(P\<longrightarrow>Q) \<Longrightarrow>(R\<longrightarrow>S) \<Longrightarrow>(P\<or>R) \<Longrightarrow>(Q\<or>S)"
  apply(erule disjE)
   apply(erule impE)
    apply assumption
   apply(rule disjI1)
   apply assumption
  apply(rule disjI2)
  apply (erule mp)
  apply assumption
  done

lemma "(P\<longrightarrow>Q) \<Longrightarrow>(R\<longrightarrow>S) \<Longrightarrow>(\<not>Q\<or>\<not>S)\<Longrightarrow>(\<not>P\<or>\<not>R) "
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule notI)
   apply(erule notE)
   apply (erule mp)
   apply assumption
  apply(rule disjI2)
  apply(rule notI)
  apply(erule notE)
  apply(erule mp)
  apply assumption
  done
