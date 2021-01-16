theory de_morgan imports Main begin 

text {*
  Proving De Morgan's Laws in zeroth and first order logic
*}

lemma "(\<not>(P\<or>Q)) = (\<not>P\<and>\<not>Q)" 
  apply (rule iffI)
   apply(rule conjI)
    apply(rule classical)
    apply(erule notE)
    apply(rule disjI1)
    apply(rule classical)
    apply(erule notE)
    apply assumption
   apply(rule classical)
   apply(erule notE)
   apply(rule disjI2)
   apply(rule classical)
   apply(erule notE)
   apply assumption
  apply(erule conjE)
  apply (rule notI)
  apply(erule notE)
  apply(rule classical)
  apply(erule notE)
  apply(erule disjE)
   apply(erule notE)
   apply assumption
  apply assumption
  done

lemma "(\<not>(P\<and>Q)) = (\<not>P\<or>\<not>Q)" 
    apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule conjI)
    apply (rule classical)
    apply (erule notE)
    apply (rule disjI1)
    apply assumption
   apply (rule classical)
   apply (erule notE)
  apply (rule disjI2)
  apply assumption

  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
  apply (erule notE,  assumption)+
  done
lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply(rule iffI)
   apply(rule classical)
   apply(erule notE)
   apply(rule allI)
   apply(rule classical)
   apply(erule notE)
  apply(rule exI)
   apply assumption

  apply(erule exE)
  apply(rule notI)
  apply(erule allE)
  apply(erule notE)
  apply assumption
  done
lemma "(\<not> (\<exists> x. P x)) = (\<forall> x. \<not> P x)"
  apply(rule iffI)
   apply(rule allI)
   apply(rule classical)
   apply (erule notE)
   apply(rule exI)
   apply(rule classical)
   apply(erule notE)
   apply assumption
  apply (rule notI)
  apply (erule exE)
  apply (erule allE)
  apply (erule notE)
  apply assumption
  done
  
 
  
  


