theory Unused 
imports CValue  "HOLCF-Meet-Classes"
begin


fixrec CValue'_meet :: "CValue' \<rightarrow> CValue' \<rightarrow> CValue'"
  where "CValue'_meet\<cdot>(CFn\<cdot>f)\<cdot>(CFn\<cdot>g) = CFn \<cdot>(\<Lambda> x r. CValue'_meet \<cdot> (f\<cdot>x\<cdot>r) \<cdot> (g\<cdot>x\<cdot>r))"
  
lemma[simp]: "CValue'_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "CValue'_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)  

lemma CValue'_meet_is_meet: "(z \<sqsubseteq> CValue'_meet\<cdot>x\<cdot>y) = (z \<sqsubseteq> x \<and> z \<sqsubseteq> y)"
proof (induct z rule:CValue'.take_induct)
  fix n
  show "(CValue'_take n\<cdot>z \<sqsubseteq> CValue'_meet\<cdot>x\<cdot>y) = (CValue'_take n\<cdot>z \<sqsubseteq> x \<and> CValue'_take n\<cdot>z \<sqsubseteq> y)"
  proof (induct n arbitrary: z x y rule:nat_induct)
    case 0 thus ?case by auto
    next
    case (Suc n z x y) thus ?case
      apply -
      apply (cases z, simp)
      apply (cases x, simp)
      apply (cases y, simp)
      apply (fastforce simp add: cfun_below_iff)
      done
  qed
qed auto

instance CValue' :: Finite_Meet_cpo
  apply default
  using CValue'_meet_is_meet
  apply blast
  done

instance CValue' :: cont_binary_meet
proof
  have [simp]:"\<And> x y. x \<sqinter> y = CValue'_meet\<cdot>x\<cdot>y"
    using CValue'_meet_is_meet
    by (blast intro: is_meetI)
  case goal1 thus ?case
    by (simp add: ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun)
qed


end
