theory CValue
imports "Denotational-Common"
begin

domain C = C (lazy "C")

instantiation C :: pure_cpo
begin
  definition "p \<bullet> (c::C) = c"
instance by default (auto simp add: permute_C_def)
end

lemma below_C: "x \<sqsubseteq> C\<cdot>x"
  by (induct x) auto

definition Cinf ("C\<^sup>\<infinity>") where "C\<^sup>\<infinity> = fix\<cdot>C"

abbreviation Cpow ("C\<^bsup>_\<^esup>") where "C\<^bsup>n\<^esup> \<equiv> iterate n\<cdot>C\<cdot>\<bottom>"

lemma case_of_C_below: "(case r of C\<cdot>_ \<Rightarrow> x) \<sqsubseteq> x"
  by (cases r) auto

lemma C_case_below: "C_case \<cdot> f \<sqsubseteq> f"
  by (metis cfun_belowI C.case_rews(2) below_C monofun_cfun_arg)

lemma C_case_Cinf[simp]: "C_case \<cdot> f \<cdot> C\<^sup>\<infinity> = f \<cdot> C\<^sup>\<infinity>"
  unfolding Cinf_def
  by (subst fix_eq) simp

instantiation C :: Finite_Meet_cpo begin
  fixrec C_meet :: "C \<rightarrow> C \<rightarrow> C"
    where "C_meet\<cdot>(C\<cdot>a)\<cdot>(C\<cdot>b) = C\<cdot>(C_meet\<cdot>a\<cdot>b)"
  
  lemma[simp]: "C_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "C_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)  

  instance
  apply default
  proof(intro exI conjI strip)
    fix x y
    {
      fix t
      have "(t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (t \<sqsubseteq> x \<and> t \<sqsubseteq> y)"
      proof (induct t rule:C.take_induct)
        fix n
        show "(C_take n\<cdot>t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>t \<sqsubseteq> x \<and> C_take n\<cdot>t \<sqsubseteq> y)"
        proof (induct n arbitrary: t x y rule:nat_induct)
          case 0 thus ?case by auto
          next
          case (Suc n t x y)
            with C.nchotomy[of t] C.nchotomy[of x] C.nchotomy[of y]
            show ?case by fastforce
        qed
     qed auto
    } note * = this
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> x" using * by auto
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> y" using * by auto
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> C_meet\<cdot>x\<cdot>y" using * by auto
qed
end

instance C :: Finite_Meet_bifinite_cpo by default


domain CValue' = CFn (lazy "(C \<rightarrow> CValue') \<rightarrow> (C \<rightarrow> CValue')")
type_synonym CValue = "C \<rightarrow> CValue'"

fixrec CFn_project :: "CValue' \<rightarrow> CValue \<rightarrow> CValue"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

lemma CFn_project_strict[simp]:
  "\<bottom> \<down>CFn v = \<bottom>"
  by (fixrec_simp) 

instantiation CValue' :: pure_cpo
begin
  definition "p \<bullet> (v::CValue') = v"
instance
  apply default
  apply (auto simp add: permute_CValue'_def)
  done
end


instantiation cfun :: (cpo,"{bifinite,cont_binary_meet}") Finite_Meet_cpo begin
  fixrec cfun_meet :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
    where "cfun_meet\<cdot>f\<cdot>g\<cdot>x = (f\<cdot>x) \<sqinter> (g\<cdot>x)"
  
  lemma[simp]: "cfun_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "cfun_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp)+

  instance
  apply default
  proof(intro exI conjI strip)
    fix x y
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> x" by (auto simp add: cfun_below_iff)
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> y" by (auto simp add: cfun_below_iff)
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> cfun_meet\<cdot>x\<cdot>y" by (auto simp add: cfun_below_iff meet_above_iff)
  qed
end

instance cfun :: (profinite,"{Finite_Meet_bifinite_cpo,cont_binary_meet}") Finite_Meet_bifinite_cpo by default

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

instance CValue' :: Finite_Meet_bifinite_cpo by default

end
