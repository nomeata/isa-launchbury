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

lemma C_Cinf[simp]: "C\<cdot>C\<^sup>\<infinity> = C\<^sup>\<infinity>" unfolding Cinf_def by (rule fix_eq[symmetric])

abbreviation Cpow ("C\<^bsup>_\<^esup>") where "C\<^bsup>n\<^esup> \<equiv> iterate n\<cdot>C\<cdot>\<bottom>"

lemma C_below_C[simp]: "(C\<^bsup>i\<^esup> \<sqsubseteq> C\<^bsup>j\<^esup>) \<longleftrightarrow> i \<le> j"
  apply (induction i arbitrary: j)
  apply simp
  apply (case_tac j, auto)
  done

lemma below_Cinf[simp]: "r \<sqsubseteq> C\<^sup>\<infinity>"
  apply (induct r)
  apply simp_all[2]
  apply (metis (full_types) C_Cinf monofun_cfun_arg)
  done

lemma C_eq_Cinf[simp]: "C\<^bsup>i\<^esup> \<noteq> C\<^sup>\<infinity>"
  by (metis C_below_C Suc_n_not_le_n below_Cinf)

lemma Cinf_eq_C[simp]: "C\<^sup>\<infinity> = C \<cdot> r \<longleftrightarrow> C\<^sup>\<infinity> = r"
  by (metis C.injects C_Cinf)

lemma C_eq_C[simp]: "(C\<^bsup>i\<^esup> = C\<^bsup>j\<^esup>) \<longleftrightarrow> i = j"
  by (metis C_below_C le_antisym le_refl)

lemma case_of_C_below: "(case r of C\<cdot>_ \<Rightarrow> x) \<sqsubseteq> x"
  by (cases r) auto

lemma C_case_below: "C_case \<cdot> f \<sqsubseteq> f"
  by (metis cfun_belowI C.case_rews(2) below_C monofun_cfun_arg)

lemma C_case_bot[simp]: "C_case \<cdot> \<bottom> = \<bottom>"
  apply (subst eq_bottom_iff)
  apply (rule C_case_below)
  done

lemma C_case_Cinf[simp]: "C_case \<cdot> f \<cdot> C\<^sup>\<infinity> = f \<cdot> C\<^sup>\<infinity>"
  unfolding Cinf_def
  by (subst fix_eq) simp

lemma nat_mono_characterization:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "mono f"
  obtains n where "\<And>m . n \<le> m \<Longrightarrow> f n = f m" | "\<And> m . \<exists> n . m \<le> f n"
proof (cases "finite (range f)")
  case True
  from Max_in[OF True]
  obtain n where Max: "f n = Max (range f)" by auto
  show thesis
  proof(rule that)
    fix m
    assume "n \<le> m"
    hence "f n \<le> f m" using `mono f` by (metis monoD)
    also
    have "f m \<le> f n" unfolding Max by (rule Max_ge[OF True rangeI])
    finally
    show "f n = f m".
  qed
next
  case False
  thus thesis by (fastforce intro: that(2) simp add: infinite_nat_iff_unbounded_le)
qed

lemma C_cases:
  obtains n where "r = C\<^bsup>n\<^esup>" | "r = C\<^sup>\<infinity>"
proof-
  { fix m
    have "\<exists> n. C_take m \<cdot> r = C\<^bsup>n\<^esup> "
    proof (rule C.finite_induct)
      have "\<bottom> = C\<^bsup>0\<^esup>" by simp
      thus "\<exists>n. \<bottom> = C\<^bsup>n\<^esup>"..
    next
      fix r
      show "\<exists>n. r = C\<^bsup>n\<^esup> \<Longrightarrow> \<exists>n. C\<cdot>r = C\<^bsup>n\<^esup>"
        by (auto simp del: iterate_Suc simp add: iterate_Suc[symmetric])
    qed
  }
  then obtain f where take: "\<And> m. C_take m \<cdot> r = C\<^bsup>f m\<^esup>" by metis
  have "chain (\<lambda> m. C\<^bsup>f m\<^esup>)" using ch2ch_Rep_cfunL[OF C.chain_take, where x=r, unfolded take].
  hence "mono f" by (auto simp add: mono_iff_le_Suc chain_def elim!:chainE)
  have r: "r = (\<Squnion> m. C\<^bsup>f m\<^esup>)"  by (metis (lifting) take C.reach lub_eq)
  from `mono f`
  show thesis
  proof(rule nat_mono_characterization)
    fix n
    assume n: "\<And> m. n \<le> m ==> f n = f m"
    have "max_in_chain n (\<lambda> m. C\<^bsup>f m\<^esup>)"
      apply (rule max_in_chainI)
      apply simp
      apply (erule n)
      done
    hence "(\<Squnion> m. C\<^bsup>f m\<^esup>) = C\<^bsup>f n\<^esup>" unfolding  maxinch_is_thelub[OF `chain _`].
    thus ?thesis using that unfolding r by blast
  next
    assume "\<And>m. \<exists>n. m \<le> f n"
    hence "\<And> n. C\<^bsup>n\<^esup> \<sqsubseteq> r" unfolding r by (fastforce intro: below_lub[OF `chain _`])
    hence "(\<Squnion> n. C\<^bsup>n\<^esup>) \<sqsubseteq> r" 
      by (rule lub_below[OF chain_iterate])
    hence "C\<^sup>\<infinity> \<sqsubseteq> r" unfolding Cinf_def fix_def2.
    hence "C\<^sup>\<infinity> = r" using below_Cinf by (metis below_antisym)
    thus thesis using that by blast
  qed
qed


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

lemma C_meet_is_meet: "(z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (z \<sqsubseteq> x \<and> z \<sqsubseteq> y)"
proof (induct z rule:C.take_induct)
  fix n
  show "(C_take n\<cdot>z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>z \<sqsubseteq> x \<and> C_take n\<cdot>z \<sqsubseteq> y)"
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


instance C :: cont_binary_meet
proof
  have [simp]:"\<And> x y. x \<sqinter> y = C_meet\<cdot>x\<cdot>y"
    using C_meet_is_meet
    by (blast intro: is_meetI)
  case goal1 thus ?case
    by (simp add: ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun)
qed


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
