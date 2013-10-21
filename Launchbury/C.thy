theory C
imports "Nominal-Utils" "Nominal-HOLCF" "HOLCF-Join"
begin

default_sort cpo

domain C = C (lazy "C")

instantiation C :: pure_cpo
begin
  definition "p \<bullet> (c::C) = c"
instance by default (auto simp add: permute_C_def)
end

fixrec Cpred :: "C \<rightarrow> C" where "Cpred\<cdot>(C\<cdot>r) = r"

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

lemma case_of_C_below: "(case r of C\<cdot>y \<Rightarrow> x) \<sqsubseteq> x"
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


subsection {* On C-ranged functions *}

definition demand :: "(C \<rightarrow> 'a::pcpo) \<Rightarrow> C" where
  "demand f = (if f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom> then C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup> else C\<^sup>\<infinity>)"

lemma finite_resources_suffice:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  obtains n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  {
  assume "\<forall>n. f\<cdot>(C\<^bsup>n\<^esup>) = \<bottom>"
  hence "f\<cdot>C\<^sup>\<infinity> \<sqsubseteq> \<bottom>"
    by (auto intro: lub_below[OF ch2ch_Rep_cfunR[OF chain_iterate]]
             simp add: Cinf_def fix_def2 contlub_cfun_arg[OF chain_iterate])
  with assms have False by simp
  }
  thus ?thesis using that by blast
qed

lemma more_resources_suffice:
  assumes "f\<cdot>r \<noteq> \<bottom>" and "r \<sqsubseteq> r'"
  shows "f\<cdot>r' \<noteq> \<bottom>"
  using assms(1) monofun_cfun_arg[OF assms(2), where  f = f]
  by auto

lemma infinite_resources_suffice:
  shows "f\<cdot>r \<noteq> \<bottom> \<Longrightarrow> f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  by (erule more_resources_suffice[OF _ below_Cinf])

lemma demand_suffices:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  apply (simp add: assms demand_def)
  apply (rule finite_resources_suffice[OF assms])
  apply (rule LeastI)
  apply assumption
  done

lemma not_bot_demand:
  "f\<cdot>r \<noteq> \<bottom> \<longleftrightarrow> demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
proof(intro iffI)
  assume "f\<cdot>r \<noteq> \<bottom>"
  thus "demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
    apply (cases r rule:C_cases)
    apply (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
    done
next
  assume *: "demand f \<noteq> C\<^sup>\<infinity>  \<and> demand f \<sqsubseteq> r"
  then have "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>" by (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
  hence "f\<cdot>(demand f) \<noteq> \<bottom>" by (rule demand_suffices)
  moreover from * have "demand f \<sqsubseteq> r"..
  ultimately
  show "f\<cdot>r \<noteq> \<bottom>" by (rule more_resources_suffice)
qed

lemma infinity_bot_demand:
  "f\<cdot>C\<^sup>\<infinity> = \<bottom> \<longleftrightarrow> demand f = C\<^sup>\<infinity>"
  by (metis below_Cinf not_bot_demand)

lemma demand_suffices':
  assumes "demand f = C\<^bsup>n\<^esup>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  by (metis C_eq_Cinf assms demand_suffices infinity_bot_demand)

lemma demand_Suc_Least:
  assumes [simp]: "f\<cdot>\<bottom> = \<bottom>"
  assumes "demand f \<noteq> C\<^sup>\<infinity>"
  shows "demand f = C\<^bsup>(Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))\<^esup>"
proof-
  from assms
  have "demand f = C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup>" by (auto simp add: demand_def)
  also
  then obtain n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (metis  demand_suffices')
  hence "(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>) = Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)"
    apply (rule Least_Suc) by simp
  finally show ?thesis.
qed

lemma demand_C_case[simp]: "demand (C_case\<cdot>f) = C \<cdot> (demand f)"
proof(cases "demand (C_case\<cdot>f) = C\<^sup>\<infinity>")
  case True
  with assms
  have "C_case\<cdot>f\<cdot>C\<^sup>\<infinity> = \<bottom>"
    by (metis infinity_bot_demand)
  with True
  show ?thesis apply auto by (metis infinity_bot_demand)
next
  case False
  hence "demand (C_case\<cdot>f) = C\<^bsup>Suc (LEAST n. (C_case\<cdot>f)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)\<^esup>"
    by (rule demand_Suc_Least[OF C.case_rews(1)])
  also have "\<dots> = C\<cdot>C\<^bsup>LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>\<^esup>" by simp
  also have "\<dots> = C\<cdot>(demand  f)"
    using False unfolding demand_def by auto
  finally show ?thesis.
qed


lemma least_const_True[simp]: "(LEAST n. True) = (0::nat)"
  by (metis gr0I not_less_Least)

fixrec C_restr :: "C \<rightarrow> (C \<rightarrow> 'a::pcpo) \<rightarrow> (C \<rightarrow> 'a)"
  where "C_restr\<cdot>r\<cdot>f\<cdot>r' = (f\<cdot>(r \<sqinter> r'))" 

lemma [simp]: "C_restr\<cdot>r\<cdot>\<bottom> = \<bottom>" by fixrec_simp
lemma [simp]: "f \<cdot> \<bottom> = \<bottom> \<Longrightarrow> C_restr\<cdot>\<bottom>\<cdot>f = \<bottom>"  by fixrec_simp

lemma [simp]: "r \<sqinter> r = (r::C)"
  by (metis below_refl is_meetI)

lemma [simp]: "(r::C) \<sqinter> (r \<sqinter> x) = r \<sqinter> x"
  by (metis below_refl is_meetI meet_below1)

lemma [simp]: "C_restr\<cdot>r\<cdot>(C_restr\<cdot>r'\<cdot>v) = C_restr\<cdot>(r' \<sqinter> r)\<cdot>v"
  apply (rule cfun_eqI)
  apply simp
  done

lemma C_restr_eqD:
  assumes "C_restr\<cdot>r\<cdot>f = C_restr\<cdot>r\<cdot>g"
  assumes "r' \<sqsubseteq> r"
  shows "f\<cdot>r' = g\<cdot>r'"
by (metis C_restr.simps assms below_refl is_meetI)

lemma [simp]: "C\<cdot>r \<sqinter> r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma [simp]: "r \<sqinter> C\<cdot>r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma Cpred_strict[simp]: "Cpred\<cdot>\<bottom> = \<bottom>" by fixrec_simp

lemma Cpred_below: "Cpred\<cdot>r \<sqsubseteq> r"
  by (cases r) (simp_all add: below_C)

lemma [simp]: "(r \<sqinter> Cpred\<cdot>r) = Cpred \<cdot> r"
  by (metis Cpred_below below_refl is_meetI)

lemma [simp]: "(Cpred\<cdot>r \<sqinter> r) = Cpred \<cdot> r"
  by (metis Cpred_below below_refl is_meetI)

lemma C_restr_below[intro, simp]:
  "C_restr\<cdot>r\<cdot>x \<sqsubseteq> x"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below2 monofun_cfun_arg)
  

lemma C_restr_below_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' \<sqsubseteq> g \<cdot> r') \<Longrightarrow> C_restr\<cdot>r\<cdot>f \<sqsubseteq> C_restr\<cdot>r\<cdot>g"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below1)

lemma C_restr_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' = g \<cdot> r') \<Longrightarrow> C_restr\<cdot>r\<cdot>f = C_restr\<cdot>r\<cdot>g"
  apply (intro below_antisym C_restr_below_cong )
  by (metis below_refl)+

lemma [simp]: "C\<cdot>r \<sqinter> C\<cdot>r' = C\<cdot>(r \<sqinter> r')"
  apply (rule is_meetI)
  apply (metis below_refl meet_below1 monofun_cfun_arg)
  apply (metis below_refl meet_below2 monofun_cfun_arg)
  apply (case_tac a)
  apply auto
  by (metis meet_above_iff)

lemma C_restr_C_case[simp]:
  "C_restr\<cdot>(C\<cdot>r)\<cdot>(C_case\<cdot>f) = C_case\<cdot>(C_restr\<cdot>r\<cdot>f)"
  apply (rule cfun_eqI)
  apply simp
  apply (case_tac x)
  apply simp
  apply simp
  done

end
