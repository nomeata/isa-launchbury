theory C_restr
imports C "Env-HOLCF" "C-Meet"
begin

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

definition fmap_C_restr :: "C \<rightarrow> ('var::type \<Rightarrow> (C \<rightarrow> 'a::pcpo)) \<rightarrow> ('var \<Rightarrow> (C \<rightarrow> 'a))" where
  "fmap_C_restr = (\<Lambda> r f.  fmap_cmap\<cdot>(C_restr\<cdot>r)\<cdot>f)"

lemma fmap_C_restr_upd[simp]: "fmap_C_restr\<cdot>r\<cdot>(\<rho>(x := v)) = (fmap_C_restr\<cdot>r\<cdot>\<rho>)(x := C_restr\<cdot>r\<cdot>v)"
  unfolding fmap_C_restr_def by simp

lemma fmap_C_restr_lookup[simp]: "(fmap_C_restr\<cdot>r\<cdot>\<rho>) v = C_restr\<cdot>r\<cdot>(\<rho> v)"
  unfolding fmap_C_restr_def by simp

lemma fmap_C_restr_fempty[simp]: "fmap_C_restr\<cdot>r\<cdot>\<bottom> = \<bottom>"
  unfolding fmap_C_restr_def
  by auto

lemma fmap_C_restr_restr_below[intro]: "fmap_C_restr\<cdot>r\<cdot>\<rho> \<sqsubseteq> \<rho>"
  by (auto intro: fun_belowI)

lemma C_restr_eq_Cpred: 
  assumes "C_restr\<cdot>r\<cdot>x = C_restr\<cdot>r\<cdot>y"
  shows "C_restr\<cdot>(Cpred\<cdot>r)\<cdot>x = C_restr\<cdot>(Cpred\<cdot>r)\<cdot>y"
  apply (rule cfun_eqI) 
  apply simp
  by (metis C_restr_eqD[OF assms] Cpred_below meet_below2 meet_comm)

lemma fmap_restr_eq_Cpred: 
  assumes "fmap_C_restr\<cdot>r\<cdot>\<rho>1 = fmap_C_restr\<cdot>r\<cdot>\<rho>2"
  shows "fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1 = fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2"
proof(rule ext)
next
  fix x
  from assms
  have "(fmap_C_restr\<cdot>r\<cdot>\<rho>1) x = (fmap_C_restr\<cdot>r\<cdot>\<rho>2) x" by simp
  thus "(fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1) x = (fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2) x"
    by (auto intro: C_restr_eq_Cpred)
qed


end
