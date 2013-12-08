theory C
imports "Nominal-Utils" "Nominal-HOLCF"
begin

default_sort cpo

domain C = C (lazy "C")

instantiation C :: pure
begin
  definition "p \<bullet> (c::C) = c"
instance by default (auto simp add: permute_C_def)
end
instance C :: pcpo_pt
  by default (simp add: pure_permute_id)

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
end
