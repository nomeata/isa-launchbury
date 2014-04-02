theory "HOLCF-Utils"
  imports HOLCF Pointwise
begin

default_sort type

lemmas cont_fun[simp]
lemmas cont2cont_fun[simp]

lemma cont_compose2:
  assumes "cont c"
  assumes "\<And> x. cont (c x)"
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda>x. c (f x) (g x))"
proof-
  have "monofun (\<lambda>x. c (f x) (g x))"
    apply (rule monofunI)
    apply (rule below_trans[OF cont2monofunE[OF assms(2) cont2monofunE[OF `cont g`]]], assumption)
    apply (rule fun_belowD[OF cont2monofunE[OF `cont c` cont2monofunE[OF `cont f`]]], assumption)
    done
  thus ?thesis
    apply (rule contI2)
    apply (subst cont2contlubE[OF `cont f`], assumption)
    apply (subst cont2contlubE[OF `cont g`], assumption)
    apply (subst cont2contlubE[OF `cont c` ch2ch_cont[OF `cont f`]], assumption)
    apply (subst lub_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (subst cont2contlubE[OF assms(2)ch2ch_cont[OF `cont g`]], assumption)
    apply (subst diag_lub)
    apply (rule ch2ch_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (rule ch2ch_cont[OF assms(2) ch2ch_cont[OF `cont g`]], assumption)
    apply (rule below_refl)
    done
qed

lemma pointwise_adm:
  fixes P :: "'a::pcpo \<Rightarrow> 'b::pcpo \<Rightarrow> bool"
  assumes "adm (\<lambda> x. P (fst x) (snd x))"
  shows "adm (\<lambda> m. pointwise P (fst m) (snd m))"
proof (rule admI)
  case (goal1 Y)
    show ?case
    apply (rule pointwiseI)
    apply (rule admD[OF adm_subst[where t = "\<lambda>p . (fst p x, snd p x)", standard, OF _ assms, simplified] `chain Y`])
    using goal1(2) unfolding pointwise_def by auto
qed

lemma fun_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x := v1) \<sqsubseteq> \<rho>2(x := v2)"
  apply (rule fun_belowI)
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fun_belowD)
  done

lemma fun_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. (f x)(v := h x) :: 'a \<Rightarrow> 'b::pcpo)"
  by (rule cont2cont_lambda)(auto simp add: assms)


subsection {* Composition of fun and cfun *}

(*
lemma comp_lookup_not_there[simp]: "v \<notin> fdom \<rho> \<Longrightarrow> (f \<circ> \<rho>) v = f \<bottom>"
  by (simp add: lookup_not_fdom)

lemma fmap_map_lookup_eq: "(f \<circ> \<rho>) v = (if v \<in> fdom \<rho> then f (\<rho> v) else f \<bottom>)"
  by (auto simp add: lookup_not_fdom)
*)

lemma cont2cont_fmap_map [simp, cont2cont]:
  assumes "cont f"
  assumes "\<And> x. cont (f x)"
  assumes "cont g"
  shows "cont (\<lambda> x. (f x) \<circ> (g x))"
  apply (rule cont2cont_lambda)
  apply (simp)
  apply (intro cont2cont  `cont g` `cont f` cont_compose2[OF assms(1,2)] cont2cont_fun)
  done

definition cfun_comp :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> ('c::type \<Rightarrow> 'a) \<rightarrow> ('c::type \<Rightarrow> 'b)"
  where  "cfun_comp = (\<Lambda> f \<rho>. (\<lambda> x. f\<cdot>x) \<circ> \<rho>)"

lemma [simp]: "cfun_comp\<cdot>f\<cdot>(\<rho>(x := v)) = (cfun_comp\<cdot>f\<cdot>\<rho>)(x := f\<cdot>v)"
  unfolding cfun_comp_def by auto

lemma cfun_comp_app[simp]: "(cfun_comp\<cdot>f\<cdot>\<rho>) x = f\<cdot>(\<rho> x)"
  unfolding cfun_comp_def by auto

lemma not_bot_below_trans[trans]:
  "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b \<Longrightarrow> b \<noteq> \<bottom>"
  by (metis below_bottom_iff)

lemma fix_eq_fix:
  "f\<cdot>(fix\<cdot>g) \<sqsubseteq> fix\<cdot>g \<Longrightarrow> g\<cdot>(fix\<cdot>f) \<sqsubseteq> fix\<cdot>f \<Longrightarrow> fix\<cdot>f = fix\<cdot>g"
  by (metis fix_least_below below_antisym)

end
