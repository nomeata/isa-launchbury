theory Fix1
  imports HOLCF
begin

primrec iterate :: "nat => ('a::cpo -> 'a) \<Rightarrow> ('a -> 'a)" where
    "iterate 0 F = (\<Lambda> x. x)"
  | "iterate (Suc n) F = (\<Lambda> x. F\<cdot>(iterate n F\<cdot>x))"

lemma iterate_Suc2: "iterate (Suc n) F \<cdot>x = iterate n F\<cdot>(F\<cdot>x)"
by (induct n) simp_all

lemma chain_iterate_from [simp]: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i F\<cdot>x)"
by (rule chainI, unfold iterate_Suc2, rule monofun_cfun_arg)

lemma iterate_stays_above: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> x \<sqsubseteq> iterate n F \<cdot> x"
  apply (rule nat_induct)
  apply simp
  by (metis "Fix1.iterate_Suc2" monofun_cfun_arg rev_below_trans)

lemma iterate_cont2cont[simp,cont2cont]: "\<lbrakk> cont F; cont G\<rbrakk> \<Longrightarrow> cont (\<lambda>y. iterate i (F y)\<cdot>(G y)) "
  by (induct i, auto)

definition
  "fix1" :: "'a \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<Rightarrow> 'a" where
  "fix1 x F = (if x \<sqsubseteq> F\<cdot>x then (\<Squnion>i. iterate i F\<cdot>x) else x)"

lemma iterate_below_fix: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> iterate n F \<cdot> x \<sqsubseteq> fix1 x F"
  unfolding fix1_def
  apply (subst if_P)
  apply assumption
  using chain_iterate_from
  by (rule is_ub_thelub)

lemma fix_eq: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow>  fix1 x F = F\<cdot>(fix1 x F)"
  apply (simp add: fix1_def)
  apply (subst lub_range_shift [of _ 1, symmetric])
  apply (erule chain_iterate_from)
  apply (subst contlub_cfun_arg)
  apply (erule chain_iterate_from)
  apply simp
  done

lemma fix1_ind: "\<lbrakk> adm P; P x; x \<sqsubseteq> F\<cdot>x; \<And>y. \<lbrakk>x \<sqsubseteq> y ; P y\<rbrakk> \<Longrightarrow> P (F\<cdot>y) \<rbrakk> \<Longrightarrow> P (fix1 x F)"
  unfolding fix1_def
  apply (subst if_P, assumption)
  apply (erule admD)
  apply (erule chain_iterate_from)
  apply (rule nat_induct)
  apply (simp_all add: iterate_stays_above)
  done

lemma fix1_ind2:
  assumes adm: "adm P"
  assumes above: "x \<sqsubseteq> F\<cdot>x"
  assumes 0: "P x" and 1: "P (F\<cdot>x)"
  assumes step: "!!y. \<lbrakk>x \<sqsubseteq> y ; P y; P (F\<cdot>y)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>y))"
  shows "P (fix1 x F)"
  unfolding fix1_def
  apply (subst if_P, fact)
  apply (rule admD [OF adm chain_iterate_from[OF above]])
  apply (rule nat_less_induct)
  apply (case_tac n)
  apply (simp add: 0)
  apply (case_tac nat)
  apply (simp add: 1)
  apply (frule_tac x=nat in spec)
  apply (simp add: step iterate_stays_above[OF above])
done

lemma parallel_fix1_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes aboveF: "x1 \<sqsubseteq> F\<cdot>x1"
  assumes aboveG: "x2 \<sqsubseteq> G\<cdot>x2"
  assumes base: "P x1 x2"
  assumes step: "!!y z. \<lbrakk> x1 \<sqsubseteq> y ; x2 \<sqsubseteq> z; P y z \<rbrakk> \<Longrightarrow> P (F\<cdot>y) (G\<cdot>z)"
  shows "P (fix1 x1 F) (fix1 x2 G)"
proof -
  from adm have adm': "adm (split P)"
    unfolding split_def .
  have "!!i. P (iterate i F\<cdot>x1) (iterate i G\<cdot>x2)"
    by (induct_tac i, simp add: base, simp add: step iterate_stays_above[OF aboveF] iterate_stays_above[OF aboveG])
  hence "!!i. split P (iterate i F\<cdot>x1, iterate i G\<cdot>x2)"
    by simp
  hence "split P (\<Squnion>i. (iterate i F\<cdot>x1, iterate i G\<cdot>x2))"
    apply - apply (rule admD [OF adm']) by(auto intro: ch2ch_Pair simp add: chain_iterate_from[OF aboveF] chain_iterate_from[OF aboveG])
  hence "split P (\<Squnion>i. iterate i F\<cdot>x1, \<Squnion>i. iterate i G\<cdot>x2)"
    by (simp add: lub_Pair chain_iterate_from[OF aboveF] chain_iterate_from[OF aboveG])
  hence "P (\<Squnion>i. iterate i F\<cdot>x1) (\<Squnion>i. iterate i G\<cdot>x2)"
    by simp
  thus "P (fix1 x1 F) (fix1 x2 G)"
    using aboveF aboveG
    by (simp add: fix1_def)
qed

lemma fix1_cont2cont[simp,cont2cont]:"\<lbrakk> cont F ; cont G ; \<And> y. G y \<sqsubseteq> (F y) \<cdot> (G y) \<rbrakk> \<Longrightarrow> cont (\<lambda>y. fix1 (G y) (F y))"
  unfolding fix1_def by auto

lemma[simp]: "(fix1 x (\<Lambda> _. x)) = x"
  by (rule fix1_ind, auto)

end
