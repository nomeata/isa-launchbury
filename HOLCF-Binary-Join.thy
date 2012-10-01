theory "HOLCF-Binary-Join"
imports 
  "HOLCF"
begin

subsection {* Binary Joins *}

context pcpo
begin
definition join :: "'a => 'a => 'a" (infix "\<squnion>" 80) where
  "x \<squnion> y = (if \<exists> z. {x, y} <<| z then lub {x, y} else \<bottom>)"

definition compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "compatible x y = (\<exists> z. {x, y} <<| z)"

lemma bot_compatible[simp]:
  "compatible x \<bottom>" "compatible \<bottom> x"
  unfolding compatible_def by (metis insert_commute is_lub_bin minimal)+

lemma join_idem[simp]: "compatible x y \<Longrightarrow> x \<squnion> (x \<squnion> y) = x \<squnion> y"
proof-
  assume c1: "compatible x y"
  then obtain z where z:"{x, y} <<| z" unfolding compatible_def by auto
  hence "x \<sqsubseteq> z" by (metis is_lubD1 is_ub_insert)
  hence "{x, z} <<| z" by (metis is_lub_bin)
  hence "x \<squnion> z = z" unfolding join_def by (auto intro: lub_eqI)
  from z
  have "x \<squnion> y = z" unfolding join_def by (auto intro: lub_eqI)
  hence c2: "compatible x (x \<squnion> y)" unfolding compatible_def using `{x, z} <<| z` by auto
  
  show ?thesis using `x \<squnion> y = z` `x \<squnion> z = z` by auto
qed

lemma join_self[simp]: "x \<squnion> x = x"
  unfolding join_def
  apply auto
  apply (metis is_lub_singleton)
  done
end

lemma compatibleI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "compatible x y"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding compatible_def by (metis)
qed

lemma is_joinI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "x \<squnion> y = z"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding join_def by (metis lub_eqI)
qed

lemma lub_is_join:
  "{x, y} <<| z \<Longrightarrow> x \<squnion> y = z"
unfolding join_def by (metis lub_eqI)


lemma join_mono:
  assumes "compatible a b"
  and "compatible c d"
  and "a \<sqsubseteq> c"
  and "b \<sqsubseteq> d"
  shows "a \<squnion> b \<sqsubseteq> c \<squnion> d"
proof-
  from assms obtain x y where "{a, b} <<| x" "{c, d} <<| y" unfolding compatible_def by auto
  with assms have "a \<sqsubseteq> y" "b \<sqsubseteq> y" by (metis below.r_trans is_lubD1 is_ub_insert)+
  with `{a, b} <<| x` have "x \<sqsubseteq> y" by (metis is_lub_below_iff is_lub_singleton is_ub_insert)
  moreover
  from `{a, b} <<| x` `{c, d} <<| y` have "a \<squnion> b = x" "c \<squnion> d = y" by (metis lub_is_join)+
  ultimately
  show ?thesis by simp
qed

lemma
  assumes "compatible x y"
  shows join_above1: "x \<sqsubseteq> x \<squnion> y" and join_above2: "y \<sqsubseteq> x \<squnion> y"
proof-
  from assms obtain z where "{x,y} <<| z" unfolding compatible_def by auto
  hence  "x \<squnion> y = z" and "x \<sqsubseteq> z" and "y \<sqsubseteq> z" apply (auto intro: lub_is_join) by (metis is_lubD1 is_ub_insert)+
  thus "x \<sqsubseteq> x \<squnion> y" and "y \<sqsubseteq> x \<squnion> y" by simp_all
qed

lemma join_below:
  assumes "compatible x y"
  and "x \<sqsubseteq> a" and "y \<sqsubseteq> a"
  shows "x \<squnion> y \<sqsubseteq> a"
proof-
  from assms obtain z where z: "{x,y} <<| z" unfolding compatible_def by auto
  with assms have "z \<sqsubseteq> a" by (metis is_lub_below_iff is_ub_empty is_ub_insert)
  moreover
  from z have "x \<squnion> y = z" by (rule lub_is_join) 
  ultimately show ?thesis by simp
qed

lemma compatible_adm:
  shows "adm (\<lambda> y. compatible x y)"
proof(rule admI)
  fix Y
  assume c: "chain Y" and "\<forall>i.  compatible x (Y i)"
  hence a: "\<And> i. compatible x (Y i)" by auto
  show "compatible x (\<Squnion> i. Y i)"
  proof(rule compatibleI)
    have c2: "chain (\<lambda>i. x \<squnion> Y i)"
      apply (rule chainI)
      apply (rule join_mono[OF a a below_refl chainE[OF `chain Y`]])
      done
    show "x \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c2] join_above1[OF a])
    show "(\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c] below_lub[OF c2 join_above2[OF a]])
    fix a
    assume "x \<sqsubseteq> a" and "(\<Squnion> i. Y i) \<sqsubseteq> a"
    show "(\<Squnion> i. x \<squnion> Y i) \<sqsubseteq> a"
      apply (rule lub_below[OF c2])
      apply (rule join_below[OF a `x \<sqsubseteq> a`])
      apply (rule below_trans[OF is_ub_thelub[OF c] `(\<Squnion> i. Y i) \<sqsubseteq> a`])
      done
  qed
qed

end