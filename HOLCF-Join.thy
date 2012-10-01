theory "HOLCF-Join"
imports 
  "HOLCF"
begin

subsection {* Binary Joins and compatibility *}

context cpo
begin
definition join :: "'a => 'a => 'a" (infix "\<squnion>" 80) where
  "x \<squnion> y = (if \<exists> z. {x, y} <<| z then lub {x, y} else x)"

definition compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "compatible x y = (\<exists> z. {x, y} <<| z)"


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
  unfolding join_def  by auto
end

lemma join_commute:  "compatible x y \<Longrightarrow> x \<squnion> y = y \<squnion> x"
  unfolding compatible_def unfolding join_def by (metis insert_commute)

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

context pcpo
begin
  lemma bot_compatible[simp]:
    "compatible x \<bottom>" "compatible \<bottom> x"
    unfolding compatible_def by (metis insert_commute is_lub_bin minimal)+
end

subsection {* Towards meets: Lower bounds *}

context po
begin
definition is_lb :: "'a set => 'a => bool" (infix ">|" 55) where
  "S >| x <-> (\<forall>y\<in>S. x \<sqsubseteq> y)"

lemma is_lbI: "(!!x. x \<in> S ==> l \<sqsubseteq> x) ==> S >| l"
  by (simp add: is_lb_def)

lemma is_lbD: "[|S >| l; x \<in> S|] ==> l \<sqsubseteq> x"
  by (simp add: is_lb_def)

lemma is_lb_empty [simp]: "{} >| l"
  unfolding is_lb_def by fast

lemma is_lb_insert [simp]: "(insert x A) >| y = (y \<sqsubseteq> x \<and> A >| y)"
  unfolding is_lb_def by fast

lemma is_lb_downward: "[|S >| l; y \<sqsubseteq> l|] ==> S >| y"
  unfolding is_lb_def by (fast intro: below_trans)

subsection {* Greatest lower bounds *}

definition is_glb :: "'a set => 'a => bool" (infix ">>|" 55) where
  "S >>| x <-> S >| x \<and> (\<forall>u. S >| u --> u \<sqsubseteq> x)"

definition glb :: "'a set => 'a" ("\<Sqinter>_" [60]60) where
  "glb S = (THE x. S >>| x)" 

text {* access to some definition as inference rule *}

lemma is_glbD1: "S >>| x ==> S >| x"
  unfolding is_glb_def by fast

lemma is_glbD2: "[|S >>| x; S >| u|] ==> u \<sqsubseteq> x"
  unfolding is_glb_def by fast

lemma (in po) is_glbI: "[|S >| x; !!u. S >| u ==> u \<sqsubseteq> x|] ==> S >>| x"
  unfolding is_glb_def by fast

lemma is_glb_above_iff: "S >>| x ==> u \<sqsubseteq> x <-> S >| u"
  unfolding is_glb_def is_lb_def by (metis below_trans)

text {* glbs are unique *}

lemma is_glb_unique: "[|S >>| x; S >>| y|] ==> x = y"
  unfolding is_glb_def is_lb_def by (blast intro: below_antisym)


text {* technical lemmas about @{term glb} and @{term is_glb} *}

lemma is_glb_glb: "M >>| x ==> M >>| glb M"
  unfolding glb_def by (rule theI [OF _ is_glb_unique])

lemma glb_eqI: "M >>| l ==> glb M = l"
  by (rule is_glb_unique [OF is_glb_glb])

lemma is_glb_singleton: "{x} >>| x"
  by (simp add: is_glb_def)

lemma glb_singleton [simp]: "glb {x} = x"
  by (rule is_glb_singleton [THEN glb_eqI])

lemma is_glb_bin: "x \<sqsubseteq> y ==> {x, y} >>| x"
  by (simp add: is_glb_def)

lemma glb_bin: "x \<sqsubseteq> y ==> glb {x, y} = x"
  by (rule is_glb_bin [THEN glb_eqI])

lemma is_glb_maximal: "[|S >| x; x \<in> S|] ==> S >>| x"
  by (erule is_glbI, erule (1) is_lbD)

lemma glb_maximal: "[|S >| x; x \<in> S|] ==> glb S = x"
  by (rule is_glb_maximal [THEN glb_eqI])

end


lemma (in cpo) Meet_insert: "S >>| l \<Longrightarrow> {x, l} >>| l2 \<Longrightarrow> insert x S >>| l2"
  apply (rule is_glbI)
  apply (metis is_glb_above_iff is_glb_def is_lb_insert)
  by (metis is_glb_above_iff is_glb_def is_glb_singleton is_lb_insert)

class Finite_Meet_cpo = cpo +
  assumes binary_meet_exists: "\<exists> l. l \<sqsubseteq> x \<and> l \<sqsubseteq> y \<and> (\<forall> z. z \<sqsubseteq> x \<longrightarrow> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> l)"
begin

  lemma binary_meet_exists': "\<exists>l. {x, y} >>| l"
    using binary_meet_exists[of x y]
    unfolding is_glb_def is_lb_def
    by auto

  lemma finite_meet_exists:
    assumes "S \<noteq> {}"
    and "finite S"
    shows "\<exists>x. S >>| x"
  using `S \<noteq> {}`
  apply (induct rule: finite_induct[OF `finite S`])
  apply (erule notE, rule refl)[1]
  apply (case_tac "F = {}")
  apply (metis is_glb_singleton)
  apply (metis Meet_insert binary_meet_exists')
  done
end

class Nonempty_Meet_cpo = cpo +
  assumes nonempty_meet_exists: "S \<noteq> {} \<Longrightarrow> \<exists>x. S >>| x"
begin
  lemma ub_implies_lub_exists:
  assumes "S <| u"
  shows "\<exists> z. S <<| z"
  proof-
    have "{u. S <| u} \<noteq> {}" using assms by auto
    from nonempty_meet_exists[OF this]
    obtain lu where lb: "{u. S <| u} >>| lu" by auto
    hence "S <| lu"
      by (metis is_glb_above_iff is_lb_def is_ub_def mem_Collect_eq)
    hence "S <<| lu"
      by (metis (full_types) is_lubI is_glbD1 is_lb_def lb mem_Collect_eq)
    thus ?thesis ..
  qed
end


(* More about Joins aka least upper bounds *)

lemma (in pcpo) join_empty: "lub {} = (\<bottom>::'a)"
  by (metis (full_types) is_lub_def is_ub_empty lub_eqI minimal)

class Join_cpo = cpo +
  assumes join_exists: "\<exists>x. S <<| x"
begin
  lemma lub_belowI: "\<lbrakk>\<And> x. x \<in> S \<Longrightarrow> x \<sqsubseteq> z \<rbrakk> \<Longrightarrow> lub S  \<sqsubseteq> z"
    by (metis is_lubD2 is_ubI join_exists lub_eqI)

  lemma join_def': "x \<squnion> y = lub {x, y}"
    unfolding join_def using join_exists by auto

  lemma join_belowI: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
    unfolding join_def'
    by (auto intro: lub_belowI)
  
  lemma join_above1: "x \<sqsubseteq> x \<squnion> y"
    unfolding join_def'
    by (metis is_lubD1 is_ub_insert join_exists lub_eqI)
  
  lemma join_above2: "y \<sqsubseteq> x \<squnion> y"
    unfolding join_def'
    by (metis is_lubD1 is_ub_insert join_exists lub_eqI)
end

(* Down-closedness *)

definition down_closed where
  "down_closed S = (\<forall>x y. x \<in> S \<longrightarrow> y \<sqsubseteq> x \<longrightarrow> y \<in> S)"

(* Compatible is downclosed in Nonempty_Meet_exists *)

lemma (in Nonempty_Meet_cpo) compatible_down_closed:
    assumes "compatible x y"
    and "z \<sqsubseteq> x"
    shows "compatible z y"
proof-
    from assms(1) obtain ub where "{x, y} <<| ub" by (metis compatible_def)
    hence "{x,y} <| ub" by (metis is_lubD1)
    hence "{z,y} <| ub" using assms(2) by (metis is_ub_insert rev_below_trans)
    thus ?thesis unfolding compatible_def by (rule ub_implies_lub_exists)
qed

end
