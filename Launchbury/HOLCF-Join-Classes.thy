theory "HOLCF-Join-Classes"
imports "HOLCF-Join"
begin

class Finite_Join_cpo = cpo +
  assumes all_compatible: "compatible x y"

lemmas join_mono = join_mono[OF all_compatible all_compatible ]
lemmas join_above1[simp] = all_compatible[THEN join_above1]
lemmas join_above2[simp] = all_compatible[THEN join_above2]
lemmas join_below[simp] = all_compatible[THEN join_below]
lemmas join_assoc[simp] = join_assoc[OF all_compatible all_compatible all_compatible]
lemmas join_comm = all_compatible[THEN join_commute]


lemma join_cont': "chain Y \<Longrightarrow> (\<Squnion> i. Y i) \<squnion> y = (\<Squnion> i. Y i \<squnion> (y::'a::Finite_Join_cpo))"
by (metis all_compatible join_cont1)

lemma join_cont1:
  fixes y :: "'a :: Finite_Join_cpo"
  shows "cont (\<lambda>x. (x \<squnion> y))"
  apply (rule contI2)
  apply (rule monofunI)
  apply (metis below_refl join_mono)
  apply (rule eq_imp_below)
  apply (rule join_cont')
  apply assumption
  done

lemma join_cont2: 
  fixes x :: "'a :: Finite_Join_cpo"
  shows "cont (\<lambda>y. (x \<squnion> y))"
  unfolding join_comm by (rule join_cont1)

lemma join_cont[cont2cont,simp]:"cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. (f x \<squnion> (g x::'a::Finite_Join_cpo)))"
  apply (rule cont2cont_case_prod[where g = "\<lambda> x. (f x, g x)" and f = "\<lambda> p x y . x \<squnion> y", simplified])
  apply (rule join_cont1)
  apply (rule join_cont2)
  apply (metis cont2cont_Pair)
  done

instantiation "fun" :: (type, Finite_Join_cpo) Finite_Join_cpo
begin
  definition fun_join :: "('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b)"
    where "fun_join = (\<Lambda> f g . (\<lambda> x. (f x) \<squnion> (g x)))"
  lemma [simp]: "(fun_join\<cdot>f\<cdot>g) x = (f x) \<squnion> (g x)"
    unfolding fun_join_def
      apply (subst beta_cfun, intro cont2cont cont2cont_lambda cont2cont_fun)+
      ..
  instance
  apply default
  proof(intro compatibleI exI conjI strip)
    fix x y
    show "x \<sqsubseteq> fun_join\<cdot>x\<cdot>y"  by (auto simp add: fun_below_iff)
    show "y \<sqsubseteq> fun_join\<cdot>x\<cdot>y"  by (auto simp add: fun_below_iff)
    fix z
    assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    thus "fun_join\<cdot>x\<cdot>y \<sqsubseteq> z" by (auto simp add: fun_below_iff)
  qed
end

instantiation "cfun" :: (cpo, Finite_Join_cpo) Finite_Join_cpo
begin
  definition cfun_join :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
    where "cfun_join = (\<Lambda> f g  x. (f \<cdot> x) \<squnion> (g \<cdot> x))"
  lemma [simp]: "cfun_join\<cdot>f\<cdot>g\<cdot>x = (f \<cdot> x) \<squnion> (g \<cdot> x)"
    unfolding cfun_join_def
      apply (subst beta_cfun, intro cont2cont cont2cont_lambda cont2cont_fun)+
      ..
  instance
  apply default
  proof(intro compatibleI exI conjI strip)
    fix x y
    show "x \<sqsubseteq> cfun_join\<cdot>x\<cdot>y"  by (auto simp add: cfun_below_iff)
    show "y \<sqsubseteq> cfun_join\<cdot>x\<cdot>y"  by (auto simp add: cfun_below_iff)
    fix z
    assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    thus "cfun_join\<cdot>x\<cdot>y \<sqsubseteq> z" by (auto simp add: cfun_below_iff)
  qed
end

lemma bot_lub[simp]: "S <<| \<bottom> \<longleftrightarrow>  S \<subseteq> {\<bottom>}"
  by (auto dest!: is_lubD1 is_ubD intro: is_lubI is_ubI)

lemma compatible_up[simp]: "compatible (up\<cdot>x) (up\<cdot>y) \<longleftrightarrow> compatible x y"
proof
  assume "compatible (up\<cdot>x) (up\<cdot>y)"
  then obtain z' where z': "{up\<cdot>x,up\<cdot>y} <<| z'" unfolding compatible_def by auto
  then obtain z where  "{up\<cdot>x,up\<cdot>y} <<| up\<cdot>z" by (cases z') auto
  hence "{x,y} <<| z"
    unfolding is_lub_def
    apply auto
    by (metis up_below)
  thus "compatible x y"  unfolding compatible_def..
next
  assume "compatible x y"
  then obtain z where z: "{x,y} <<| z" unfolding compatible_def by auto
  hence  "{up\<cdot>x,up\<cdot>y} <<| up\<cdot>z"  unfolding is_lub_def
    apply auto
    by (metis not_up_less_UU upE up_below)
  thus "compatible (up\<cdot>x) (up\<cdot>y)"  unfolding compatible_def..
qed


instance u :: (Finite_Join_cpo) Finite_Join_cpo
proof default
  fix x y :: "'a\<^sub>\<bottom>"
  show "compatible x y"
  apply (cases x, simp)
  apply (cases y, simp)
  apply (simp add: all_compatible)
  done
qed

lemma fun_meet_simp[simp]: "(f \<squnion> g) x = f x \<squnion> (g x::'a::Finite_Join_cpo)"
proof-
  have "f \<squnion> g = (\<lambda> x. f x \<squnion> g x)"
  by (rule is_joinI)(auto simp add: fun_below_iff)
  thus ?thesis by simp
qed

lemma cfun_meet_simp[simp]: "(f \<squnion> g) \<cdot> x = f \<cdot> x \<squnion> (g \<cdot> x::'a::Finite_Join_cpo)"
proof-
  have "f \<squnion> g = (\<Lambda> x. f \<cdot> x \<squnion> g \<cdot> x)"
  by (rule is_joinI)(auto simp add: cfun_below_iff)
  thus ?thesis by simp
qed

lemma cfun_join_below:
  fixes f :: "('a::Finite_Join_cpo) \<rightarrow> ('b::Finite_Join_cpo)"
  shows "f\<cdot>x \<squnion> f\<cdot>y \<sqsubseteq> f\<cdot>(x \<squnion> y)"
  by (intro join_below monofun_cfun_arg join_above1 join_above2)
  
lemma join_self_below[iff]:
  "x = x \<squnion> y \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x = y \<squnion> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x \<squnion> y = x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "y \<squnion> x = x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "x \<squnion> y \<sqsubseteq> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  "y \<squnion> x \<sqsubseteq> x \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  apply (metis join_above2 larger_is_join1)
  apply (metis join_above1 larger_is_join2)
  apply (metis join_above2 larger_is_join1)
  apply (metis join_above1 larger_is_join2)
  apply (metis join_above1 join_above2 below_antisym larger_is_join1)
  apply (metis join_above2 join_above1 below_antisym larger_is_join2)
  done

end
