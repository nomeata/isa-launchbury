theory AEnv
imports "Arity-Nominal" Vars "Env" "Nominal-HOLCF"
begin

instantiation var :: discrete_cpo
begin
  definition  [simp]: "(x::var) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

type_synonym AEnv = "var \<Rightarrow> Arity\<^sub>\<bottom>"

definition AE_singleton :: "var \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "AE_singleton x = (\<Lambda> a. (\<lambda> y . (if x = y then a else \<bottom>)))"

lemma AE_singleton_bot[simp]: "AE_singleton x \<cdot> \<bottom> = \<bottom>"
  by (rule ext)(simp add: AE_singleton_def)

lemma AE_singleton_simps[simp]:
  "(AE_singleton x \<cdot> n) x = n"
  "x' \<noteq> x \<Longrightarrow> (AE_singleton x \<cdot> n) x' = \<bottom>"
  by (simp_all add: AE_singleton_def)

lemma up_zero_top[simp]: "x \<sqsubseteq> up\<cdot>(0::Arity)"
  by (cases x) auto

lemma AE_singleton_below_iff[simp]: "AE_singleton x \<cdot> a \<sqsubseteq> ae  \<longleftrightarrow> a \<sqsubseteq> ae x"
  by (auto simp add: fun_below_iff AE_singleton_def)

lemma edom_AE_singleton_up[simp]: "edom (AE_singleton x \<cdot> (up \<cdot> n)) = {x}"
  unfolding edom_def AE_singleton_def by auto

lemma AE_singleton_eqvt[eqvt]: "\<pi> \<bullet> (AE_singleton x) = AE_singleton (\<pi> \<bullet> x)"
  unfolding AE_singleton_def
  apply perm_simp
  apply (simp add: Abs_cfun_eqvt)
  done

lemma env_delete_AE_singleton[simp]: "env_delete x (AE_singleton x \<cdot> n) = \<bottom>"
  unfolding env_delete_def AE_singleton_def
  by auto

lemma join_eqvt[eqvt]: "\<pi> \<bullet> (x \<squnion> (y :: 'a :: {Finite_Join_cpo, cont_pt})) = (\<pi> \<bullet> x) \<squnion> (\<pi> \<bullet> y)"
  by (rule is_joinI[symmetric]) (auto simp add: perm_below_to_right)

(* Move to somewhere? *)
lemma edom_join[simp]: "edom (f \<squnion> (g::('a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}))) = edom f \<union> edom g"
  unfolding edom_def by auto

lemma env_delete_join[simp]: "env_delete x (f \<squnion> (g::('a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}))) = env_delete x f \<squnion> env_delete x g"
  by (metis env_delete_def fun_upd_meet_simp)

lemma env_restr_join:
  fixes m1 m2 :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "(m1 \<squnion> m2) f|` S = (m1 f|` S) \<squnion> (m2 f|` S )"
  by (auto simp add: env_restr_def)

lemma env_restr_join2:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "m f|` S \<squnion> m f|` S' = m f|` (S \<union> S')"
  by (auto simp add: env_restr_def)

lemma join_env_restr_UNIV:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "S1 \<union> S2 = UNIV \<Longrightarrow> (m f|` S1) \<squnion> (m f|` S2) = m"
  by (fastforce simp add: env_restr_def)

lemma env_restr_split:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "m = m f|` S \<squnion> m f|` (- S)"
by (simp add: env_restr_join2 Compl_partition)

end
