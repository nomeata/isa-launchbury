theory "HOLCF-Down-Closed"
  imports "HOLCF-Set"
begin

subsubsection {* Down-closed sets *}

locale down_closed =
  fixes S
  assumes down_closedE: "\<And>x y. x \<in> S \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> S"

lemma down_closedI:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> S"
  shows "down_closed S"
  using assms unfolding down_closed_def by simp

lemma down_closed_inter:
  "down_closed S1 \<Longrightarrow> down_closed S2 \<Longrightarrow> down_closed (S1 \<inter> S2)"
  unfolding down_closed_def by auto

lemma down_closed_ball:
  assumes  "\<And> x. x \<in> A \<Longrightarrow> down_closed (S x)"
  shows  "down_closed (\<Inter>x \<in> A. S x)"
  using assms unfolding down_closed_def by auto

lemma down_closed_Inter:
  assumes  "\<And> z. down_closed (S z)"
  shows  "down_closed (\<Inter>x. S x)"
  using assms by (metis down_closed_ball)

lemma down_closed_vimage:
  assumes "down_closed S"
  and "monofun f"
  shows "down_closed (f -` S)"
  using assms
  unfolding down_closed_def monofun_def vimage_def
  by auto

end
