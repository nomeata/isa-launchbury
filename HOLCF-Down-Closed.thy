theory "HOLCF-Down-Closed"
  imports "HOLCF-Set" "FMap-HOLCF"
begin

definition contains_bottoms where
  "contains_bottoms d S = (\<forall>d'. d' \<subseteq> d \<longrightarrow> (\<forall> x \<in> S. fmap_extend (fmap_restr d' x) (d - d') \<in> S))"

lemma contains_bottomsD:
  "contains_bottoms d S \<Longrightarrow> d' \<subseteq> d \<Longrightarrow> x \<in> S \<Longrightarrow> fmap_extend (fmap_restr d' x) (d - d') \<in> S"
  unfolding contains_bottoms_def by metis

lemma contains_bottomsI:
  "\<lbrakk> \<And> d' x . d' \<subseteq> d \<Longrightarrow> x \<in> S \<Longrightarrow> fmap_extend (fmap_restr d' x) (d - d') \<in> S\<rbrakk> \<Longrightarrow> contains_bottoms d S"
  unfolding contains_bottoms_def by metis

lemma contains_bottoms_subsetD:
  "contains_bottoms d S \<Longrightarrow> d' \<subseteq> d  \<Longrightarrow> (\<lambda> m. fmap_extend m (d - d')) ` fmap_restr d' ` S \<subseteq> S"
  by (auto dest:contains_bottomsD)

lemma contains_bottoms_inter:
  "contains_bottoms d S1 \<Longrightarrow> contains_bottoms d S2 \<Longrightarrow> contains_bottoms d (S1 \<inter> S2)"
  unfolding contains_bottoms_def by auto

lemma contains_bottoms_restr:
  assumes "finite d"
  assumes "d' \<subseteq> d"
  assumes "contains_bottoms d S"
  shows "contains_bottoms d' (fmap_restr d' ` S)" 
proof(rule contains_bottomsI)
  fix d'' x
  assume "d'' \<subseteq> d'"
  assume "x \<in> fmap_restr d' ` S"
  then obtain y where "y \<in> S" and "x = fmap_restr d' y" by auto
  then have "fmap_extend (fmap_restr d'' x) (d - d'') \<in> S" 
    using contains_bottomsD[OF `contains_bottoms d S` subset_trans[OF `d'' \<subseteq> d'` `d' \<subseteq> d`]]
    using `d'' \<subseteq> d'`  `d' \<subseteq> d` `finite d`
    by (simp add: finite_subset Int_absorb2)
  then have "fmap_restr d' (fmap_extend (fmap_restr d'' x) (d - d'')) \<in> fmap_restr d' ` S" by (rule imageI)
  then have "fmap_restr d' (fmap_extend (fmap_restr d'' x) (d' - d'')) \<in> fmap_restr d' ` S" 
       using `d'' \<subseteq> d'`  `d' \<subseteq> d` `finite d`
       by (auto simp add: fmap_restr_fmap_extend Diff_Int_distrib Int_absorb1 Int_absorb2)
  then show "fmap_extend (fmap_restr d'' x) (d' - d'') \<in> fmap_restr d' ` S" 
      apply (subst (asm) fmap_restr_useless)
      using `d'' \<subseteq> d'`  `d' \<subseteq> d` `finite d`
      apply (auto simp add: finite_subset)
      done
qed




(* Down-closedness *)

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

lemma down_closed_contains_bottoms:
  assumes "down_closed S"
  and "finite d"
  and "\<And> x. x \<in> S \<Longrightarrow> fdom x = d"
  shows  "contains_bottoms d S"
proof(rule contains_bottomsI)
  interpret down_closed S by fact
  fix d' x
  assume "x \<in> S"
  hence [simp]: "fdom x = d" by (rule assms(3))
  assume "d' \<subseteq> d"
  have "fmap_extend (fmap_restr d' x) (d - d') \<sqsubseteq> x"
  proof (induct rule: fmap_belowI')
  case 1 thus ?case by (auto simp add: `finite d` finite_subset[OF `d' \<subseteq> d`])
  case (2 var)
    hence "var \<in> d" by (metis `fdom x = d`)
    show ?case
    proof (cases "var \<in> d'")
    case True 
      thus "the (lookup (fmap_extend (fmap_restr d' x) (d - d')) var) \<sqsubseteq> the (lookup x var)"
        by (simp add:`finite d` finite_subset[OF `d' \<subseteq> d` `finite d`])
    next
    case False
      hence "var \<in> d - d'" using 2(2) `fdom x = d` by auto
      thus "the (lookup (fmap_extend (fmap_restr d' x) (d - d')) var) \<sqsubseteq> the (lookup x var)"
        by (simp add:`finite d` finite_subset[OF `d' \<subseteq> d` `finite d`])
    qed
  qed
  thus "fmap_extend (fmap_restr d' x) (d - d') \<in> S"
  by (rule down_closedE[OF `x \<in> S`])
qed

lemma down_closed_restrict_image:
  fixes S :: "('a, 'b::pcpo) fmap set"
  assumes "down_closed S"
  and "\<And> x. x \<in> S \<Longrightarrow> fdom x = d"
  and "finite d"
  and "d' \<subseteq> d"
  shows "down_closed (fmap_restr d' `S)"
proof(rule down_closedI)
  let ?f = "fmap_restr d'"
  let ?g = "\<lambda>y. fmap_extend y (d - d')"
  have im:"?g ` ?f ` S \<subseteq> S" by (metis assms(1) assms(2) assms(3) assms(4) contains_bottoms_subsetD down_closed_contains_bottoms)
  have cut: "\<And> x. fdom x = d' \<Longrightarrow> ?f (?g x) = x" by (metis assms(3) assms(4) restr_extend_cut)

  fix x
  assume "x \<in> ?f ` S" then obtain x' where x'1: "x = ?f x'" and x'2: "x' \<in> S" by auto
  fix y
  assume "y \<sqsubseteq> x"
  hence "?g y \<sqsubseteq> ?g x" by (rule cont2monofunE[OF fmap_extend_cont])
  moreover
  have "?g x \<in> S" by (metis `x \<in> ?f \` S` im image_eqI set_mp)
  ultimately
  have "?g y \<in> S" by (metis down_closed.down_closedE[OF `down_closed S`])
  hence "?f (?g y) \<in> ?f`S" by (rule imageI)
  thus "y \<in> ?f ` S " by (metis x'1 x'2 `y \<sqsubseteq> x` assms(2) assms(3) assms(4) cut fdom_fmap_restr fmap_below_dom inf_absorb2 finite_subset)
qed


lemma down_closed_ball:
  assumes  "\<And> x. x \<in> A \<Longrightarrow> down_closed (S x)"
  shows  "down_closed (\<Inter>x \<in> A. S x)"
  using assms unfolding down_closed_def by auto

lemma down_closed_all:
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


locale nice_domain = subpcpo_bot + down_closed

lemma cone_above_bottom_is_nice:
  "finite d \<Longrightarrow> nice_domain {y. fmap_bottom d \<sqsubseteq> y} (fmap_bottom d)"
  unfolding nice_domain_def
  apply rule
  apply (rule subpcpo_bot_cone_above)
  apply (auto simp add: down_closed_def)
  apply (metis fmap_below_dom)+
  done

lemma nice_domain_is_subpcpo_bot: "nice_domain S d \<Longrightarrow> subpcpo_bot S d"
  unfolding nice_domain_def by auto

lemma nice_domain_is_subpcpo: "nice_domain S d \<Longrightarrow> subpcpo S"
  by (metis subpcpo_bot_is_subpcpo nice_domain_is_subpcpo_bot)

lemma nice_domain_is_down_closed: "nice_domain S d \<Longrightarrow> down_closed S"
  unfolding nice_domain_def by auto

lemma nice_domain_contains_bottoms: "nice_domain S d \<Longrightarrow> contains_bottoms (fdom d) S"
  unfolding nice_domain_def
  apply (auto intro!: down_closed_contains_bottoms)
  apply (metis bottom_of_subpcpo_bot_minimal fmap_below_dom)+
  done

lemma nice_domain_inter:
  "nice_domain S b \<Longrightarrow> nice_domain S2 b \<Longrightarrow> nice_domain (S \<inter> S2) b"
  by (metis nice_domain_def down_closed_inter subpcpo_bot_inter subpcpo_bot_is_subpcpo subpcpo_is_subcpo bottom_of_subpcpo_bot_there)

lemma nice_domain_retrict_image:
  fixes S :: "('a, 'b::pcpo) fmap set"
  assumes "nice_domain S b"
  and "\<And> x. x \<in> S \<Longrightarrow> fdom x = d"
  and "finite d"
  and "d' \<subseteq> d"
  shows "nice_domain (fmap_restr d' `S) (fmap_restr d' b)"
using assms
  unfolding nice_domain_def
  apply -
  apply rule
  apply (rule subpcpo_bot_image[OF _ fmap_restr_cont fmap_extend_cont _ restr_extend_cut[OF `finite d`]])
  apply auto[1]
  apply (metis contains_bottoms_subsetD down_closed_contains_bottoms)
  apply assumption
  apply (erule imageE, simp)
  apply (metis Int_absorb1 fdom_fmap_restr finite_subset)
  by (metis down_closed_restrict_image)


end
