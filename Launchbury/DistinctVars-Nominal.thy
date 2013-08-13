theory "DistinctVars-Nominal"
imports DistinctVars "Nominal-Utils"
begin

subsubsection {* Freshness lemmas related to associative lists *}

lemma heapVars_not_fresh:
  "x \<in> heapVars \<Gamma> \<Longrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_delete:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (delete v \<Gamma>)"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_heap_expr:
  assumes "a \<sharp> \<Gamma>"
  and "(x,e) \<in> set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (metis fresh_list_elem fresh_Pair)

lemma fresh_heap_expr':
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma supp_image:
  fixes S :: "'a::fs set"
  fixes f :: "'a::fs \<Rightarrow> 'b::fs"
  assumes "finite S"
  and "eqvt f"
  shows "supp (f ` S) \<subseteq> supp S"
proof
  from assms(1) have "finite (f ` S)" by simp

  fix a
  assume "a \<in> supp (f ` S)"
  then obtain y where "a \<in> supp y" and "y \<in> f ` S" 
    unfolding supp_of_finite_sets[OF `finite (f \` S)`] by auto
  then obtain x where "y = f x" and "x \<in> S" by auto
  from this(1) `a \<in> supp y` supp_fun_app_eqvt[OF assms(2)]
  have "a \<in> supp x" by auto
  with `x \<in> S`
  show "a \<in> supp S" unfolding supp_of_finite_sets[OF `finite S`] by auto
qed

lemma fresh_image:
  fixes S :: "'a::fs set"
  fixes f :: "'a::fs \<Rightarrow> 'b::fs"
  assumes "atom a \<sharp> S"
  and "finite S"
  and "eqvt f"
  shows "atom a \<sharp> f ` S"
using assms by (metis fresh_def in_mono supp_image)


lemma fresh_star_heap_expr':
  assumes "S \<sharp>* \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "S \<sharp>* e"
  using assms
  by (metis fresh_star_def fresh_heap_expr')

lemma fresh_map_of:
  assumes "x \<in> heapVars \<Gamma>"
  assumes "a \<sharp> \<Gamma>"
  shows "a \<sharp> the (map_of \<Gamma> x)"
  using assms
  by (induct \<Gamma>)(auto simp add: fresh_Cons fresh_Pair)

lemma fresh_star_map_of:
  assumes "x \<in> heapVars \<Gamma>"
  assumes "a \<sharp>* \<Gamma>"
  shows "a \<sharp>* the (map_of \<Gamma> x)"
  using assms by (simp add: fresh_star_def fresh_map_of)


subsubsection {* Equivariance lemmas *}

lemma heapVars[eqvt]:
  "\<pi> \<bullet> heapVars \<Gamma> = heapVars (\<pi> \<bullet> \<Gamma>)"
  by (simp add: heapVars_def)

lemma distinctVars_eqvt[eqvt]:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (\<pi> \<bullet> \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply simp
  apply (simp add: distinctVars_Cons)
  by (metis (full_types) heapVars mem_permute_iff)

subsubsection {* Freshness and distinctness *}

lemma fresh_heapVars_distinct:
 assumes "atom ` heapVars \<Delta> \<sharp>* \<Gamma>"
 shows "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> heapVars \<Delta>"
    moreover
    assume "x \<in> heapVars \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      by (induct \<Gamma>)(auto simp add: supp_Cons heapVars_def supp_Pair supp_at_base)
    ultimately
    have False
      using assms
      by (simp add: fresh_star_def fresh_def)
  }
  thus "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}" by auto
qed
end
