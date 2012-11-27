theory "Nominal-Utils"
imports "Nominal/Nominal/Nominal2"
begin

lemma not_self_fresh[simp]: "atom x \<sharp> (x::'a::at_base) \<longleftrightarrow> False"
  by (metis fresh_at_base(2))

lemma image_eqvt[eqvt]: "\<pi> \<bullet> (f ` S) = (\<pi> \<bullet> f) ` (\<pi> \<bullet> S)"
  unfolding permute_set_def permute_fun_def
  by (auto simp add: image_def)

lemma range_eqvt: "\<pi> \<bullet> range Y = range (\<pi> \<bullet> Y)"
  unfolding image_eqvt UNIV_eqvt ..

lemma option_case_eqvt[eqvt]:
  "\<pi> \<bullet> option_case d f x = option_case (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  by(cases x, auto simp add: permute_fun_def)

lemma fresh_star_singleton: "{ x } \<sharp>* e \<longleftrightarrow> x \<sharp> e"
  by (simp add: fresh_star_def)

lemma [simp]:"atom x \<sharp> x \<longleftrightarrow> False" by (metis fresh_at_base(2))

lemma eqvt_fresh_cong1: "(\<And>p x. p \<bullet> (f x) = f (p \<bullet> x)) \<Longrightarrow> a \<sharp> x \<Longrightarrow> a \<sharp> f x "
  apply (rule fresh_fun_eqvt_app[of f])
  apply (auto simp add: eqvt_def permute_fun_def)
  done

lemma eqvt_fresh_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y"
  shows "a \<sharp> f x y"
proof-
  have "eqvt (\<lambda> (x,y). f x y)"
    using eqvt
    by (auto simp add: eqvt_def permute_fun_def)
  moreover
  have "a \<sharp> (x, y)" using fresh1 fresh2 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y). f x y) (x, y)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma eqvt_fresh_star_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp>* x" and fresh2: "a \<sharp>* y"
  shows "a \<sharp>* f x y"
  by (metis fresh_star_def eqvt_fresh_cong2 assms)

lemma eqvt_fresh_cong3:
  assumes eqvt: "(\<And>p x y z. p \<bullet> (f x y z) = f (p \<bullet> x) (p \<bullet> y) (p \<bullet> z))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y" and fresh3: "a \<sharp> z"
  shows "a \<sharp> f x y z"
proof-
  have "eqvt (\<lambda> (x,y,z). f x y z)"
    using eqvt
    by (auto simp add: eqvt_def permute_fun_def)
  moreover
  have "a \<sharp> (x, y, z)" using fresh1 fresh2 fresh3 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y,z). f x y z) (x, y, z)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma funpow_eqvt[simp,eqvt]:
  "\<pi> \<bullet> ((f :: 'a \<Rightarrow> 'a::pt) ^^ n) = (\<pi> \<bullet> f) ^^ (\<pi> \<bullet> n)"
 apply (induct n)
 apply (auto simp add: permute_fun_def permute_pure)[1]
 apply (auto simp add: permute_pure)
 by (metis (no_types) eqvt_lambda permute_fun_app_eq)

lemma supp_mono: "finite (B::'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> supp A \<subseteq> supp B"
  apply (subst (1 2) supp_finite_set_at_base)
  apply (auto dest:infinite_super)
  done

lemma fresh_subset:
  "finite B \<Longrightarrow> x \<sharp> (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp> A"
  by (auto dest:supp_mono simp add: fresh_def)

lemma fresh_set_subset:
  "x \<sharp> (B :: 'a::at_base list) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> x \<sharp> A"
  by (metis fresh_set fresh_subset[OF finite_set])

lemma fresh_star_subset:
  "finite B \<Longrightarrow> x \<sharp>* (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_def fresh_subset)

lemma fresh_star_set_subset:
  "x \<sharp>* (B :: 'a::at_base list) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_set fresh_star_subset[OF finite_set])

lemma fresh_star_fun_eqvt_app: "eqvt f \<Longrightarrow> a \<sharp>* x \<Longrightarrow> a \<sharp>* f x "
  by (metis fresh_star_def fresh_fun_eqvt_app)

lemma eqvt2I:
  assumes "(\<And> p x y. p \<bullet> f x y = f (p \<bullet> x) (p \<bullet> y))"
  shows "eqvt (\<lambda> p. f (fst p) (snd p))"
  by (auto simp add: eqvt_def eqvt_lambda assms unpermute_def)

lemma fresh_fun_eqvt_app2: 
  assumes "(\<And> p x y. p \<bullet> f x y = f (p \<bullet> x) (p \<bullet> y))"
  shows "a \<sharp> x \<Longrightarrow> a \<sharp> y \<Longrightarrow> a \<sharp> f x y"
  by (intro fresh_fun_eqvt_app[of "\<lambda> p. f (fst p) (snd p)" _ "(x, y)", simplified, unfolded fresh_Pair] eqvt2I assms conjI)

lemma fresh_star_fun_eqvt_app2: 
  assumes "(\<And> p x y. p \<bullet> f x y = f (p \<bullet> x) (p \<bullet> y))"
  shows "a \<sharp>* x \<Longrightarrow> a \<sharp>* y \<Longrightarrow> a \<sharp>* f x y"
  by (intro fresh_star_fun_eqvt_app[of "\<lambda> p. f (fst p) (snd p)" _ "(x, y)", simplified, unfolded fresh_star_Pair] eqvt2I assms conjI)

lemma fresh_star_Cons:
  "S \<sharp>* (x # xs) = (S \<sharp>* x \<and> S \<sharp>* xs)"
by (metis fresh_star_def fresh_Cons)

lemma fresh_star_append:
  shows "a \<sharp>* (xs @ ys) \<longleftrightarrow> a \<sharp>* xs \<and> a \<sharp>* ys"
by (metis fresh_star_def fresh_append)

lemma fresh_list_elem:
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "a \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)


end
