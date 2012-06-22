theory "FMap-Nominal"
  imports FMap "./Nominal/Nominal/Nominal2" "~~/src/HOL/Library/Permutations"
begin

lemma dom_perm:
  "dom (\<pi> \<bullet> f) = \<pi> \<bullet> (dom f)"
proof
  have 1: "\<And>\<pi> f. dom (\<pi> \<bullet> f) \<subseteq> \<pi> \<bullet> (dom f)"
  proof
    fix \<pi> f x
    assume "x \<in> dom (\<pi> \<bullet> f)"
    then obtain y where "(\<pi> \<bullet> f) x = Some y" by auto
    hence "\<pi> \<bullet> (f (-\<pi> \<bullet> x)) = Some y"  by (auto simp add: permute_fun_def)
    hence "f (-\<pi> \<bullet> x) = -\<pi> \<bullet> Some y" by (metis permute_minus_cancel(2))
    hence "f (-\<pi> \<bullet> x) = Some (-\<pi> \<bullet> y)" by simp
    hence "-\<pi> \<bullet> x \<in> dom f" by auto
    thus "x \<in> \<pi> \<bullet> (dom f)" by (metis (full_types) mem_permute_iff permute_minus_cancel(2))
  qed
  show "dom (\<pi> \<bullet> f) \<subseteq> \<pi> \<bullet> (dom f)" using 1 .

  have "dom (-\<pi> \<bullet> (\<pi> \<bullet> f)) \<subseteq> -\<pi> \<bullet> dom (\<pi> \<bullet> f)" using 1 .
  hence "dom f \<subseteq> -\<pi> \<bullet> dom (\<pi> \<bullet> f)" by simp
  hence "\<pi> \<bullet> dom f \<subseteq> \<pi> \<bullet> (-\<pi> \<bullet> dom (\<pi> \<bullet> f))" by (metis permute_pure subset_eqvt)
  thus  "\<pi> \<bullet> dom f \<subseteq> dom (\<pi> \<bullet> f)" by simp
qed

lemmas dom_perm_rev[simp] = dom_perm[symmetric]

lemma ran_perm[simp]:
  "\<pi> \<bullet> (ran f) = ran (\<pi> \<bullet> f)"
proof
  have 1: "\<And>\<pi> f. ran (\<pi> \<bullet> f) \<subseteq> \<pi> \<bullet> (ran f)"
  using [[show_sorts]]
  proof
    fix \<pi> :: perm and f :: "'c::pt \<rightharpoonup> 'd::pt " and y:: 'd
    assume "y \<in> ran (\<pi> \<bullet> f)"
    then obtain x where "(\<pi> \<bullet> f) x = Some y" by (auto simp add: ran_def)
    hence "\<pi> \<bullet> (f (-\<pi> \<bullet> x)) = Some y"  by (auto simp add: permute_fun_def)
    hence "f (-\<pi> \<bullet> x) = -\<pi> \<bullet> Some y" by (metis permute_minus_cancel(2))
    hence "f (-\<pi> \<bullet> x) = Some (-\<pi> \<bullet> y)" by simp
    hence "-\<pi> \<bullet> y \<in> ran f" by (auto simp add: ran_def)
    thus "y \<in> \<pi> \<bullet> (ran f)" by (metis (full_types) mem_permute_iff permute_minus_cancel(2))
  qed
  show "ran (\<pi> \<bullet> f) \<subseteq> \<pi> \<bullet> (ran f)" using 1 .

  have "ran (-\<pi> \<bullet> (\<pi> \<bullet> f)) \<subseteq> -\<pi> \<bullet> ran (\<pi> \<bullet> f)" using 1 .
  hence "ran f \<subseteq> -\<pi> \<bullet> ran (\<pi> \<bullet> f)" by simp
  hence "\<pi> \<bullet> ran f \<subseteq> \<pi> \<bullet> (-\<pi> \<bullet> ran (\<pi> \<bullet> f))" by (metis permute_pure subset_eqvt)
  thus  "\<pi> \<bullet> ran f \<subseteq> ran (\<pi> \<bullet> f)" by simp
qed

instantiation "fmap" :: (pt,pt) pt
begin
  lift_definition permute_fmap :: "perm \<Rightarrow> ('a::pt,'b::pt) fmap \<Rightarrow> ('a,'b) fmap"
    is "\<lambda> p f . p \<bullet> f" by (simp del: dom_perm_rev add:dom_perm)
  
  instance
  apply(default)
  apply(transfer, simp)+
  done
end

consts permutation_of :: "('a \<rightharpoonup> 'b)  \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool"

lemma have_permutation:
  assumes "permutation_of m' m"
  obtains mp where "mp permutes (dom m)" and "m' = m \<circ> mp"
sorry

lemma is_perm: "\<lbrakk> dom m1 = dom m2 ; ran m1 = ran m2  \<rbrakk> \<Longrightarrow>  permutation_of m1 m2" sorry

lemma perm_finite: "finite (dom m1) \<Longrightarrow> finite {m1. permutation_of m1 m2}" sorry

definition proinj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "proinj_on f A = (\<forall> x\<in>A. finite (f -` {x}))" 

lemma finite_vimage_IntI_proinj:
  "finite F \<Longrightarrow> proinj_on h A \<Longrightarrow> finite (h -` (F \<inter> A))" sorry

lemma vimage_Collect:"f -` {a} = {b. f b = a}" by auto

lemma supp_fmap_raw:
  assumes "finite (dom m)"
  shows  "supp m = (supp (dom m) \<union> supp (ran m))"
proof-
{ 
  fix x 

  let ?f = "(\<lambda>b . (x \<rightleftharpoons> b) \<bullet> m)"

  assume "x \<notin> supp (ran m)" and "x \<notin> supp (dom m)" and "dom m \<noteq> {}"

  from `x \<notin> supp (ran m)`
  have fin_point: "\<And> mp d. d \<in> dom m \<Longrightarrow> finite {b. ?f b = m \<circ> mp}"
    sorry
  have inter: "\<And> mp . {b. ?f b = m \<circ> mp} \<subseteq> (\<Inter> d \<in> dom m. {b. (?f b) d = (m \<circ> mp) d})"
    by auto
  have  "\<And>mp. \<lbrakk> mp permutes dom m;  m \<circ> mp \<noteq> m \<rbrakk> \<Longrightarrow> finite ({b. ?f b = m \<circ> mp})"
    using `dom m \<noteq> {}` fin_point
    by (metis all_not_in_conv)
  hence  "\<And>m'. \<lbrakk> permutation_of m' m;  m' \<noteq> m \<rbrakk> \<Longrightarrow> finite ({b. ?f b = m'})"
    by -(erule have_permutation, auto)
  hence "proinj_on ?f {m'. permutation_of m' m \<and> m' \<noteq> m}" unfolding proinj_on_def
    by (auto simp add: vimage_Collect)

  from `x \<notin> supp (ran m)` and `x \<notin> supp (dom m)`
  have "x \<notin> supp m" 
    unfolding supp_def
    apply simp
    apply (rule finite_subset[of _ "
          {b. dom ((x \<rightleftharpoons> b) \<bullet> m) \<noteq> dom m} \<union> {b. ran ((x \<rightleftharpoons> b) \<bullet> m) \<noteq> ran m} 
              \<union> {b. permutation_of ((x \<rightleftharpoons> b) \<bullet> m) m \<and> (x \<rightleftharpoons> b) \<bullet> m \<noteq> m}"])
    apply rule
    apply simp
    apply (intro strip)
    apply (rule is_perm)
    apply assumption+

    using finite_vimage_IntI_proinj[OF perm_finite[OF `finite (dom m)`] `proinj_on _ _`, of m]
    by (auto simp add:Collect_conj_eq)
} moreover
{ assume "dom m = {}"
  have "supp m = {}" and "supp (dom m) = {}" and "supp (ran m) = {}" sorry
} 
moreover
{ fix x
  have "{b. (x \<rightleftharpoons> b) \<bullet> dom m \<noteq> dom m} \<subseteq> {b. (x \<rightleftharpoons> b) \<bullet> m \<noteq> m}" by auto
  hence "x \<in> supp (dom m) \<Longrightarrow> x \<in> supp m"
  by (auto elim!: infinite_super simp add: supp_def)
} moreover
{ fix x
  have "{b. (x \<rightleftharpoons> b) \<bullet> ran m \<noteq> ran m} \<subseteq> {b. (x \<rightleftharpoons> b) \<bullet> m \<noteq> m}" by auto
  hence "x \<in> supp (ran m) \<Longrightarrow> x \<in> supp m"
  by (auto elim!: infinite_super simp add: supp_def)
} ultimately
show ?thesis by auto
qed

lemma supp_fmap:
  "supp m = (supp (fdom m) \<union> supp (fran m))"
proof-
{ fix x 
  assume "x \<in> supp m"
  assume "x \<notin> supp (fdom m)"
  have "x \<in> supp (fran m)" sorry
} moreover
{ fix x
  assume "x \<in> supp (fdom m)"
  hence "x \<in> supp m" sorry
} moreover
{ fix x
  assume "x \<in> supp (fran m)"
  hence "x \<in> supp m" sorry
} ultimately
show ?thesis by auto
qed


instance "fmap" :: (fs,fs) fs
apply default
sorry

end
