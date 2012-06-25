theory "FMap-Nominal"
  imports FMap "./Nominal/Nominal/Nominal2" "~~/src/HOL/Library/Permutations" "~~/src/HOL/Library/FuncSet"
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

lemma map_between_finite:
  assumes "finite A"
  and "finite B"
  shows "finite {m. dom m = A \<and> ran m = B}"
proof (rule finite_imageD[OF finite_subset])
  def f  \<equiv> "\<lambda> m. (\<lambda> x \<in> A. (the (m x) :: 'b))"
  def g  \<equiv> "\<lambda> f x. (if x \<in> A then Some (f x :: 'b) else None)"
  show "f ` {m. dom m = A \<and> ran m = B} \<subseteq> extensional_funcset A B"
    by (auto simp add: extensional_funcset_def ran_def f_def)
  show "finite (extensional_funcset A B)"
    by (rule finite_extensional_funcset[OF assms])
  show "inj_on f {m. dom m = A \<and> ran m = B}"
    apply(rule inj_on_inverseI[of _ g])
    unfolding f_def g_def
    apply (auto simp add: dom_def fun_eq_iff)
    by (metis not_Some_eq)
qed


lemma perm_finite: "finite (dom m2) \<Longrightarrow> finite {m1. dom m1 = dom m2 \<and> ran m1 = ran m2}"
  by (rule map_between_finite[OF _ finite_range])

lemma supp_set_elem_finite:
  assumes "finite S"
  and "(m::'a::fs) \<in> S"
  and "y \<in> supp m"
  shows "y \<in> supp S"
  using assms supp_of_finite_sets
  by auto

lemma supp_map_union:
  assumes "finite (dom (m:: 'a::fs \<rightharpoonup> 'b::fs))"
  shows  "supp m = (supp (dom m) \<union> supp (ran m))"
proof-
have "finite (ran m)" using assms by (rule finite_range)
{ 
  fix x

  let ?f = "(\<lambda>b . (x \<rightleftharpoons> b) \<bullet> m)"

  assume "x \<notin> supp (ran m)" and "x \<notin> supp (dom m)"

  { fix m'
    assume "dom m = dom m'" and "ran m = ran m'"
    assume "m' \<noteq> m"
    then obtain d where "m' d \<noteq> m d" by auto
    hence "d \<in> dom m" and "d \<in> dom m'" using `dom m = dom m'` by (auto simp add: dom_def)
    
    have "x \<notin> supp d" using `finite (dom m)` `x \<notin> supp (dom m)` `d \<in> dom m`
      by (metis supp_set_elem_finite)
      
    have "{b. ?f b d = m' d} = {b. (x \<rightleftharpoons> b) \<bullet> m ( (x \<rightleftharpoons> b) \<bullet> d) = m' d}"
      by (simp add: permute_fun_def)
    also have "... =  (\<Union> d' \<in> dom m . {b . (x \<rightleftharpoons> b) \<bullet> d = d' \<and> (x \<rightleftharpoons> b) \<bullet> m d' = m' d})"
      using `d \<in> dom m'` `dom m = dom m'`  apply auto
      by (metis Some_eqvt  domD domI permute_swap_cancel2)
    finally
    have "finite ({b. ?f b d = m' d})" 
      apply (rule ssubst)  
      proof
        fix d'
        assume "d' \<in> dom m"
        
        have "d \<noteq> d' \<or> m d' \<noteq> m' d"
          using `m' d \<noteq> m d` by auto
        moreover 
        { assume  "d \<noteq> d'" 
          hence "finite {b . (x \<rightleftharpoons> b) \<bullet> d = d'}" using `x \<notin> supp d`
            by (auto elim!: finite_subset[rotated] simp add: supp_def)
        }
        moreover
        { assume  "d = d'" and "m d' \<noteq> m' d"
          
          have "the (m d') \<in> ran m" using `d' \<in> dom m` 
            by (auto simp add: ran_def)
          hence "x \<notin> supp (the (m d'))" using `finite (ran m)` `ran m = ran m'` `x \<notin> supp (ran m)`
            by (metis supp_set_elem_finite)
          hence "x \<notin> supp (m d')" using `d' \<in> dom m`
            by (auto simp add: ran_def supp_Some)
          hence "finite {b. (x \<rightleftharpoons> b) \<bullet> m d' = m' d}" using `m d' \<noteq> m' d`
            by (auto elim!: finite_subset[rotated] simp add: supp_def)
        }
        ultimately
        have "finite {b . (x \<rightleftharpoons> b) \<bullet> d = d'} \<or> finite {b. (x \<rightleftharpoons> b) \<bullet> m d' = m' d}" by auto
        thus "finite {b . (x \<rightleftharpoons> b) \<bullet> d = d' \<and> (x \<rightleftharpoons> b) \<bullet> m d' = m' d}" by auto
      next
        show "finite (dom m)" by fact
      qed 
    hence "finite ({b. ?f b = m'})"
      by (auto elim: finite_subset[rotated])
  }
  moreover
    have "finite {m'. dom m' = dom m \<and> ran m' = ran m}" using perm_finite[OF `finite (dom m)`] .
    hence "finite {m'. dom m' = dom m \<and> ran m' = ran m \<and> m' \<noteq> m}"
      by (auto elim!: finite_subset[rotated]) 
  ultimately
  have "finite (\<Union> {{b. (x \<rightleftharpoons> b) \<bullet> m = m'} | m'. dom m' = dom m \<and> ran m' = ran m \<and> m' \<noteq> m})"
    by auto
  hence "finite {b. dom (?f b) = dom m \<and> ran (?f b) = ran m \<and> ?f b \<noteq> m}"
    by (auto elim!: finite_subset[rotated])
 
  with `x \<notin> supp (ran m)` and `x \<notin> supp (dom m)`
  have "x \<notin> supp m" 
    unfolding supp_def
    apply simp
    apply (rule finite_subset[of _ "
          {b. dom ((x \<rightleftharpoons> b) \<bullet> m) \<noteq> dom m} \<union> {b. ran ((x \<rightleftharpoons> b) \<bullet> m) \<noteq> ran m} 
              \<union> {b. dom (?f b) = dom m \<and> ran (?f b) = ran m \<and> ?f b \<noteq> m}"])
    by auto
} moreover
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

lemma supp_fmap_transfer[transfer_rule]:
  "(cr_fmap ===> op =) supp supp"
  unfolding fun_rel_def cr_fmap_def supp_def 
  by (simp add: permute_fmap.rep_eq[symmetric] Rep_fmap_inject)

lemma supp_fmap:
  "supp (m:: ('a::fs, 'b::fs) fmap) = (supp (fdom m) \<union> supp (fran m))"
apply transfer
apply (erule supp_map_union)
proof-
  show "Transfer.Rel (op = ===> set_rel op =) supp supp"
    by (metis Rel_eq_refl fun_rel_eq set_rel_eq)
  next
  show "Transfer.Rel (op = ===> set_rel op =) supp supp"
    by (metis Rel_eq_refl fun_rel_eq set_rel_eq)
  next
  show "Transfer.Rel (op = ===> set_rel op = ===> op =) op = op ="
    by (metis Rel_eq_refl fun_rel_eq set_rel_eq)
qed

instance "fmap" :: (fs,fs) fs
  by (default, auto intro: finite_sets_supp simp add: supp_fmap)

lemma fmap_upd_eqvt[eqvt]: "p \<bullet> (fmap_upd f x y) = fmap_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
  by (transfer, auto simp add:permute_fun_def fun_eq_iff)

end
