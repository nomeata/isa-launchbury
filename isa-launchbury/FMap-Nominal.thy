theory "FMap-Nominal"
  imports FMap "Nominal-Utils" "~~/src/HOL/Library/FuncSet"
begin

lemma dom_perm:
  "dom (\<pi> \<bullet> f) = \<pi> \<bullet> (dom f)"
  unfolding dom_def by (perm_simp) (simp)

lemmas dom_perm_rev[simp] = dom_perm[symmetric]

lemma ran_perm[simp]:
  "\<pi> \<bullet> (ran f) = ran (\<pi> \<bullet> f)"
  unfolding ran_def by (perm_simp) (simp)

instantiation "fmap" :: (pt,pt) pt
begin
  lift_definition permute_fmap :: "perm \<Rightarrow> 'a::pt f\<rightharpoonup> 'b::pt \<Rightarrow> 'a f\<rightharpoonup> 'b"
    is "\<lambda> p f . p \<bullet> f" by (simp del: dom_perm_rev add:dom_perm)
  
  instance
  apply(default)
  apply(transfer, simp)+
  done
end

lemma lookup_eqvt[eqvt]:
  "\<pi> \<bullet> lookup m x = lookup (\<pi> \<bullet> m) (\<pi> \<bullet> x)"
  by (transfer, auto simp add: permute_fun_def)

lemma mem_transfer[transfer_rule]: "(op = ===> op = ===> op =) op \<in> op \<in>" 
  apply (rule fun_relI)+
  apply (simp)
  done

lemma the_lookup_eqvt:
  "x \<in> fdom m \<Longrightarrow> \<pi> \<bullet> the (lookup m x) = the (lookup (\<pi> \<bullet> m) (\<pi> \<bullet> x))"
  by (transfer fixing: x, auto simp add: dom_def permute_fun_def)

lemma fempty_eqvt[eqvt, simp]:
  "\<pi> \<bullet> fempty = fempty"
  by (transfer, auto simp add: permute_fun_def)

lemma fempty_supp[simp]: "supp fempty = {}"
  by (metis eqvtI fempty_eqvt supp_fun_eqvt)

lemma fempty_fresh[simp]: "a \<sharp> fempty"
  by (simp add: fresh_def)

lemma permute_transfer[transfer_rule]: "(op = ===> cr_fmap ===> cr_fmap) permute permute" 
  apply (rule fun_relI)+
  apply (auto simp add: cr_fmap_def permute_fmap_def simp del: dom_perm_rev simp add: dom_perm Rep_fmap[simplified] Abs_fmap_inverse)
  done

lemma supp_transfer[transfer_rule]: "(cr_fmap ===> op =) supp supp" 
  apply (rule fun_relI)+
  apply (simp add: cr_fmap_def supp_def permute_fmap.rep_eq[symmetric] Rep_fmap_inject)
  done

lemma fresh_transfer[transfer_rule]: "(op = ===> cr_fmap ===> op =) fresh fresh" 
  apply (rule fun_relI)+
  apply (simp add: cr_fmap_def fresh_def)
  using fun_relD[OF supp_transfer, unfolded cr_fmap_def]
  by auto

lemma fresh_star_transfer[transfer_rule]: "(op = ===> cr_fmap ===> op =) fresh_star fresh_star" 
  apply (rule fun_relI)+
  apply (simp add: cr_fmap_def fresh_star_def)
  using fun_relD[OF fun_relD[OF fresh_transfer], unfolded cr_fmap_def]
  by blast

lemma permute_transfer2[transfer_rule]: "(op = ===> op = ===> op =) permute (permute :: perm \<Rightarrow> ('a::pt) set \<Rightarrow> 'a set)" 
  unfolding fun_rel_eq by (rule refl)

lemma fdom_perm: "fdom (\<pi> \<bullet> f) = \<pi> \<bullet> (fdom f)"
  apply transfer by (rule dom_perm)
lemmas fdom_perm_rev[simp,eqvt] = fdom_perm[symmetric]


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
  "supp (m:: 'a::fs f\<rightharpoonup> 'b::fs) = (supp (fdom m) \<union> supp (fran m))"
apply transfer
apply (erule supp_map_union)
by (metis Rel_eq_refl fun_rel_eq set_rel_eq)


instance "fmap" :: (fs,fs) fs
  by (default, auto intro: finite_sets_supp simp add: supp_fmap)

lemma fmap_upd_eqvt[eqvt]: "p \<bullet> (fmap_upd f x y) = fmap_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
  by (transfer, auto simp add:permute_fun_def fun_eq_iff)

lemma fmap_restr_eqvt:
  "finite d \<Longrightarrow> \<pi> \<bullet> (fmap_restr d m) = fmap_restr (\<pi> \<bullet> d) (\<pi> \<bullet> m)"
proof
case goal1 thus ?case by (simp add:fdom_perm inter_eqvt  del:fdom_perm_rev)
case goal2
  hence "finite (\<pi> \<bullet> d)" by simp

  from goal2(2) have "x \<in> \<pi> \<bullet> fdom m \<inter> \<pi> \<bullet> d" by (metis (full_types) fdom_fmap_restr fdom_perm_rev goal1 inter_eqvt)
  then obtain y where "x = \<pi> \<bullet> y" and "y \<in> fdom m \<inter> d" by (auto simp add: permute_set_def)

  have "the (lookup (\<pi> \<bullet> fmap_restr d m) x) = the (lookup (\<pi> \<bullet> fmap_restr d m) (\<pi> \<bullet> y))" by (simp add: `x = _`)
  also have "... = \<pi> \<bullet> (the (lookup (fmap_restr d m) y))" using `finite d` `y \<in> fdom m \<inter> d` by (metis fdom_fmap_restr the_lookup_eqvt)
  also have "... = \<pi> \<bullet> (the (lookup m y))" using `y \<in> _` by (simp add: lookup_fmap_restr[OF `finite d`])
  also have "... = the (lookup (\<pi> \<bullet> m) x)" using `x = _` `y \<in> _` by (simp add: the_lookup_eqvt)
  also have "... = the (lookup (fmap_restr (\<pi> \<bullet> d) (\<pi> \<bullet> m)) x)" using `x \<in> _ \<inter> _` by (simp add: lookup_fmap_restr[OF `finite (\<pi> \<bullet> d)`])
  finally show ?case.
qed

lemma fmap_delete_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_delete x m = fmap_delete (\<pi> \<bullet> x) (\<pi> \<bullet> m)"
  by (transfer, auto simp add: permute_fun_def fun_eq_iff)

lemma fmap_add_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_add m1 m2 = fmap_add (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  by (transfer, perm_simp, rule)

lift_definition fmap_id :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b" is "(\<lambda>x. x)" by simp

lemma fmap_of_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_of l = fmap_of (\<pi> \<bullet> l)"
  (* apply transfer does not do anything here *)
  by (simp add: fmap_of_def permute_fmap_def map_fun_def Abs_fmap_inverse finite_dom_map_of map_of_eqvt)


lemma sharp_Env: "atom x \<sharp> (\<rho> :: 'a::at_base f\<rightharpoonup> 'b::pure) \<longleftrightarrow> x \<notin> fdom \<rho>"
  apply (subst fresh_def)
  apply (simp  add: supp_fmap)
  apply (subst (1 2) fresh_def[symmetric])
  apply (simp add: fresh_finite_set_at_base[OF finite_fdom] pure_fresh)
  done

lemma fmap_fmap_upd[simp]:
  "fran (m(x f\<mapsto> v)) = insert v (fran (fmap_delete x m))"
by (transfer, auto simp add: ran_def)

lemma supp_fmap_upd[simp]:
  "supp (m((x::'a::fs) f\<mapsto> v::'b::fs)) = supp (fmap_delete x m) \<union> supp x \<union> supp v"
  apply (subst (1 2) supp_fmap)
  apply (subst (1 2 3 4) supp_of_finite_sets)
  apply simp_all[4]
  apply auto
  done

lemma fresh_fmap_upd_eq:
  "a \<sharp> m((x::'a::fs) f\<mapsto> v::'b::fs) \<longleftrightarrow> (a \<sharp> (fmap_delete x m) \<and> a \<sharp> x \<and> a \<sharp> v)"
  unfolding fresh_def by simp

lemma fresh_star_fmap_upd_eq:
  "a \<sharp>* m((x::'a::fs) f\<mapsto> v::'b::fs) \<longleftrightarrow> (a \<sharp>* (fmap_delete x m) \<and> a \<sharp>* x \<and> a \<sharp>* v)"
by (metis fresh_fmap_upd_eq fresh_star_def)

end
