theory "FMap-Nominal-Unused"
  imports "FMap-Nominal" "FMap-Unused"
begin

subsubsection {* Finite maps have finite support *}

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
    by (rule finite_PiE[OF assms])
  show "inj_on f {m. dom m = A \<and> ran m = B}"
    apply(rule inj_on_inverseI[of _ g])
    unfolding f_def g_def
    apply (auto simp add: dom_def fun_eq_iff)
    by (metis not_Some_eq)
qed

lemma perm_finite: "finite (dom m2) \<Longrightarrow> finite {m1. dom m1 = dom m2 \<and> ran m1 = ran m2}"
  by (rule map_between_finite[OF _ finite_range])


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
      by (metis (hide_lams, no_types) Nominal2_Base.swap_commute eqvt_bound eqvt_lambda permute_swap_cancel2)
    also have "... =  (\<Union> d' \<in> dom m . {b . (x \<rightleftharpoons> b) \<bullet> d = d' \<and> (x \<rightleftharpoons> b) \<bullet> m d' = m' d})"
      using `d \<in> dom m'` `dom m = dom m'`
      apply auto
      apply (metis Some_eqvt domD domI permute_fun_app_eq permute_self permute_swap_cancel swap_eqvt)
      apply (metis permute_self permute_swap_cancel swap_eqvt)
      apply (metis permute_self permute_swap_cancel swap_eqvt)
      done
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
    apply (auto elim!: finite_subset[rotated])
    by (metis (lifting, full_types) mem_Collect_eq)
 
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
  "(pcr_fmap op= op= ===> op =) supp supp"
  unfolding supp_def[abs_def] by transfer_prover


lemma supp_fmap:
  "supp (m:: 'a::fs f\<rightharpoonup> 'b::fs) = (supp (fdom m) \<union> supp (fran m))"
by transfer(erule supp_map_union)

instance "fmap" :: (fs,fs) fs
  by (default, auto intro: finite_sets_supp simp add: supp_fmap)

subsubsection {* Freshness and support *}

lemma supp_fmap_pure:
  fixes \<rho> :: "'a::fs f\<rightharpoonup> 'b::pure"
  shows "supp \<rho> = supp (fdom \<rho>)"
  by (metis supp_fmap Un_empty_right pure_supp)


lemma fresh_fmap_pure:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::pure"
  shows "atom a \<sharp> \<rho> \<longleftrightarrow> a \<notin> fdom \<rho>"
  by (auto simp add: fresh_def supp_fmap_pure supp_finite_set_at_base)

lemma fresh_fdom[simp]: "atom x \<sharp> (f :: 'a::at_base f\<rightharpoonup> 'b::fs) \<Longrightarrow> x \<notin> fdom f"
  apply (subst (asm) fresh_def)
  apply (simp  add: supp_fmap)
  apply (subst (asm) (1 2) fresh_def[symmetric])
  apply (simp add: fresh_finite_set_at_base[OF finite_fdom] pure_fresh)
  done

lemma supp_fmap_upd[simp]:
  "supp (m((x::'a::fs) f\<mapsto> v::'b::fs)) = supp (fmap_delete x m) \<union> supp x \<union> supp v"
  apply (subst (1 2) supp_fmap)
  apply (subst (1 2 3 4) supp_of_finite_sets)
  apply simp_all[4]
  apply auto
  done

lemma supp_fmap_restr_subset:
  fixes m :: "'a::fs f\<rightharpoonup> 'b::fs"
  shows "supp (m f|` S) \<subseteq> supp m"
  apply (induction m)
  apply simp
  apply (case_tac "x \<in> S")
  apply auto
  done

lemma fresh_fmap_restr_subset:
  fixes m :: "'a::fs f\<rightharpoonup> 'b::fs"
  shows "a \<sharp> m \<Longrightarrow> a \<sharp> m f|` S"
  using supp_fmap_restr_subset
  by (auto simp add: fresh_def)

lemma fresh_fmap_upd_eq:
  "a \<sharp> m((x::'a::fs) f\<mapsto> v::'b::fs) \<longleftrightarrow> (a \<sharp> (fmap_delete x m) \<and> a \<sharp> x \<and> a \<sharp> v)"
  unfolding fresh_def by simp

lemma fresh_lookup:
  fixes m :: "'a::fs f\<rightharpoonup> 'b::fs"
  shows "atom x \<sharp> m \<Longrightarrow> lookup m y = Some v \<Longrightarrow> atom x \<sharp> v"
  by (induction m)
     (auto simp add: lookup_fmap_upd_eq fresh_fmap_upd_eq split:if_splits)

lemma fresh_lookup_fdom:
  fixes m :: "'a::fs f\<rightharpoonup> 'b::fs"
  shows "a \<sharp> m \<Longrightarrow> x \<in> fdom m \<Longrightarrow> a \<sharp> m f! x"
  by (metis (full_types) fmap_upd_noop fresh_fmap_upd_eq)

lemma fresh_star_fmap_upd_eq:
  "a \<sharp>* m((x::'a::fs) f\<mapsto> v::'b::fs) \<longleftrightarrow> (a \<sharp>* (fmap_delete x m) \<and> a \<sharp>* x \<and> a \<sharp>* v)"
by (metis fresh_fmap_upd_eq fresh_star_def)

lemma supp_fmap_delete_subset:
  "supp (fmap_delete x m) \<subseteq> supp (m :: 'a::at_base f\<rightharpoonup> 'b::fs)"
  by (auto simp add: supp_fmap simp del: fdom_fmap_delete
        dest: set_mp[OF supp_mono[OF finite_fdom fdom_fmap_delete_subset]]
        dest: set_mp[OF supp_mono[OF finite_fran fran_fmap_delete_subset]])

lemma fresh_fmap_delete_subset:
  "a \<sharp>  (m :: 'a::at_base f\<rightharpoonup> 'b::fs) \<Longrightarrow> a \<sharp> fmap_delete x m"
  using supp_fmap_delete_subset
  by (auto simp add: fresh_def)

lemma fresh_fmap_copy_subset:
  "a \<sharp> (m :: 'a::at_base f\<rightharpoonup> 'b::fs) \<Longrightarrow> a \<sharp> y \<Longrightarrow> a \<sharp> fmap_copy m x y"
  by (auto simp add: fresh_def supp_fmap supp_of_finite_insert  simp del: fdom_fmap_copy
        dest: set_mp[OF supp_mono[OF iffD2[OF finite_insert, OF finite_fdom] fdom_fmap_copy_subset]]
        dest: set_mp[OF supp_mono[OF finite_fran fran_fmap_copy_subset]])

lemma fresh_fun_merge_subset:
  "a \<sharp> (m1 :: 'a::at_base f\<rightharpoonup> 'b::fs) \<Longrightarrow> a \<sharp> m2 \<Longrightarrow> a \<sharp> m1 f++ m2"
  by (auto simp add: fresh_def supp_fmap supp_of_finite_insert supp_of_finite_union 
      dest: set_mp[OF supp_mono[OF finite_UnI[OF finite_fran finite_fran] fran_fun_merge_subset]])

end
