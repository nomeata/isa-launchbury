theory "Denotational-HeapExtend"
  imports "Denotational-Common" "HOLCF-Set" "HOLCF-Down-Closed" "HOLCF-Fix-Join" "Value-Meet"
begin


instantiation fmap :: (type, pcpo) subpcpo_partition
begin
  definition "to_bot x = fmap_bottom (fdom x)"
  lemma [simp]:"fdom (to_bot x) = fdom x"
    unfolding to_bot_fmap_def by auto

  lemma to_bot_vimage_cone:"to_bot -` {to_bot x} = {z. fmap_bottom (fdom x) \<sqsubseteq> z}"
    by (auto simp add:to_bot_fmap_def)

  instance  
  apply default
  apply (subst to_bot_vimage_cone)
  apply (rule subpcpo_cone_above)
  apply (simp add: to_bot_fmap_def fmap_below_dom)
  apply (simp add: to_bot_fmap_def)
  done
end


definition heapExtendJoin_cond'
  where "heapExtendJoin_cond' h eval \<rho> =
      ((\<forall> \<rho>'. compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) \<rho>' \<longrightarrow>
             compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))) \<and>
       (\<forall> e. e\<in> snd`set h \<longrightarrow> cont (eval e)))"

lemma heapExtendJoin_cond'D:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  and   "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) \<rho>'"
  shows " compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))"
  using assms unfolding heapExtendJoin_cond'_def  by metis

lemma heapExtendJoin_cond'I:
  assumes  "\<And> \<rho>'. compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) \<rho>' \<Longrightarrow>
                   compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))"
  and "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (eval e)"
  shows "heapExtendJoin_cond' h eval \<rho>"
  using assms unfolding heapExtendJoin_cond'_def by metis

definition heapExtendJoin :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtendJoin \<rho> h eval =
    (if heapExtendJoin_cond' h eval \<rho>
    then fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>' . fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)))
      (\<lambda> \<rho>'. fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))
    else (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))"

lemma fdom_adm:
   "adm (\<lambda>\<rho>. P (fdom \<rho>))"
   by (metis admI chain_fdom(2))

lemma fdom_adm_eq[simp]:
   "adm (\<lambda>\<rho>. fdom \<rho> = z)"
   by (rule fdom_adm)

(* More special version first, just to check proof *)
lemma fix_join_cont':
  fixes F :: "'a::pcpo \<Rightarrow> 'a"
  assumes "chain Y"
  assumes "cont F"
  assumes "\<And> y::'a. cont (\<lambda>x. y \<squnion> x)"
  assumes "\<And> y::'a. cont (\<lambda>x. x \<squnion> y)"
  shows "(\<mu> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (\<mu> x. Y i \<squnion> F x))"
  apply (rule Fix.fix_least_below)
  apply (subst beta_cfun[OF cont_compose[OF assms(3) assms(2)]])
  apply (subst cont2contlubE[OF assms(2)])
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply (rule assms(4))
  
  apply (subst cont2contlubE[OF assms(3)])
  defer
  apply (subst cont2contlubE[OF assms(4) `chain Y`])
  apply (subst diag_lub)
  prefer 3
  apply (subst Fix.fix_eq) back
  apply (subst beta_cfun[OF cont_compose[OF assms(3) assms(2)]])
  apply (rule below_refl)
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF assms(3)])
  apply (rule cont_compose[OF `cont F`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply fact
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply fact
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF `cont F`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply fact
  done

lemma "fdom \<rho> \<inter> fst ` set h = {} \<Longrightarrow> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. ESem e \<rho>'))"
  by (rule compatible_fmap_disjoint_fdom, simp)

lemma compatible_fmap_is_compatible: "compatible_fmap m1 m2 \<Longrightarrow> fdom m1 = fdom m2 \<Longrightarrow> compatible m1 m2"
  apply (rule compatibleI[of _ "fmap_join m1 m2"])
  apply (erule (1) fmap_join_below1)
  apply (erule (1) fmap_join_below2)
  apply (erule (3) fmap_join_least)
  done

lemma compatible_is_compatible_fmap: assumes "compatible m1 m2" shows "compatible_fmap m1 m2"
proof (rule compatible_fmapI, rule compatibleI)
case (goal1 x)
  show "the (lookup m1 x) \<sqsubseteq> the (lookup (m1 \<squnion> m2) x)"
    by (rule fmap_belowE[OF join_above1[OF assms]])
next
case (goal2 x)
  show "the (lookup m2 x) \<sqsubseteq> the (lookup (m1 \<squnion> m2) x)"
    by (rule fmap_belowE[OF join_above2[OF assms]])
next
case (goal3 x a)
  have "m1 \<sqsubseteq> fmap_upd (m1 \<squnion> m2) x a"
    apply (rule fmap_belowI')
    apply (simp)[1]
    apply (metis "HOLCF-Join.join_above1" assms fmap_below_dom goal3(1) insert_absorb)
    apply (case_tac "xa = x")
    apply (auto simp add: goal3)
    by (rule fmap_belowE[OF join_above1[OF assms]])
  moreover
  have "m2 \<sqsubseteq> fmap_upd (m1 \<squnion> m2) x a"
    apply (rule fmap_belowI')
    apply (simp)[1]
    apply (metis "HOLCF-Join.join_above2" assms below_fmap_def goal3(2) insert_absorb)
    apply (case_tac "xa = x")
    apply (auto simp add: goal3)
    by (rule fmap_belowE[OF join_above2[OF assms]])
  ultimately
  have "m1 \<squnion> m2 \<sqsubseteq> fmap_upd (m1 \<squnion> m2) x a"
    by (rule join_below[OF assms])
  moreover
  have "the (lookup (fmap_upd (m1 \<squnion> m2) x a) x) = a" by simp
  ultimately  
  show "the (lookup (m1 \<squnion> m2) x) \<sqsubseteq> a" by (metis fmap_belowE)
qed

lemma fdom_compatible[simp]:
  "compatible m1 (m2::('a, 'b::pcpo) fmap) \<Longrightarrow> fdom m1 = fdom m2"
by (metis join_above1 join_above2 fmap_below_dom)

lemma fdom_join[simp]:
  "compatible m1 (m2::('a, 'b::pcpo) fmap) \<Longrightarrow> fdom (m1 \<squnion> m2) = fdom m1"
  by (metis join_above1 fmap_below_dom)

lemma join_is_fmap_join:
  assumes "compatible m1 (m2::('a, 'b::pcpo) fmap)"
  shows "m1 \<squnion> m2 = fmap_join m1 m2"
  apply (rule is_joinI)
  apply (rule fmap_join_below1[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  apply (rule fmap_join_below2[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  apply (erule (1) fmap_join_least[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  done

lemma the_lookup_compatible:
  assumes "compatible m1 (m2::('a, 'b::pcpo) fmap)"
  shows "compatible (the (lookup m1 x)) (the (lookup m2 x))"
proof(cases "x \<in> fdom m1")
case True hence "x \<in> fdom m2" by (metis fdom_compatible[OF assms])
  thus ?thesis
    by (metis Int_iff True compatible_fmap_def' compatible_is_compatible_fmap[OF assms])
next
case False
  thus ?thesis
    by (metis assms compatible_refl fdomIff fdom_compatible)
qed

lemma the_lookup_join:
  assumes "compatible m1 (m2::('a, 'b::pcpo) fmap)"
  shows "the (lookup (m1 \<squnion> m2) x) = the (lookup m1 x) \<squnion> the (lookup m2 x)"
proof(cases "x \<in> fdom m1")
case True hence "x \<in> fdom m2" by (metis fdom_compatible[OF assms])
  show ?thesis
  apply (subst join_is_fmap_join[OF assms])
  apply (rule lookup_fmap_join1[OF compatible_is_compatible_fmap[OF assms]])
  by fact+
next
case False
  thus ?thesis by (metis fdomIff join_self fdom_compatible[OF assms] fdom_join[OF assms])
qed


lemma compatible_expand: "compatible_fmap m1 m2 \<Longrightarrow> compatible (fmap_expand m1 (fdom m1 \<union> fdom m2)) (fmap_expand m2 (fdom m1 \<union> fdom m2))"
  apply (rule compatible_fmap_is_compatible)
  apply (erule compatible_fmap_expand)
  apply simp
  done

lemma fmap_join_expand: "compatible_fmap m1 m2 \<Longrightarrow> fmap_join m1 m2 = (fmap_join (fmap_expand m1 (fdom m1 \<union> fdom m2)) (fmap_expand m2 (fdom m1 \<union> fdom m2)))"
  apply (rule fmap_eqI)
  apply simp
  apply simp
  apply (erule disjE)
  apply (case_tac "x \<in> fdom m2")
  apply (simp add: compatible_is_compatible_fmap[OF compatible_expand])
  apply (simp add: compatible_is_compatible_fmap[OF compatible_expand])
  apply (case_tac "x \<in> fdom m1")
  apply (simp add: compatible_is_compatible_fmap[OF compatible_expand])
  apply (simp add: compatible_is_compatible_fmap[OF compatible_expand])
  done

lemma fmap_join_is_join_expand:
  "compatible_fmap m1 (m2::('a, 'b::pcpo) fmap) \<Longrightarrow> fmap_join m1 m2 = fmap_expand m1 (fdom m1 \<union> fdom m2) \<squnion> fmap_expand m2 (fdom m1 \<union> fdom m2)"
  apply (subst fmap_join_expand, assumption)
  apply (erule join_is_fmap_join[symmetric, OF compatible_expand])
  done

lemma disjoint_is_heapExtendJoin_cond':
  "fdom \<rho> \<inter> fst ` set h = {} \<Longrightarrow> (\<forall> e \<in> snd`set h.  cont (ESem e)) \<Longrightarrow> heapExtendJoin_cond' h ESem \<rho>"
  apply (rule heapExtendJoin_cond'I)
  by (metis compatible_expand compatible_fmap_disjoint_fdom heapToEnv_fdom, metis)

lemma heapExtendJoin_cond'_cont:
  " heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> cont (\<lambda>x. fmap_expand (heapToEnv h (\<lambda>e. eval e x)) (fdom \<rho> \<union> fst ` set h))"
unfolding heapExtendJoin_cond'_def
  apply (rule cont_compose[OF fmap_expand_cont])
  apply (rule cont2cont_heapToEnv)
  apply simp
  done

lemma heapExtendJoin_ind:
  assumes "heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> subpcpo_syn.adm_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))) P"
  assumes "heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> P (to_bot (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))"
  assumes "\<And> y. heapExtendJoin_cond' h eval \<rho> \<Longrightarrow>
        y \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)) \<Longrightarrow>
        P y \<Longrightarrow>
        P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e y)) (fdom \<rho> \<union> fst ` set h))"
  assumes "P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h))"
  shows "P (heapExtendJoin \<rho> h eval)"
  unfolding heapExtendJoin_def
  apply (cases "heapExtendJoin_cond' h eval \<rho>")
  apply (simp)
  apply (rule fix_on_jfc''_ind)
  apply (erule heapExtendJoin_cond'_cont)
  apply (erule (1) heapExtendJoin_cond'D)
  apply fact+
  apply (simp)
  apply (rule assms(4))
  done

lemma heapExtendJoin_eq:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  shows "heapExtendJoin \<rho> h eval = fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e (heapExtendJoin \<rho> h eval))) (fdom \<rho> \<union> fst ` set h)"
  unfolding heapExtendJoin_def
  using assms
  apply (simp)
  apply (rule fix_on_jfc''_eq)
  apply (erule heapExtendJoin_cond'_cont)
  apply (erule (1) heapExtendJoin_cond'D)
  done

lemma compatible_fmap_bottom[simp]:
  "fdom x = y \<Longrightarrow> compatible x (fmap_bottom y)"
  by (metis below.r_refl compatibleI to_bot_fmap_def to_bot_minimal)

lemma heapExtendJoin_compatible[simp]:
  "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)) (heapExtendJoin \<rho> \<Gamma> ESem)"
  apply (rule heapExtendJoin_ind)
  apply (rule adm_is_adm_on)
  apply (rule compatible_adm2)
  apply (subst to_bot_fmap_def)
  apply simp
  apply (erule (1) compatible_above1[OF heapExtendJoin_cond'D])
  apply (rule compatible_refl)
  done  


lemma fdom_heapExtendJoin[simp]:
  "fdom (heapExtendJoin \<rho> h eval) = fdom \<rho> \<union> fst ` set h"
  apply (rule heapExtendJoin_ind)
  apply (rule adm_is_adm_on)
  apply simp
  apply simp
  apply (subst fdom_join)

  apply (rule compat_jfc'')
  apply (rule rho_jfc''[OF _ heapExtendJoin_cond'D])
  apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv])
  prefer 2
  apply assumption
  prefer 2
  apply assumption
  apply (metis heapExtendJoin_cond'_def)

  apply (rule F_pres_compat''[OF _ heapExtendJoin_cond'D])
  apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv])
  prefer 2
  apply assumption
  prefer 2
  apply assumption
  apply (metis heapExtendJoin_cond'_def)
  apply assumption
  
  apply auto
  done


lemma lub_eq_range_is_lub:
  "(\<And> i. F (Y i) \<sqsubseteq> F (Y (Suc i))) \<Longrightarrow> F (\<Squnion> i. Y i) = (\<Squnion> i. F (Y i)) \<Longrightarrow> range (\<lambda>i. F (Y i)::'b::cpo) <<| F (\<Squnion> i. Y i)"
  apply (erule ssubst)
  apply (rule cpo_lubI)
  apply (erule chainI)
  done

lemma range_is_lubI2:
  assumes "(\<And> i. F (Y i) \<sqsubseteq> F (Y (Suc i)))"
  assumes "(\<And> i. F (Y i) \<sqsubseteq> F (\<Squnion>i . Y i))"
  assumes "F (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. F (Y i))"
  shows "range (\<lambda>i. F (Y i)::'b::cpo) <<| F (\<Squnion> i. Y i)"
proof-
  have "chain (\<lambda>i. F (Y i))" using assms(1) by (rule chainI)
  have "(\<Squnion> i. F (Y i)) \<sqsubseteq> F (\<Squnion> i. Y i)" by (rule lub_below[OF `chain _` assms(2)])
  hence "F (\<Squnion> i. Y i) = (\<Squnion> i. F (Y i))" using assms(3) by (rule below_antisym[rotated])
  thus ?thesis
    apply (rule ssubst)
    apply (rule cpo_lubI[OF `chain _`])
    done
qed

lemma heapExtendJoin_monofun'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes cond1: "heapExtendJoin_cond' h ESem \<rho>"
  assumes cond2: "heapExtendJoin_cond' h ESem \<rho>'"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  shows "heapExtendJoin \<rho> h ESem \<sqsubseteq> heapExtendJoin \<rho>' h ESem"
    unfolding heapExtendJoin_def
    unfolding if_P[OF cond1] if_P[OF cond2]
    apply (simp only: fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`, symmetric])
    apply (rule fix_on_jfc''_mono'')
    apply (rule monofunE[OF fmap_expand_monofun assms(4)])
    apply (intro cont_compose[OF fmap_expand_cont] cont2cont_heapToEnv assms) apply assumption
    apply (erule heapExtendJoin_cond'D[OF cond1])
    apply (erule heapExtendJoin_cond'D[OF cond2, unfolded fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`, symmetric]])
    done


lemma heapExtendJoin_cont'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes cond1: "heapExtendJoin_cond' h ESem (\<Squnion> i. Y i)"
  assumes cond2: "\<And>i. heapExtendJoin_cond' h ESem (Y i)"
  assumes "chain Y"
  shows "heapExtendJoin (\<Squnion> i. Y  i) h ESem \<sqsubseteq> (\<Squnion> i. heapExtendJoin (Y i) h ESem)"
proof-
  have fdoms[simp]:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 

  have compat_preserve:
    "\<And> i \<rho>'. compatible (fmap_expand (Y i) (?d \<union> fst ` set h)) \<rho>' \<Longrightarrow>
            compatible (fmap_expand (Y i) (?d \<union> fst ` set h)) (fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)) "
     using heapExtendJoin_cond'D[OF cond2] by simp

  have "fix_on       (fix_join_compat'' (\<Squnion> i. fmap_expand (Y i)  (?d \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)))
             (\<lambda>\<rho>'.                     (\<Squnion> i. fmap_expand (Y i)  (?d \<union> fst ` set h)) \<squnion>
                      fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)) \<sqsubseteq>
       (\<Squnion> i. fix_on  (fix_join_compat''      (fmap_expand (Y i) (?d \<union> fst ` set h))  (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)))
                                        (\<lambda>\<rho>'. fmap_expand (Y i) (?d \<union> fst ` set h) \<squnion>
                      fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h))) "
    apply (rule fix_on_join_cont''')
    apply (rule ch2ch_cont[OF fmap_expand_cont `chain Y`])
    apply (intro cont_compose[OF fmap_expand_cont] cont2cont_heapToEnv assms) apply assumption
    apply (erule compat_preserve)
    done
  thus ?thesis
    unfolding heapExtendJoin_def
    unfolding if_P[OF cond1] if_P[OF cond2]
    by (simp  add: cont2contlubE[OF fmap_expand_cont `chain Y`])
qed


lemma heapExtendJoin_cond'_eqvt[eqvt]:
 assumes "heapExtendJoin_cond' h eval \<rho>"
 shows "heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
proof (rule heapExtendJoin_cond'I)
  fix \<rho>'
  assume "compatible (fmap_expand (\<pi> \<bullet> \<rho>) (fdom (\<pi> \<bullet> \<rho>) \<union> fst ` set (\<pi> \<bullet> h))) \<rho>'"
  hence "compatible (-\<pi> \<bullet> (fmap_expand (\<pi> \<bullet> \<rho>) (fdom (\<pi> \<bullet> \<rho>) \<union> fst ` set (\<pi> \<bullet> h)))) (-\<pi> \<bullet>\<rho>')"
    by (rule compatible_eqvt)
  hence "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (-\<pi> \<bullet> \<rho>')"
    apply perm_simp by (metis pemute_minus_self permute_minus_cancel(1))
  hence "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h))
           (fmap_expand (heapToEnv h (\<lambda>e. eval e (- \<pi> \<bullet> \<rho>'))) (fdom \<rho> \<union> fst ` set h))"
    by (rule heapExtendJoin_cond'D[OF assms])
  hence "compatible (\<pi> \<bullet> (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))
           (\<pi> \<bullet> (fmap_expand (heapToEnv h (\<lambda>e. eval e (- \<pi> \<bullet> \<rho>'))) (fdom \<rho> \<union> fst ` set h)))"
    by (rule compatible_eqvt)
  thus  "compatible (fmap_expand (\<pi> \<bullet> \<rho>) (fdom (\<pi> \<bullet> \<rho>) \<union> fst ` set (\<pi> \<bullet> h)))
          (fmap_expand (heapToEnv (\<pi> \<bullet> h) (\<lambda>e. (\<pi> \<bullet> eval) e \<rho>')) (fdom (\<pi> \<bullet> \<rho>) \<union> fst ` set (\<pi> \<bullet> h)))"
    apply (perm_simp)  by (metis (no_types) permute_minus_cancel(2) permute_self)
next
  fix e
  assume "e \<in> snd ` set (\<pi> \<bullet> h)"
  hence "- \<pi> \<bullet> e \<in> -\<pi> \<bullet> (snd ` set (\<pi> \<bullet> h))" by (metis mem_permute_iff)
  hence "-\<pi> \<bullet> e \<in> snd ` set h" apply perm_simp by (metis eqvt_bound permute_self unpermute_def)
  hence "cont (eval (-\<pi> \<bullet> e))" using assms unfolding  heapExtendJoin_cond'_def by metis
  thus "cont ((\<pi> \<bullet> eval) e)" by (metis perm_still_cont permute_fun_def)
qed

lemma fix_join_compat'_eqvt[eqvt]:
  "\<pi> \<bullet> fix_join_compat' (\<rho>::'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}) = fix_join_compat' (\<pi> \<bullet> \<rho>)"
unfolding fix_join_compat'_def
  by (perm_simp, rule)

lemma subcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subcpo S"
  shows "subcpo (\<pi> \<bullet> S)"
proof(rule subcpoI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
    hence "chain (-\<pi> \<bullet> Y)" by (rule chain_eqvt)
  moreover
  assume "\<And> i. Y i \<in> \<pi> \<bullet> S"
  hence "\<And> i. - \<pi> \<bullet> Y i \<in> S" by (metis (full_types) mem_permute_iff permute_minus_cancel(1))
  hence "\<And> i. (- \<pi> \<bullet> Y) i \<in> S" by (metis eqvt_apply permute_pure)
  ultimately
  have "(\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> S" by (metis subcpo.cpo'[OF assms])
  hence "\<pi> \<bullet> (\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> \<pi> \<bullet> S"  by (metis mem_permute_iff)
  find_theorems permute cont
  thus "(\<Squnion> i. Y i) \<in> \<pi> \<bullet> S"
    apply -
    apply (subst (asm) cont2contlubE[OF perm_cont `chain (-\<pi> \<bullet> Y)`])
    by (metis image_image permute_minus_cancel(1) permute_set_eq_image range_eqvt)
qed

lemma subpcpo_bot_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo_bot S b"
  shows "subpcpo_bot (\<pi> \<bullet> S) (\<pi> \<bullet> b)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo'[OF subcpo_eqvt[OF subpcpo_is_subcpo[OF subpcpo_bot_is_subpcpo[OF assms]]]])
  apply (metis bottom_of_subpcpo_bot_there[OF assms] mem_permute_iff)
  apply (metis (full_types) bottom_of_subpcpo_bot_minimal[OF assms] eqvt_bound mem_permute_iff perm_cont_simp)
  done

lemma subpcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo S"
  shows "subpcpo (\<pi> \<bullet> S)"
  by (rule subpcpo_bot_is_subpcpo[OF subpcpo_bot_eqvt[OF subpcpo_is_subpcpo_bot[OF assms]]])

lemma bottom_of_eqvt:
  assumes "subpcpo S"
  shows "\<pi> \<bullet> (bottom_of (S ::('a::cont_pt) set)) = bottom_of (\<pi> \<bullet> S)"
  by (rule bottom_of_subpcpo_bot[symmetric, OF subpcpo_bot_eqvt[OF  subpcpo_is_subpcpo_bot[OF assms]]])


lemma fix_on_jfc'_eqvt:
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}"
  assumes "cont F"
  assumes F_pres_compat:"\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
  shows "\<pi> \<bullet> fix_on (fix_join_compat' \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>') = fix_on (fix_join_compat' (\<pi> \<bullet> \<rho>))  (\<lambda> \<rho>'. (\<pi> \<bullet> \<rho>) \<squnion> (\<pi> \<bullet> F) \<rho>')"
proof-
  have cont_permuted: "cont (\<pi> \<bullet> F)" 
    by (metis assms(1) perm_still_cont)
  have F_pres_compat_permuted: "(\<And> x. compatible (\<pi> \<bullet> \<rho>) x \<Longrightarrow> compatible (\<pi> \<bullet> \<rho>) ((\<pi> \<bullet> F) x))"
    by (metis assms(2) compatible_eqvt eqvt_bound eqvt_lambda unpermute_def)
  show ?thesis
    apply (rule parallel_fix_on_ind[OF subpcpo_jfc' subpcpo_jfc' _ closed_on_jfc'[OF assms] cont_on_jfc'[OF assms] closed_on_jfc'[OF cont_permuted F_pres_compat_permuted] cont_on_jfc'[OF cont_permuted F_pres_compat_permuted] ])
    apply (rule adm_is_adm_on)
    apply auto
    apply (subst bottom_of_eqvt[OF subpcpo_jfc'])
    apply (subst fix_join_compat'_eqvt, rule)
    apply perm_simp
    apply rule
    done
qed

lemma fix_join_compat''_eqvt:
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}"
  assumes "cont F"
  assumes F_pres_compat:"\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
  shows "\<pi> \<bullet> fix_join_compat'' \<rho> F = fix_join_compat'' (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> F)"
proof-
  note fix_on_jfc'_eqvt[OF assms]
  show ?thesis
    unfolding fix_join_compat''_def
    apply (auto simp add: permute_set_eq)
    apply (subst (asm) perm_cont_simp[symmetric, of _ _ \<pi>])
    apply (subst (asm) fix_on_jfc'_eqvt[OF assms])
    apply auto[2]
    apply (subst (asm) perm_cont_simp[symmetric, of _ _ "-\<pi>"])
    apply (subst (asm) fix_on_jfc'_eqvt[OF assms, symmetric])
    apply auto[2]
    done
qed

lemma heapExtendJoin_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtendJoin \<rho> h eval = heapExtendJoin (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "heapExtendJoin_cond' h eval \<rho>")
  case True
  hence True_permuted: "heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
    by (rule heapExtendJoin_cond'_eqvt)

  have  cont: "cont (\<lambda>x. fmap_expand (heapToEnv h (\<lambda>e. eval e x)) (fdom \<rho> \<union> fst ` set h))"
   apply (rule cont_compose[OF fmap_expand_cont])
   apply (rule cont2cont_heapToEnv)
   using True unfolding heapExtendJoin_cond'_def apply metis
   done

  have  cont_permuted: "cont (\<lambda>x. fmap_expand (heapToEnv (\<pi> \<bullet> h) (\<lambda>e. (\<pi> \<bullet> eval) e x)) (fdom (\<pi> \<bullet> \<rho>) \<union> fst ` set (\<pi> \<bullet> h)))"
   apply (rule cont_compose[OF fmap_expand_cont])
   apply (rule cont2cont_heapToEnv)
   using True_permuted unfolding heapExtendJoin_cond'_def apply metis
   done

  show ?thesis
   unfolding heapExtendJoin_def
   apply (simp only: if_P[OF True] if_P[OF True_permuted])
   apply (rule parallel_fix_on_ind[OF
        subpcpo_jfc''
        subpcpo_jfc''
        adm_is_adm_on
        closed_onI[OF closed_jfc''[OF cont heapExtendJoin_cond'D[OF True]]]
        cont_on_jfc''[OF cont heapExtendJoin_cond'D[OF True]]
        closed_onI[OF closed_jfc''[OF cont_permuted heapExtendJoin_cond'D[OF True_permuted]]]
        cont_on_jfc''[OF cont_permuted heapExtendJoin_cond'D[OF True_permuted]]
        ])
   apply simp
   apply assumption+
   apply (subst bottom_of_eqvt[OF subpcpo_jfc''])
   apply (subst fix_join_compat''_eqvt[OF cont heapExtendJoin_cond'D[OF True]], assumption)
   apply (perm_simp, rule)
   apply perm_simp
   apply simp
   done
next
case False 
  hence False_permuted: "\<not> heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
    by (metis heapExtendJoin_cond'_eqvt permute_minus_cancel(2))
  show ?thesis
   unfolding heapExtendJoin_def
   apply (simp only: if_not_P[OF False] if_not_P[OF False_permuted])
   apply perm_simp
   apply rule
   done
qed


lemma heapExtendJoin_cond'_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ; (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow>  heapExtendJoin_cond' heap1 eval1 env1 \<longleftrightarrow> heapExtendJoin_cond'  heap2 eval2 env2"
  unfolding heapExtendJoin_cond'_def by (auto cong:heapToEnv_cong)

lemma heapExtendJoin_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ; (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtendJoin env1 heap1 eval1 = heapExtendJoin env2 heap2 eval2"
  unfolding heapExtendJoin_def
  unfolding heapExtendJoin_cond'_def
  by (auto cong:heapToEnv_cong)

definition heapExtend :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e))
    then fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h)) (\<Lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_update \<rho> \<rho>'))))
    else fempty)"


lemma heapExtend_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtend \<rho> h eval = heapExtend (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "\<forall> e \<in> snd ` set h. cont (eval e)")
  case True
  moreover hence "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)" by (simp only: perm_still_cont4 simp_thms(35))
  ultimately show ?thesis
   unfolding heapExtend_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_update_eqvt)
   apply (subst fix1_eqvt)
   apply (subst Lam_eqvt)
     apply (rule cont2cont)
     apply (rule cont_compose) back
     apply auto[1]
     apply auto[1]
    apply (auto simp add: fmap_bottom_eqvt)[1]
    apply perm_simp
    apply rule
    done
next
case False thus ?thesis
   unfolding heapExtend_def
   apply (simp_all only: if_not_P perm_still_cont4)
   apply auto
  done 
qed

lemma heapExtend_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtend env1 heap1 eval1 = heapExtend env2 heap2 eval2"
  unfolding heapExtend_def
  by (auto cong:heapToEnv_cong)


lemma heapExtend_cont[simp,cont2cont]: "cont (\<lambda>\<rho>. heapExtend \<rho> h eval)"
  unfolding heapExtend_def
  apply (cases "\<forall> e \<in> snd ` set h.  cont (eval e)")
  apply (simp_all only: if_P if_not_P perm_still_cont4 simp_thms(35) if_False)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply (subst beta_cfun)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply simp
  apply simp
  done
end
