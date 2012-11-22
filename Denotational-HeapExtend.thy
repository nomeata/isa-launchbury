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

abbreviation heapExtendJoin_cond'
  where "heapExtendJoin_cond' h eval \<rho> \<equiv>
      fix_on_cond_jfc' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) 
                        (\<lambda> \<rho>' . fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))"

(*
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
*)

definition heapExtendJoin :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtendJoin \<rho> h eval =
    (if heapExtendJoin_cond' h eval \<rho>
    then fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>' . fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)))
      (\<lambda> \<rho>'. fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))
    else (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))"

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
  "compatible m1 (m2::(('a::type), ('b::pcpo)) fmap) \<Longrightarrow> fdom m1 = fdom m2"
by (metis join_above1 join_above2 fmap_below_dom)

lemma fdom_join[simp]:
  "compatible m1 (m2::('a::type, ('b::pcpo)) fmap) \<Longrightarrow> fdom (m1 \<squnion> m2) = fdom m1"
  by (metis join_above1 fmap_below_dom)

lemma join_is_fmap_join:
  assumes "compatible m1 (m2::('a::type, 'b::pcpo) fmap)"
  shows "m1 \<squnion> m2 = fmap_join m1 m2"
  apply (rule is_joinI)
  apply (rule fmap_join_below1[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  apply (rule fmap_join_below2[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  apply (erule (1) fmap_join_least[OF compatible_is_compatible_fmap[OF assms] fdom_compatible[OF assms]])
  done

lemma the_lookup_compatible:
  assumes "compatible m1 (m2::('a::type, ('b::pcpo)) fmap)"
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
  assumes "compatible m1 (m2::(('a::type), ('b::pcpo)) fmap)"
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

lemma fmap_restr_compatible: "finite S \<Longrightarrow> compatible m1 (m2\<Colon>('a\<Colon>type, 'b\<Colon>pcpo) fmap) \<Longrightarrow> compatible (fmap_restr S m1) (fmap_restr S m2)"
  apply (rule compatible_fmap_is_compatible)
  apply (rule compatible_fmapI)
  apply (auto elim: the_lookup_compatible)
  done

lemma fmap_restr_join: "finite S \<Longrightarrow> compatible m1 (m2\<Colon>('a\<Colon>type, 'b\<Colon>pcpo) fmap) \<Longrightarrow> fmap_restr S (m1 \<squnion> m2) = fmap_restr S m1 \<squnion> fmap_restr S m2"
  apply (frule (1) fmap_restr_compatible)
  apply (rule fmap_eqI)
  apply simp
  apply (simp add: the_lookup_join)
  done

lemma fmap_join_is_join_expand:
  "compatible_fmap m1 (m2::('a, 'b::pcpo) fmap) \<Longrightarrow> fmap_join m1 m2 = fmap_expand m1 (fdom m1 \<union> fdom m2) \<squnion> fmap_expand m2 (fdom m1 \<union> fdom m2)"
  apply (subst fmap_join_expand, assumption)
  apply (erule join_is_fmap_join[symmetric, OF compatible_expand])
  done

lemma disjoint_is_heapExtendJoin_cond':
  "fdom \<rho> \<inter> fst ` set h = {} \<Longrightarrow> (\<forall> e \<in> snd`set h.  cont (ESem e)) \<Longrightarrow> heapExtendJoin_cond' h ESem \<rho>"
  apply (rule fix_on_cond_jfc'I)
  apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv])
  apply (metis)
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>")
  apply simp
  apply (subst lookup_fmap_expand2)
  apply auto
  done

lemma fempty_is_heapExtendJoin_cond':
  "(\<forall> e \<in> snd`set h.  cont (ESem e)) \<Longrightarrow> heapExtendJoin_cond' h ESem fempty"
  apply (rule disjoint_is_heapExtendJoin_cond')
  by auto

lemma heapExtendJoin_cond'_cont:
  "heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> cont (\<lambda>x. fmap_expand (heapToEnv h (\<lambda>e. eval e x)) (fdom \<rho> \<union> fst ` set h))"
  by (rule cont_F_jfc'')

lemma heapExtendJoin_ind':
  assumes "heapExtendJoin_cond' h eval \<rho>"
  assumes "adm_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))) P"
  assumes "P (to_bot (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))"
  assumes "\<And> y. y \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)) \<Longrightarrow>
        P y \<Longrightarrow>
        P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e y)) (fdom \<rho> \<union> fst ` set h))"
  shows "P (heapExtendJoin \<rho> h eval)"
  unfolding heapExtendJoin_def
  apply (subst if_P[OF assms(1)])
  apply (rule fix_on_jfc''_ind[OF assms(1)])
  apply fact
  apply (simp add:bottom_of_jfc'')
  apply fact
  apply fact
  done

lemma heapExtendJoin_ind:
  assumes "heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> adm_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))) P"
  assumes "heapExtendJoin_cond' h eval \<rho> \<Longrightarrow> P (to_bot (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)))"
  assumes "\<And> y. heapExtendJoin_cond' h eval \<rho> \<Longrightarrow>
        y \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)) \<Longrightarrow>
        P y \<Longrightarrow>
        P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e y)) (fdom \<rho> \<union> fst ` set h))"
  assumes "P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h))"
  shows "P (heapExtendJoin \<rho> h eval)"
  apply (cases "heapExtendJoin_cond' h eval \<rho>")
  apply (rule heapExtendJoin_ind'[OF _ assms(1,2,3)], assumption+)
  unfolding heapExtendJoin_def
  apply (subst if_not_P, assumption)
  apply (rule assms(4))
  done

lemma parallel_heapExtendJoin_ind:
  assumes cond1: "heapExtendJoin_cond' h eval \<rho>"
  assumes cond2: "heapExtendJoin_cond' h2 eval2 \<rho>2"
  assumes "adm_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda>\<rho>'. fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))
                  \<times> fix_join_compat'' (fmap_expand \<rho>2 (fdom \<rho>2 \<union> fst ` set h2)) (\<lambda>\<rho>'. fmap_expand (heapToEnv h2 (\<lambda>e. eval2 e \<rho>')) (fdom \<rho>2 \<union> fst ` set h2)))
                 (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (fmap_bottom (fdom \<rho>2 \<union> fst ` set h2))"
  assumes "\<And>y z. y \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h))
               (\<lambda>\<rho>'. fmap_expand (heapToEnv h (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h)) \<Longrightarrow>
          z \<in> fix_join_compat'' (fmap_expand \<rho>2 (fdom \<rho>2 \<union> fst ` set h2))
               (\<lambda>\<rho>'. fmap_expand (heapToEnv h2 (\<lambda>e. eval2 e \<rho>')) (fdom \<rho>2 \<union> fst ` set h2)) \<Longrightarrow>
          P y z \<Longrightarrow>
          P (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e y)) (fdom \<rho> \<union> fst ` set h))
           (fmap_expand \<rho>2 (fdom \<rho>2 \<union> fst ` set h2) \<squnion> fmap_expand (heapToEnv h2 (\<lambda>e. eval2 e z)) (fdom \<rho>2 \<union> fst ` set h2)) "
  shows "P (heapExtendJoin \<rho> h eval) (heapExtendJoin \<rho>2 h2 eval2)"
  unfolding heapExtendJoin_def if_P[OF cond1] if_P[OF cond2]
  apply (rule parallel_fix_on_ind[OF fix_on_cond_jfc''[OF cond1] fix_on_cond_jfc''[OF cond2]])
  apply (rule assms(3))
  using assms(4) apply (simp add: bottom_of_jfc'' to_bot_fmap_def)
  by (rule assms(5))


lemma heapExtendJoin_eq:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  shows "heapExtendJoin \<rho> h eval = fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<squnion> fmap_expand (heapToEnv h (\<lambda>e. eval e (heapExtendJoin \<rho> h eval))) (fdom \<rho> \<union> fst ` set h)"
  unfolding heapExtendJoin_def
  using assms
  apply (simp)
  apply (erule fix_on_jfc''_eq)
  done

lemma heapExtendJoin_there:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  shows "heapExtendJoin \<rho> h eval \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda> e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set h))"
  unfolding heapExtendJoin_def
  apply (subst if_P[OF assms])
  apply (rule fix_on_there[OF fix_on_cond_jfc''[OF assms]])
  done

lemma the_lookup_heapExtendJoin_other:
  assumes "y \<notin> fst ` set h"
  shows "the (lookup (heapExtendJoin \<rho> h eval) y) = the (lookup \<rho> y)"
proof(cases "heapExtendJoin_cond' h eval \<rho>")
  case True show ?thesis
    apply (subst heapExtendJoin_eq[OF True])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF True heapExtendJoin_there[OF True]]])
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms lookup_not_fdom)
    done
next
  case False show ?thesis
    unfolding heapExtendJoin_def if_not_P[OF False]
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms  False lookup_not_fdom)
    done
qed

lemma the_lookup_heapExtendJoin_both:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  assumes "y \<in> fst ` set h"
  shows "the (lookup (heapExtendJoin \<rho> h eval) y) =
    the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) y) \<squnion> eval (the (map_of h y)) (heapExtendJoin \<rho> h eval)"
  apply (subst heapExtendJoin_eq[OF assms(1)])
  apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF assms(1) heapExtendJoin_there[OF assms(1)]]])
  apply (subst (2) lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst lookupHeapToEnv[OF assms(2)])
  by (rule refl)

lemma the_lookup_heapExtendJoin_both_compatible:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  assumes "y \<in> fst ` set h"
  shows "compatible (the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) y)) (eval (the (map_of h y)) (heapExtendJoin \<rho> h eval))"
  using the_lookup_compatible[OF rho_F_compat_jfc''[OF assms(1) heapExtendJoin_there[OF assms(1)]], of y]
  apply (subst (asm) (2) lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst (asm) lookupHeapToEnv[OF assms(2)])
  .

lemma the_lookup_heapExtendJoin_heap:
  assumes "heapExtendJoin_cond' h eval \<rho>"
  assumes "y \<in> fst ` set h"
  assumes "y \<notin> fdom \<rho>"
  shows "the (lookup (heapExtendJoin \<rho> h eval) y) = eval (the (map_of h y)) (heapExtendJoin \<rho> h eval)"
  apply (subst heapExtendJoin_eq[OF assms(1)])
  apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF assms(1) heapExtendJoin_there[OF assms(1)]]])
  apply (subst lookup_fmap_expand2)
    using assms(2,3) apply auto[3]
  apply (subst lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst lookupHeapToEnv[OF assms(2)])
  by (simp)

lemma compatible_fmap_bottom[simp]:
  "fdom x = y \<Longrightarrow> compatible x (fmap_bottom y)"
  by (metis below.r_refl compatibleI to_bot_fmap_def to_bot_minimal)

lemma heapExtendJoin_compatible[simp]:
  "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)) (heapExtendJoin \<rho> \<Gamma> ESem)"
  unfolding heapExtendJoin_def
  apply (cases "heapExtendJoin_cond' \<Gamma> ESem \<rho>")
  apply (simp)
  apply (rule compat_jfc'')
  apply (erule rho_jfc'')
  apply (erule fix_on_there[OF fix_on_cond_jfc''])
  apply simp
  done
  
lemma fdom_heapExtendJoin[simp]:
  "fdom (heapExtendJoin \<rho> h eval) = fdom \<rho> \<union> fst ` set h"
  apply (rule heapExtendJoin_ind)
  apply (rule adm_is_adm_on)
  apply simp
  apply simp
  apply (subst fdom_join)

  apply (rule compat_jfc'')
  apply (erule rho_jfc'')
  apply (erule (1) F_pres_compat'')
  apply simp+
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
    apply (rule fix_on_mono2[OF fix_on_cond_jfc''[OF cond1] fix_on_cond_jfc''[OF cond2]])
    apply (simp add: bottom_of_jfc'' to_bot_fmap_def fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`])
    apply (erule (1) join_mono[OF rho_F_compat_jfc''[OF cond1] rho_F_compat_jfc''[OF cond2]])
    apply (subst fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`], rule monofunE[OF fmap_expand_monofun assms(4)])
    apply (subst fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`], rule monofunE[OF fmap_expand_monofun])
    apply (erule cont2monofunE[rotated])
    apply (intro cont_compose[OF fmap_expand_cont] cont2cont_heapToEnv assms) apply assumption
    done


lemma heapExtendJoin_cont'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes cond1: "heapExtendJoin_cond' h ESem (\<Squnion> i. Y i)"
  assumes cond2: "\<And>i. heapExtendJoin_cond' h ESem (Y i)"
  assumes "chain Y"
  shows "heapExtendJoin (\<Squnion> i. Y  i) h ESem = (\<Squnion> i. heapExtendJoin (Y i) h ESem)"
proof-
  have fdoms[simp]:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 

  (*
  have compat_preserve:
    "\<And> i \<rho>'. compatible (fmap_expand (Y i) (?d \<union> fst ` set h)) \<rho>' \<Longrightarrow>
            compatible (fmap_expand (Y i) (?d \<union> fst ` set h)) (fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)) "
     using heapExtendJoin_cond'D[OF cond2] by simp
  *)

  have "fix_on       (fix_join_compat'' (\<Squnion> i. fmap_expand (Y i)  (?d \<union> fst ` set h)) (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)))
             (\<lambda>\<rho>'.                     (\<Squnion> i. fmap_expand (Y i)  (?d \<union> fst ` set h)) \<squnion>
                      fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)) =
       (\<Squnion> i. fix_on  (fix_join_compat''      (fmap_expand (Y i) (?d \<union> fst ` set h))  (\<lambda> \<rho>'. fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h)))
                                        (\<lambda>\<rho>'. fmap_expand (Y i) (?d \<union> fst ` set h) \<squnion>
                      fmap_expand (heapToEnv h (\<lambda>e. ESem e \<rho>')) (?d \<union> fst ` set h))) "
    by (rule fix_on_join_cont'''[OF 
          ch2ch_cont[OF fmap_expand_cont `chain Y`]
          cond2[unfolded fdoms]
          cond1[unfolded cont2contlubE[OF fmap_expand_cont `chain Y`]]
          ])
  thus ?thesis
    unfolding heapExtendJoin_def
    unfolding if_P[OF cond1] if_P[OF cond2]
    by (simp add: cont2contlubE[OF fmap_expand_cont `chain Y`])
qed

lemma heapExtendJoin_refines:
  assumes "heapExtendJoin_cond' h ESem \<rho>"
  shows "fmap_expand \<rho> (fdom \<rho> \<union> fst `set h) \<sqsubseteq> heapExtendJoin \<rho> h ESem"
  apply (subst heapExtendJoin_eq[OF assms(1)])
  apply (rule join_above1[OF rho_F_compat_jfc''[OF assms heapExtendJoin_there[OF assms]]])
done

lemma heapExtendJoin_below:
  assumes "fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<sqsubseteq> r"
  assumes "\<And>x. x \<in> fst ` set h \<Longrightarrow> ESem (the (map_of h x)) r \<sqsubseteq> the (lookup r x)"
  assumes cont: "\<And> e. cont (ESem e)"
  shows "heapExtendJoin \<rho> h ESem \<sqsubseteq> r"
proof (rule heapExtendJoin_ind)
  from fmap_below_dom[OF assms(1)]
  have [simp]:"fdom r = fdom \<rho> \<union> fst ` set h" by simp
  {
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
    show ?case
    apply (rule join_below[OF rho_F_compat_jfc''[OF goal3(1) goal3(2)] assms(1)])
    apply (rule fmap_expand_belowI)
    apply simp
    apply (simp add: lookupHeapToEnv)
    by (rule below_trans[OF
          cont2monofunE[OF cont goal3(3)]
          assms(2)])
  next
  case goal4 show ?case by fact
  }
qed  


(*

lemma heapExtendJoin_cond'_eqvt[eqvt]:
 assumes "heapExtendJoin_cond' h eval \<rho>"
 shows "heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
sor ry
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
*)

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

(*
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
*)

lemma closed_on_eqvt:
  "closed_on S F \<Longrightarrow> closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule closed_onI)
  apply (simp add: permute_set_def)
  by (metis closed_onE eqvt_apply)

lemma cont_eqvt[eqvt]:
  "cont (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont (\<pi> \<bullet> F)"
  apply (rule contI)
  apply (drule_tac Y = "unpermute \<pi> Y" in contE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done

lemma chain_on_eqvt:
  "chain_on (S::'a::cont_pt set) Y \<Longrightarrow> chain_on (\<pi> \<bullet> S) (\<pi> \<bullet> Y)"
  apply (rule chain_onI)
  apply (drule_tac i = i in chain_onE)
  apply (metis perm_cont_simp permute_fun_app_eq permute_pure)
  apply (drule_tac i = i in chain_on_is_on)
  by (metis (full_types) mem_permute_iff permute_fun_app_eq permute_pure)

lemma cont_on_eqvt:
  "cont_on S (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule cont_onI)
  apply (drule_tac Y = "unpermute \<pi> Y" in cont_onE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (metis chain_on_eqvt permute_minus_cancel(2))
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (drule chain_on_is_chain)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done


lemma fix_on_cond_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof
  from assms
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
    by (metis fix_on_cond.cases)+

  show "subpcpo (\<pi> \<bullet> S)" by (rule subpcpo_eqvt[OF pcpo1])
  show "bottom_of (\<pi> \<bullet> S) = \<pi> \<bullet> b" by (simp add: bottom_of_eqvt[OF pcpo1, symmetric])
  show "closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule closed_on_eqvt[OF closed])
  show "cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule cont_on_eqvt[OF cont])
qed

lemma fix_on_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "\<pi> \<bullet> (fix_on' b F) = fix_on' (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof-
  have permuted: "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
    by (rule fix_on_cond_eqvt[OF assms])
  show ?thesis
    apply (rule parallel_fix_on_ind[OF assms permuted])
    apply (rule adm_is_adm_on, auto)[1]
    by (auto simp add: eqvt_apply)
qed

lemma to_bot_eqvt[eqvt,simp]: "\<pi> \<bullet> to_bot (\<rho>::'a::{subpcpo_partition,cont_pt}) = to_bot (\<pi> \<bullet> \<rho>)"
proof(rule below_antisym)
  show "to_bot (\<pi> \<bullet> \<rho>) \<sqsubseteq> \<pi> \<bullet> to_bot \<rho>"
    by (metis perm_cont_simp to_bot_minimal unrelated)
  show "\<pi> \<bullet> to_bot \<rho> \<sqsubseteq> to_bot (\<pi> \<bullet> \<rho>)"
    by (metis eqvt_bound perm_cont_simp to_bot_minimal unrelated)
qed



lemma fix_on_cond_jfc'_eqvt[eqvt]:
  shows "fix_on_cond_jfc' \<rho> (F::'a::{subpcpo_partition,cont_pt} \<Rightarrow> 'a) \<Longrightarrow> fix_on_cond_jfc' (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> F)"
  apply (erule fix_on_cond_jfc'.induct)
  apply (rule fix_on_cond_jfc'I)
  apply (erule cont_eqvt)
  apply (erule_tac x = i in meta_allE) 
  apply (drule compatible_eqvt[where \<pi> = \<pi>], perm_simp, assumption)
  done

lemma fix_join_compat''_eqvt:
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}"
  assumes "fix_on_cond_jfc' \<rho> F"
  shows "\<pi> \<bullet> fix_join_compat'' \<rho> F = fix_join_compat'' (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> F)"
proof-
  show ?thesis
    apply (auto simp add: permute_set_eq)
    apply (subst (asm) perm_cont_simp[symmetric, of _ _ \<pi>])
    apply (subst (asm) fix_on_eqvt[OF fix_on_cond_jfc''[OF assms(1), unfolded bottom_of_jfc'']])
    apply simp
    apply perm_simp
    apply assumption
    
    apply (subst  perm_cont_simp[symmetric, of _ _ "\<pi>"])
    apply (subst  fix_on_eqvt[OF fix_on_cond_jfc''[OF assms(1), unfolded bottom_of_jfc'']])
    apply simp
    apply perm_simp
    apply assumption
    done
qed

lemma heapExtendJoin_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtendJoin \<rho> h eval = heapExtendJoin (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "heapExtendJoin_cond' h eval \<rho>")
  case True
  hence True_permuted: "heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
    by -(drule fix_on_cond_jfc'_eqvt[where \<pi> = \<pi>], perm_simp, assumption)

  show ?thesis
   unfolding heapExtendJoin_def
   apply (simp only: if_P[OF True] if_P[OF True_permuted])
   apply (subst fix_on_eqvt[OF fix_on_cond_jfc''[OF True]])
   apply (subst bottom_of_eqvt[OF subpcpo_jfc''])
   apply (subst fix_join_compat''_eqvt[OF True])
   apply perm_simp
   apply rule
   done
next
case False 
  hence False_permuted: "\<not> heapExtendJoin_cond' (\<pi> \<bullet> h) (\<pi> \<bullet> eval) (\<pi> \<bullet> \<rho>)"
    apply -
    apply rule
    apply (erule notE)
    apply (drule fix_on_cond_jfc'_eqvt[where \<pi> = "- \<pi>"])
    apply perm_simp
    by (metis (no_types) eqvt_bound pemute_minus_self unpermute_def)
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
  by (auto cong:heapToEnv_cong)

lemma heapExtendJoin_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ; (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtendJoin env1 heap1 eval1 = heapExtendJoin env2 heap2 eval2"
  unfolding heapExtendJoin_def
  by (auto cong:heapToEnv_cong)


lemma heapToEnv_remove_Cons_fmap_expand:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> fmap_expand (heapToEnv ((x, e) # \<Gamma>) eval) S = fmap_expand (heapToEnv \<Gamma> eval) S"
  apply (rule fmap_eqI)
  apply simp
  apply (subgoal_tac "xa \<noteq> x")
  apply (case_tac "xa \<in> fst`set \<Gamma>")
  apply simp
  apply simp
  apply auto
  done

lemma fdom_fix_join_compat'':
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat'' \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_jfc'' fmap_below_dom subpcpo.bottom_of_minimal subpcpo_jfc'' to_bot_minimal)

(*
lemma HSem_add_fresh:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> eval \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x,e) # \<Gamma>) eval \<rho>"
  assumes fresh: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* \<Gamma>"
  assumes step: "\<And>e \<rho>1' \<rho>2'. e \<in> snd ` set \<Gamma> \<Longrightarrow> fdom \<rho>1' = fdom \<rho>1 \<Longrightarrow> fdom \<rho>2' = fdom \<rho>2 \<Longrightarrow> \<rho>1 \<le> \<rho>2 \<Longrightarrow> eval e \<rho>1' = eval e \<rho>2'"
  shows  "heapExtendJoin \<rho> \<Gamma> eval \<le> heapExtendJoin \<rho> ((x, e) # \<Gamma>) eval"
proof (rule parallel_heapExtendJoin_ind[OF cond1 cond2])
case goal1 show ?case by (auto intro:adm_is_adm_on)
case goal2 show ?case by (auto simp add: heapVars_def)[1]
*)

lemma heapExtendJoin_add_fresh:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> eval \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x,e) # \<Gamma>) eval \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>,\<Gamma>)"
  assumes step: "\<And>e \<rho>'. fdom \<rho>' = fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>) \<Longrightarrow> e \<in> snd ` set \<Gamma> \<Longrightarrow> eval e \<rho>' = eval e (fmap_restr (fdom \<rho>' - {x}) \<rho>')"
  shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (heapExtendJoin \<rho> ((x, e) # \<Gamma>) eval) = heapExtendJoin \<rho> \<Gamma> eval"
proof (rule parallel_heapExtendJoin_ind[OF cond1 cond2])
case goal1 show ?case by (auto intro:adm_is_adm_on)
case goal2 show ?case by (auto simp add: heapVars_def)[1]
case goal3
  have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))) = fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)"
    unfolding heapVars_def
    apply (subst fmap_restr_fmap_expand2)
    by auto
  moreover

  have "x \<notin> fdom \<rho> \<union> fst ` set \<Gamma>"
    using fresh
    apply (auto simp add: sharp_Env fresh_Pair)
    by (metis fresh_PairD(1) fresh_list_elem not_self_fresh)
  hence [simp]:"fdom z - {x} = fdom \<rho> \<union> fst ` set \<Gamma>"
    using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond2] goal3(2)]
    by auto

  have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. eval e z)) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))
    =  fmap_expand (heapToEnv \<Gamma> (\<lambda>e. eval e y)) (fdom \<rho> \<union> fst ` set \<Gamma>) "
    unfolding heapVars_def
    apply (subst fmap_restr_fmap_expand2)
      apply simp
      apply auto[1]
    apply (subst heapToEnv_remove_Cons_fmap_expand[OF _ `x \<notin> fdom \<rho> \<union> fst \` set \<Gamma>`])
      apply simp
    apply (rule arg_cong[OF heapToEnv_cong[OF refl]])
    apply (subst step)
    using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond2] goal3(2)] apply simp
    apply assumption
    using `_ = y`[symmetric]
    apply (simp add: heapVars_def)
    done
  ultimately
  show ?case
    apply (subst fmap_restr_join[OF _ rho_F_compat_jfc''[OF cond2 `z \<in> _`]])
    by simp+
qed


end
