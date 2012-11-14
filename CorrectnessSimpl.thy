theory CorrectnessSimpl
  imports "Denotational-Props" LaunchburySimpl
begin

lemma preserve_meaning:
  assumes "\<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z"
  and "distinctVars \<Gamma>"
  and "x \<in> set L"
  and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  shows "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
proof(cases "x \<in> heapVars \<Gamma>")
case True
  thus ?thesis
  using fmap_less_eqD[OF `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`, of x] 
  by (auto simp add: heapVars_def)
next
case False with reds_avoids_live[OF assms(1-3)]
  have "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)" and "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)"
    by (auto intro:  the_lookup_HSem_other simp add: heapVars_def)
  thus ?thesis by simp
qed

inductive refines where
  refinesI: "heapExtendJoin_cond' \<Gamma> ESem \<rho> \<Longrightarrow> (\<And> x e. (x, e) \<in> set \<Gamma> \<Longrightarrow> x \<in> fdom \<rho> \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)
      \<Longrightarrow> refines \<Gamma> \<rho>"

lemma refinesD:
  assumes "refines \<Gamma> \<rho>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "x \<in> fdom \<rho>"
  shows "the (lookup \<rho> x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
using assms
 by (metis refines.simps)

lemma refinesD':
  assumes "refines \<Gamma> \<rho>"
  assumes "finite S"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "x \<in> fdom \<rho> \<union> S"
  shows "the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> S)) x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
  using assms
  apply (cases "x \<in> fdom \<rho>")
  apply (auto dest: refinesD)
  done


lemma refines_is_heapExtendJoin_cond:
  assumes "refines \<Gamma> \<rho>"
  shows "heapExtendJoin_cond' \<Gamma> ESem \<rho>" (is "fix_on_cond_jfc' ?\<rho> ?F")
  using assms
 by (metis refines.simps)
(*
proof (rule fix_on_cond_jfc'I[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]]])
  fix i
  have compat: "compatible ?\<rho> (?F ?\<rho>)"
    apply (rule compatible_fmap_expand)
    apply simp
    apply (rule ub_implies_compatible[OF _ below_refl])
    apply (erule lookupHeapToEnvE)
    apply (rule below_trans)
    apply (erule (1) refinesD[OF assms,rotated, of _  _"fst ` set \<Gamma>"])
    apply simp+
    done
  show "compatible ?\<rho> (?F (((\<lambda> \<rho>'. ?\<rho> \<squnion> ?F \<rho>')^^i) (to_bot ?\<rho>)))"
  proof(induct i)
  case 0 show ?case
    apply simp
    apply (rule ub_implies_compatible[of _ "?\<rho> \<squnion> ?F ?\<rho>"])
    apply (rule join_above1[OF compat])
    apply (rule below_trans[OF _ join_above2[OF compat]])
    apply (rule cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] to_bot_minimal])
    done
  case (Suc i)
    show ?case
    apply (rule compatible_fmap_expand)
    apply simp
    apply (rule ub_implies_compatible[OF _ below_refl])
    apply (erule lookupHeapToEnvE)
    apply (rule below_trans)
    apply (erule (1) refinesD[OF assms,rotated, of _  _"fst ` set \<Gamma>"])
    apply simp
    apply simp
    apply (rule cont2monofunE[OF ESem_cont join_above1[OF Suc]])
    done
  qed
qed
*)

(*
lemma refines_subsetD:
  "refines \<Gamma> \<rho> \<Longrightarrow> set \<Delta> \<subseteq> set \<Gamma> \<Longrightarrow> refines \<Delta> \<rho>"
  apply (rule refinesI)
  apply (drule refines_is_heapExtendJoin_cond)
  apply (frule (1) subsetD)
  apply (drule (3) refinesD)
  apply assumption
  done
*)


lemma the_lookup_HSem:
  assumes "refines \<Gamma> \<rho>"
  assumes "(x, e) \<in> set \<Gamma>"
  shows "the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x) = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> "
proof-
  have [simp]: "x \<in> fst ` set \<Gamma>" using assms(2)  by (metis fst_eqD image_iff)
  have [simp]: "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)) x) =  \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    (* Need distinctness here *)
    sorry
  show ?thesis
    apply (subst HSem_unroll[OF refines_is_heapExtendJoin_cond[OF assms(1)]])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF refines_is_heapExtendJoin_cond[OF assms(1)] HSem_there[OF refines_is_heapExtendJoin_cond [OF assms(1)]]]])
    apply simp
    apply (rule larger_is_join)
    apply (rule refinesD'[OF assms(1) _ assms(2)])
    apply auto
    done
qed


lemma compatible_fmap_expand:
  assumes "\<And> x. x \<in> fdom \<rho>1 \<Longrightarrow> x \<in> fdom \<rho>2 \<Longrightarrow> compatible (the (lookup \<rho>1 x)) (the (lookup \<rho>2 x))"
  shows "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
  apply (case_tac "finite S")
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto simp add: assms fmap_expand_nonfinite)
  done


lemma HSem_commutes:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> ESem \<rho>" (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
  assumes cond2: "heapExtendJoin_cond' \<Gamma> ESem (F \<rho>)" (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
  assumes cont: "cont F"
  assumes fdom[simp]: "\<And> \<rho>' . fdom \<rho>' = fdom \<rho> \<union> fst ` set \<Gamma> \<Longrightarrow> fdom (F \<rho>') = fdom (F \<rho>) \<union> fst ` set \<Gamma>"
  assumes start: "F (fmap_bottom (fdom \<rho> \<union> fst ` set \<Gamma>)) \<sqsubseteq> fmap_expand (F \<rho>) (fdom (F \<rho>) \<union> fst ` set \<Gamma>)"
  assumes comp_step: "\<And> \<rho>' . \<rho>' \<in> fix_join_compat'' ?\<rho>1 ?F1 \<Longrightarrow> compatible ?\<rho>2 (?F2 (F \<rho>'))"
  assumes step: "\<And> \<rho>' . \<rho>' \<in> fix_join_compat'' ?\<rho>1 ?F1 \<Longrightarrow> F (?\<rho>1 \<squnion> ?F1 \<rho>') = ?\<rho>2 \<squnion> ?F2 (F \<rho>')"
  shows "F (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>(F \<rho>)"
proof (rule below_antisym)
  (*
  have "heapExtendJoin_cond' \<Gamma> ESem (F \<rho>)"
    apply (rule fix_on_cond_jfc'I)  
    apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]])
    apply (induct_tac i)
    apply simp
    apply (rule compatible_down_closed2[OF comp_step cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]]],
        of "fmap_bottom (fdom \<rho> \<union> fst ` set \<Gamma>)"])
    apply (metis (no_types) fdom_HSem fdom_fmap_expand finite_fdom fjc''_iff to_bot_fix_on to_bot_fmap_def to_bot_idem to_bot_minimal)
    apply (simp add: to_bot_fmap_def)

    apply (rule compatible_down_closed2[OF comp_step cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]]]])

    apply (rule comp_step)
    thm compatible_down_closed2 

    oops

  { fix \<rho>'
    have "\<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho> \<longrightarrow> F \<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>(F \<rho>)"
    unfolding HSem_def'[OF cond1] HSem_def'[OF cond2]
    apply (rule parallel_fix_on_ind[OF fix_on_cond_jfc''[OF cond1] fix_on_cond_jfc''[OF cond2]])
    apply (rule adm_is_adm_on)
      apply (intro adm_lemmas cont cont2cont)
    sorry
  }
  *)
  show "\<lbrace>\<Gamma>\<rbrace>(F \<rho>) \<sqsubseteq> F (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    apply (subst HSem_def)
    apply (rule heapExtendJoin_ind'[OF cond2])
    apply (auto intro!: adm_is_adm_on adm_subst[OF `cont F`])[1]
    apply rule
    apply (simp add: to_bot_fmap_def)
    apply (subst HSem_unroll[OF cond1])
    apply (subst step[OF HSem_there[OF cond1]])
    apply (erule join_mono[OF rho_F_compat_jfc''[OF cond2 _] comp_step[OF HSem_there[OF cond1]]  below_refl])
    apply (erule cont2monofunE[OF cont_F_jfc''[OF cond2]])
    done

  show "F (\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>(F \<rho>)"
    apply (subst HSem_def)
    apply (rule heapExtendJoin_ind'[OF cond1])
    apply (auto intro!: adm_is_adm_on adm_subst[OF `cont F`])[1]
    apply (subst HSem_unroll[OF cond2])

    apply (rule below_trans[OF _ join_above1[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]]])
    apply (simp add: to_bot_fmap_def)
    apply (rule start)
   
    apply (subst step, assumption)
    apply (subst HSem_unroll[OF cond2])
    apply (rule join_mono[OF rho_F_compat_jfc''[OF cond2 ] rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]] below_refl])
      apply (simp add: HSem_def'[OF cond2] bottom_of_jfc'')
    apply (erule cont2monofunE[OF cont_F_jfc''[OF cond2]])
    done
qed

lemma HSem_commutes_fmap_upd:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> ESem \<rho>" (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
  assumes cond2: "heapExtendJoin_cond' \<Gamma> ESem (\<rho>(x f\<mapsto> v))"
  assumes "x \<notin> fst ` set \<Gamma>"
  assumes "\<And> \<rho>' e. \<rho>' \<in> fix_join_compat'' ?\<rho>1 ?F1 \<Longrightarrow> e \<in> snd `set \<Gamma> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'(x f\<mapsto> v)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>)(x f\<mapsto> v) = \<lbrace>\<Gamma>\<rbrace>(\<rho>(x f\<mapsto> v))"
oops
(*
proof (rule HSem_commutes[OF assms(1) assms(2) fmap_upd_cont[OF cont_id cont_const]])
case goal1 thus ?case by simp
next
case goal2 thus ?case by (rule fmap_upd_below, simp_all)[1]
next
{
case goal3 show ?case 
  proof(rule compatible_fmap_expand)
    case (goal1 xa) thus ?case
      apply (cases "xa = x")
      apply (simp add: assms(3))
      apply (simp add: heapToEnv_cong[OF refl assms(4)[OF goal3(1)]])
      using the_lookup_compatible[OF goal3(2), of xa]
      by simp
  qed
} note compat = this
case goal4 show ?case
  proof (rule fmap_eqI)
  case goal1 show ?case
      apply (subst fmap_upd_fdom)
      apply (subst fdom_join[OF rho_F_compat_jfc''[OF cond1 goal4(1)]])
      apply (subst fdom_join[OF compat[OF goal4(1) rho_F_compat_jfc''[OF cond1 goal4(1)]]])
      apply simp
      done
  case (goal2 xa)
    hence "xa = x \<or> (xa \<noteq> x \<and> xa \<in> fdom \<rho> \<union> fst ` set \<Gamma>)"
      by (auto simp add: fdom_join[OF rho_F_compat_jfc''[OF cond1 goal4(1)]])
    thus ?case
      apply (rule disjE)
      apply (subst the_lookup_join[OF compat[OF goal4(1) rho_F_compat_jfc''[OF cond1 goal4(1)]]])
      apply (simp add: assms(3))

      apply (subst the_lookup_join[OF compat[OF goal4(1) rho_F_compat_jfc''[OF cond1 goal4(1)]]])
      apply simp
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 goal4(1)]])
      apply (simp add: heapToEnv_cong[OF refl assms(4)[OF goal4(1)]])
      apply (cases "xa \<in> fdom \<rho>")
      apply (cases "xa \<in> fst ` set \<Gamma>")
      apply simp
      apply simp
      apply (cases "xa \<in> fst ` set \<Gamma>")
      apply simp
      apply simp
    done
  qed      
qed
*)

lemma ESem_HSem_unused:
  shows "supp (fst ` set \<Delta>) \<sharp>* e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>" and True
proof(nominal_induct e and avoiding: \<Delta> \<rho> rule:exp_assn.strong_induct)
print_cases
case (Var x \<Delta> \<rho>)
  have "\<not>(atom x \<sharp> Var x)"  by (simp add: fresh_def exp_assn.supp supp_at_base)
  hence  "atom x \<notin> supp (fst ` set \<Delta>)" using Var(1) by (auto simp add: fresh_star_def)
  hence "x \<notin> fst ` set \<Delta>" by (metis finite_imageI finite_set image_eqI supp_finite_set_at_base)
  thus ?case by (simp add: the_lookup_HSem_other)
next
case (App e x \<Delta> \<rho>)
  have "\<not>(atom x \<sharp> App e x)"  by (simp add: fresh_def exp_assn.supp supp_at_base)
  hence  "atom x \<notin> supp (fst ` set \<Delta>)" using App(2) by (auto simp add: fresh_star_def)
  hence "x \<notin> fst ` set \<Delta>" by (metis finite_imageI finite_set image_eqI supp_finite_set_at_base)
  hence "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>" by (simp add: the_lookup_HSem_other)
  moreover
  have "supp (fst ` set \<Delta>) \<sharp>* e" using App(2) by (metis exp_assn.fresh(2) fresh_star_def)
  ultimately
  show ?case using App(1) by auto
next
case (Let as e \<Delta> \<rho>)
  {
    fix a :: atom 
    assume "a \<in> supp (fst ` set \<Delta>)"
    hence "a \<in> supp \<Delta>"
      by (induct \<Delta>, auto simp add:supp_set_empty supp_of_finite_insert supp_Cons supp_Pair)
    hence "\<not> (a \<sharp> \<Delta>)"
      by (simp add: fresh_def )
    with Let(1)
    have "a \<notin> set (bn as)"
      by (auto simp add: fresh_star_def)
  }
  hence "supp (fst ` set \<Delta>) \<sharp>* e" and "supp (fst ` set \<Delta>) \<sharp>* as"
    using Let(5) 
    by (simp add: exp_assn.fresh fresh_star_def)+
  note hyps = Let.hyps(4)[OF this(1)]

  have "set (bn as) \<sharp>* (\<lbrace>\<Delta>\<rbrace>\<rho>)"
    by (rule fresh_star_fun_eqvt_app2[OF HSem_eqvt `set (bn as) \<sharp>* \<Delta>` `set (bn as) \<sharp>* \<rho>`])

  note `supp (fst \` set \<Delta>) \<sharp>* as`  `set (bn as) \<sharp>* \<Delta>`
  have "\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<lbrace>asToHeap as\<rbrace>\<rho>"
    apply (subst (2 3) HSem_def')
    prefer 3
    apply (rule parallel_fix_on_ind[OF  fix_on_cond_jfc'' fix_on_cond_jfc''])
    defer
    defer
    apply (rule adm_is_adm_on)
    defer
    apply (simp add: bottom_of_jfc'' to_bot_fmap_def)
  sorry    
    
  hence "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (auto intro: hyps)
  thus ?case
    using `set (bn as) \<sharp>* (\<lbrace>\<Delta>\<rbrace>\<rho>)` `set (bn as) \<sharp>* \<rho>`
    by simp
next
case (Lam v e \<Delta> \<rho>)
  {
    fix a :: atom 
    assume "a \<in> supp (fst ` set \<Delta>)"
    hence "a \<in> supp \<Delta>"
      by (induct \<Delta>, auto simp add:supp_set_empty supp_of_finite_insert supp_Cons supp_Pair)
    hence "\<not> (a \<sharp> \<Delta>)"
      by (simp add: fresh_def )
    with Lam(1)
    have "a \<noteq> atom v"
      by (auto simp add: fresh_star_def)
  }
  hence "supp (fst ` set \<Delta>) \<sharp>* e"
    using Lam(4)
    by (simp add: exp_assn.fresh fresh_star_def)
  note hyps = Lam.hyps(3)[OF this]

  have "atom v \<sharp> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
    by (rule fresh_fun_eqvt_app2[OF HSem_eqvt `atom v \<sharp> \<Delta>` `atom v \<sharp> \<rho>`])
  { fix x
    have "(\<lbrace>\<Delta>\<rbrace>\<rho>)(v f\<mapsto> x) = \<lbrace>\<Delta>\<rbrace>(\<rho>(v f\<mapsto> x))" sorry

    hence "\<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(v f\<mapsto> x)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(v f\<mapsto> x)\<^esub>"
      by (auto intro: hyps)
  }
  thus ?case
    using `atom v \<sharp> (\<lbrace>\<Delta>\<rbrace>\<rho>)` `atom v \<sharp> \<rho>`
    by simp

oops

lemma HSem_HSem:
  "\<lbrace>\<Delta>\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
  (* Need conditions that \<Gamma> does not use \<Delta> *)
  sorry

lemma HSem_le_append:
  "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
  (* Need same conditions that \<Gamma> does not use \<Delta> *)
  sorry


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z"
  and "refines \<Gamma> \<rho>"
  and "distinctVars \<Gamma>"
  and "fdom \<rho> \<subseteq> set L"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" and "refines \<Delta> \<rho>"
  using assms
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
case (Lambda \<Gamma> x e L \<rho>)
  case 1 show ?case by simp
  case 2 show ?case by simp
  case 3 show ?case by fact
next

case (Application y \<Gamma> e x L \<Delta> \<Theta> z S e' \<rho>)
  case 1
  have "fdom \<rho> \<subseteq> set (x # L)" by (metis `fdom \<rho> \<subseteq> set L` set_subset_Cons subset_trans)
  note Application.hyps(11-13)[OF `refines \<Gamma> \<rho>`  `distinctVars \<Gamma>` `fdom \<rho> \<subseteq> set (x # L)`]
  note reds_pres_distinctVars[OF Application.hyps(10) `distinctVars \<Gamma>`]
  note Application.hyps(15-17)[OF `refines \<Delta> \<rho>` `distinctVars \<Delta>` `fdom \<rho> \<subseteq> set L`]
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (subst preserve_meaning[OF `\<Gamma> : e \<Down>\<^bsub>x # L;S\<^esub> \<Delta> : Lam [y]. e'` `distinctVars \<Gamma>` _ `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`], auto) also
  have "... = (\<Lambda> v. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> v)\<^esub>)\<cdot>(\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` by simp also
  have "... = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> (\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))\<^esub>"
    by simp also
  have "... = \<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` and `atom y \<sharp> x`
    by-(rule ESem_subst, simp_all add:fresh_at_base) also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>_\<^esub> = _` by simp
  finally
  show ?case .
  case 2 show ?case using `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> _` `\<lbrace>\<Delta>\<rbrace>\<rho> \<le> _`  by simp
  case 3 show ?case by fact
next

case (Variable x e \<Gamma> S L \<Delta> z \<rho>)
  assume "refines \<Gamma> \<rho>"
  assume "fdom \<rho> \<subseteq> set L"
  assume "distinctVars \<Gamma>"

  note hyps = Variable.hyps(4-6)[OF `refines \<Gamma> \<rho>` `distinctVars \<Gamma>` `fdom \<rho> \<subseteq> set L`]

  have cond: "heapExtendJoin_cond' \<Gamma> ESem \<rho>"
    by (rule refines_is_heapExtendJoin_cond, fact)

  have cond2: "heapExtendJoin_cond' \<Delta> ESem \<rho>"
    by (rule refines_is_heapExtendJoin_cond, fact)

  let "?S" = "(fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>))
       (\<lambda>\<rho>'a. fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'a\<^esub>))
               (fdom \<rho> \<union> fst ` set \<Gamma>)))"
  let "?S2" = "(fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Delta>))
       (\<lambda>\<rho>'a. fmap_expand (heapToEnv \<Delta> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'a\<^esub>))
               (fdom \<rho> \<union> fst ` set \<Delta>)))"
   
  have *: "\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>(x, z) # removeAll (x, e) \<Delta>\<rbrace>\<rho>" sorry

  case 2
    have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" by (rule hyps)
    also have "... = \<lbrace>(x, z) # removeAll (x, e) \<Delta>\<rbrace>\<rho>" by fact
    finally
    show ?case.

  case 1
  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x)" by simp
  also
  have "... = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule the_lookup_HSem[OF `refines \<Gamma> \<rho>` `(x, e) \<in> set \<Gamma>`])
  also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    using hyps by simp
  also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x, z) # removeAll (x, e) \<Delta>\<rbrace>\<rho>\<^esub>" by (simp add: * )
  finally show ?case.

  from `refines \<Delta> \<rho>`
  show "refines ((x, z) # removeAll (x, e) \<Delta>) \<rho>" sorry

next

case (Let as \<Gamma> L body S \<Delta> z \<rho>)
  assume "fdom \<rho> \<subseteq> set L"
  note `set (bn as) \<sharp>* L`
  hence "set (bn as) \<sharp>* set L"  by (metis fresh_star_set)
  hence "set (bn as) \<sharp>* fdom \<rho>"
    by (rule fresh_star_subset[OF finite_set _ `fdom \<rho> \<subseteq> set L`])
  hence "set (bn as) \<sharp>* \<rho>"
    by (simp add:fresh_def fresh_star_def supp_fmap pure_supp)
  have "set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    by (rule fresh_star_fun_eqvt_app2[OF HSem_eqvt `set (bn as) \<sharp>* \<Gamma>` `set (bn as) \<sharp>* \<rho>`])

  have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>" by (rule HSem_le_append)

  find_theorems ESem "_ \<le> _"

  assume "refines \<Gamma> \<rho>"
  have "refines (asToHeap as @ \<Gamma>) \<rho>"
    apply (rule refinesI)
    defer
    apply auto[1]
    using `set (bn as) \<sharp>* fdom \<rho>` 
    defer
    sorry
  thm HSem_le_append
 
  assume "distinctVars \<Gamma>"
  note distinctVars_append_asToHeap[OF `distinctVars (asToHeap as)` `distinctVars \<Gamma>` `set (bn as) \<sharp>* \<Gamma>`]
  note hyps = Let.hyps(5-7)[OF `refines (asToHeap as @ \<Gamma>) \<rho>` `distinctVars (asToHeap as @ \<Gamma>)` `fdom \<rho> \<subseteq> set L`]

  case 1
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule Esem_simps4[OF `set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)`]) also
  have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_HSem]) also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" by (rule hyps)
  finally show ?case .

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>" by fact also
  have "... \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" by (rule hyps)
  finally show ?case .

  case 3 show ?case by (rule hyps)
qed

end

