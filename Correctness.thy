theory Correctness
  imports "Denotational-Props" Launchbury
begin

lemma preserve_meaning:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and "x \<in> set L"
  and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  shows "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
proof(cases "x \<in> heapVars \<Gamma>")
case True
  thus ?thesis
  using fmap_less_eqD[OF `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`, of x] 
  by (auto simp add: heapVars_def)
next
case False with reds_avoids_live[OF assms(1,2)]
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


lemma refines_insertI:
  assumes "refines \<Gamma> \<rho>"
  assumes "heapExtendJoin_cond' ((x, e) # \<Gamma>) ESem \<rho>"
  assumes "x \<in> fdom \<rho> \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
  shows "refines ((x,e) # \<Gamma>) \<rho>"
proof(rule refinesI[OF assms(2)])
  case (goal1 x' e')
  show ?case
  proof(cases "(x', e') = (x, e)")
  case True
    with goal1 have "x \<in> fdom \<rho>" by auto
    from assms(3)[OF this]
    show ?thesis using True by simp
  next
  case False
    hence "(x', e') \<in> set \<Gamma>" using goal1(1) by auto
    from refinesD[OF assms(1) this goal1(2)]
    show ?thesis
      apply (rule below_trans)
      apply (rule cont2monofunE[OF ESem_cont])
      sorry
(*    apply (rule HSem_mono_subset)
      apply auto
      done *)
  qed
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


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and "refines \<Gamma> \<rho>"
  and "distinctVars \<Gamma>"
  and "fdom \<rho> \<subseteq> set L"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" and "refines \<Delta> \<rho>"
  using assms
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
print_cases
case (Lambda \<Gamma> x e L \<rho>)
  print_cases
  case 1 show ?case by simp
  case 2 show ?case by simp
  case 3 show ?case by fact
next

case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' \<rho>)

  case 1
  have "fdom \<rho> \<subseteq> set (x # L)" by (metis `fdom \<rho> \<subseteq> set L` set_subset_Cons subset_trans)
  note Application.hyps(10,11,12)[OF `refines \<Gamma> \<rho>`  `distinctVars \<Gamma>` `fdom \<rho> \<subseteq> set (x # L)`]
  note reds_pres_distinctVars[OF Application.hyps(9) `distinctVars \<Gamma>`]
  note Application.hyps(14,15,16)[OF `refines \<Delta> \<rho>` `distinctVars \<Delta>` `fdom \<rho> \<subseteq> set L`]
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (subst preserve_meaning[OF `\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. e'` _ `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`], auto) also
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

case (Variable x e \<Gamma> L \<Delta> z \<rho>)
  have xnot1: "x \<notin> fst ` set (removeAll (x, e) \<Gamma>)" sorry
  hence xnot2: "x \<notin> fst ` set \<Delta>"
    by (rule reds_avoids_live[OF `removeAll (x, e) \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z`, unfolded heapVars_def, rotated], simp)

  assume "refines \<Gamma> \<rho>"
  hence "refines (removeAll (x, e) \<Gamma>) \<rho>" sorry (* by (auto intro: refines_subsetD) *)
  assume "fdom \<rho> \<subseteq> set L" 
  hence "fdom \<rho> \<subseteq> set (x # L)" by (metis set_subset_Cons subset_trans)

  assume "distinctVars \<Gamma>"
  hence "distinctVars (removeAll (x, e) \<Gamma>)"
    by (rule distinctVars_removeAll[OF _  `(x, e) \<in> set \<Gamma>`])

  note hyps = Variable.hyps(3-5)[OF `refines (removeAll (x, e) \<Gamma>) \<rho>` `distinctVars (removeAll (x, e) \<Gamma>)` `fdom \<rho> \<subseteq> set (x#L)`]

  thm refinesD[OF `refines \<Gamma> \<rho>` `(x,e) \<in> set \<Gamma>`]

  from `refines \<Delta> \<rho>`
  have "refines ((x, z) # \<Delta>) \<rho>"
    (*
    apply (rule refines_insertI)
    apply (rule below_trans)
    apply (erule (1) refinesD[OF `refines \<Gamma> \<rho>` _ `(x,e) \<in> set \<Gamma>`])
    find_theorems e z
    *)
  sorry

  have cond: "heapExtendJoin_cond' \<Gamma> ESem \<rho>"
    by (rule refines_is_heapExtendJoin_cond, fact)

  have cond: "heapExtendJoin_cond' ((x, e) # removeAll (x, e) \<Gamma>) ESem \<rho>"
    (* simple consequence of set being equal *)
    sorry
  have cond2: "heapExtendJoin_cond' ((x, z) # \<Delta>) ESem \<rho>"
    by (rule refines_is_heapExtendJoin_cond, fact)

  let "?S" = "(fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>)))
       (\<lambda>\<rho>'a. fmap_expand (heapToEnv ((x, e) # removeAll (x, e) \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'a\<^esub>))
               (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))))"
  let "?S2" = "(fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>)))
       (\<lambda>\<rho>'a. fmap_expand (heapToEnv ((x, z) # \<Delta>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'a\<^esub>))
               (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>))))"

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e) # removeAll (x,e) \<Gamma>\<rbrace>\<rho>" sorry also (* Distinctness and reordering lemma needed *)
  have "... = fix_on ?S
     (\<lambda>\<rho>'. (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))))"                           
    by (rule iterative_HSem[OF cond xnot1])
  also
  have "... = fix_on ?S
     (\<lambda>\<rho>'. (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))))"                           
    sorry also (* Unfolding a bit under the fixed point, as in 5.2.1 *)
  have "... = fix_on ?S
     (\<lambda>\<rho>'. (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))))"  
   apply (rule fix_on_cong)
   (* fix_on_cond with bit unfolded *)
   defer
   (* drule for refines in jfc'' *)
   apply (rule arg_cong[OF Variable.hyps(3)])
   defer
   sorry also 
   (*    by (subst  hyps(1), rule refl) also *)
   have "... \<le> fix_on ?S
     (\<lambda>\<rho>'. (\<lbrace>\<Delta>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>))))"
    using Variable.hyps(4)
    (* \<le> and fix1 *)
    sorry also
  have "... = fix_on ?S2
     (\<lambda>\<rho>'. (\<lbrace>\<Delta>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>))(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>))))"
    (* fdoms anpassen *)
    sorry also
  have "... = fix_on ?S2
     (\<lambda>\<rho>'. (\<lbrace>\<Delta>\<rbrace>\<rho>') \<squnion>
            (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>))(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>) \<squnion>
             fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>))))"
    (* Again 5.2.1 *)
    sorry also
  have  "... = \<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>"
    by (rule iterative_HSem[OF cond2  xnot2,symmetric])
  finally show part2: ?case.

  case 1
  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x)" by simp also
  have "... = the (lookup (\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>) x)"
    using part2 (* Definition of \<le> and existence of x in \<Gamma> *)
    sorry also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    apply (subst HSem_unroll[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]])
    apply auto
    apply (rule larger_is_join)
    apply (cases "x \<in> fdom \<rho>")
    apply (rule refinesD'[OF `refines ((x, z) # \<Delta>) \<rho>`, of "fst ` set  ((x, z) # \<Delta>)", simplified])
    apply auto[2]
    apply simp
    done
  finally show ?case.

  case 3 show ?case by fact
next

case (Let as \<Gamma> L body \<Delta> z \<rho>)
  assume "fdom \<rho> \<subseteq> set L"
  note `set (bn as) \<sharp>* L`
  hence "set (bn as) \<sharp>* set L"  by (metis fresh_star_set)
  hence "set (bn as) \<sharp>* fdom \<rho>"
    by (rule fresh_star_subset[OF finite_set _ `fdom \<rho> \<subseteq> set L`])
  hence "set (bn as) \<sharp>* \<rho>"
    by (simp add:fresh_def fresh_star_def supp_fmap pure_supp)
  have "set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    by (rule fresh_star_fun_eqvt_app2[OF HSem_eqvt `set (bn as) \<sharp>* \<Gamma>` `set (bn as) \<sharp>* \<rho>`])

  have "refines (asToHeap as @ \<Gamma>) \<rho>" sorry
 
  assume "distinctVars \<Gamma>"
  note distinctVars_append_asToHeap[OF `distinctVars (asToHeap as)` `distinctVars \<Gamma>` `set (bn as) \<sharp>* \<Gamma>`]
  note hyps = Let.hyps(5-7)[OF `refines (asToHeap as @ \<Gamma>) \<rho>` `distinctVars (asToHeap as @ \<Gamma>)` `fdom \<rho> \<subseteq> set L`]

  case 1
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule Esem_simps4[OF `set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)`]) also
  have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>" sorry also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" by (rule hyps)
  finally show ?case .

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>" sorry also
  have "... \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" by (rule hyps)
  finally show ?case .

  case 3 show ?case by (rule hyps)
qed

end

