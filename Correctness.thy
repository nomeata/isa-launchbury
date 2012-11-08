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
  refinesI: "(\<And> x e. (x, e) \<in> set \<Gamma> \<Longrightarrow> x \<in> fdom \<rho> \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>fmap_expand \<rho> (fdom \<rho> \<union> fst `set \<Gamma>)\<^esub>) \<Longrightarrow> refines \<Gamma> \<rho>"

lemma refinesD:
  assumes "refines \<Gamma> \<rho>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "x \<in> fdom \<rho>"
  shows "the (lookup \<rho> x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>fmap_expand \<rho> (fdom \<rho> \<union> fst `set \<Gamma>)\<^esub>"
using assms by (metis refines.simps)

lemma refinesD':
  assumes "refines \<Gamma> \<rho>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "x \<in> fdom \<rho> \<union> fst ` set \<Gamma>"
  shows "the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> fst `set \<Gamma>)) x) \<sqsubseteq> \<lbrakk>e\<rbrakk>\<^bsub>fmap_expand \<rho> (fdom \<rho> \<union> fst `set \<Gamma>)\<^esub>"
  using assms
  apply (cases "x \<in> fdom \<rho>")
  apply (auto dest: refinesD)
  done

lemma compatible_fmap_expand:
  assumes "\<And> x. x \<in> fdom \<rho>1 \<Longrightarrow> x \<in> fdom \<rho>2 \<Longrightarrow> compatible (the (lookup \<rho>1 x)) (the (lookup \<rho>2 x))"
  shows "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
  apply (case_tac "finite S")
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto simp add: assms fmap_expand_nonfinite)
  done

lemma refines_is_heapExtendJoin_cond:
  assumes "refines \<Gamma> \<rho>"
  shows "heapExtendJoin_cond' \<Gamma> ESem \<rho>" (is "fix_on_cond_jfc' ?\<rho> ?F")
proof (rule fix_on_cond_jfc'I[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]]])
  fix i
  have compat: "compatible ?\<rho> (?F ?\<rho>)"
    apply (rule compatible_fmap_expand)
    apply simp
    apply (rule ub_implies_compatible[OF _ below_refl])
    apply (erule lookupHeapToEnvE)
    apply (rule below_trans)
    apply (erule (1) refinesD[OF assms])
    apply simp
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
    apply (erule (1) refinesD[OF assms])
    apply simp
    apply (rule cont2monofunE[OF ESem_cont join_above1[OF Suc]])
    done
  qed
qed


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z" and "refines \<Gamma> \<rho>" and "fdom \<rho> \<subseteq> set L"
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
  note Application.hyps(10,11,12)[OF `refines \<Gamma> \<rho>` `fdom \<rho> \<subseteq> set (x # L)`]
  note Application.hyps(14,15,16)[OF `refines \<Delta> \<rho>` `fdom \<rho> \<subseteq> set L`]
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
  have xnot2: "x \<notin> fst ` set \<Delta>" sorry

  assume "refines \<Gamma> \<rho>"
  have "refines (removeAll (x, e) \<Gamma>) \<rho>" sorry
  assume "fdom \<rho> \<subseteq> set L" 

  note hyps = Variable.hyps(3-5)[OF `refines (removeAll (x, e) \<Gamma>) \<rho>` `fdom \<rho> \<subseteq> set L`]

  from `refines \<Delta> \<rho>`
  have "refines ((x, z) # \<Delta>) \<rho>" sorry

  have cond: "heapExtendJoin_cond' \<Gamma> ESem \<rho>"
    by (rule refines_is_heapExtendJoin_cond, fact)

  have cond: "heapExtendJoin_cond' ((x, e) # removeAll (x, e) \<Gamma>) ESem \<rho>"
    (* simple consequence of set being equals *)
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
    apply (rule below_trans[OF refinesD'[OF  `refines ((x, z) # \<Delta>) \<rho>`, simplified]])
    apply auto[2]
    apply (rule cont2monofunE[OF ESem_cont HSem_refines[OF cond2, simplified]])
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
 
  note hyps = Let.hyps(4-6)[OF `refines (asToHeap as @ \<Gamma>) \<rho>` `fdom \<rho> \<subseteq> set L`]

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

