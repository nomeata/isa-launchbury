theory CorrectnessStacked
  imports "Denotational-Props" LaunchburyStacked
begin

lemma compatible_fmap_expand:
  assumes "\<And> x. x \<in> fdom \<rho>1 \<Longrightarrow> x \<in> fdom \<rho>2 \<Longrightarrow> compatible (the (lookup \<rho>1 x)) (the (lookup \<rho>2 x))"
  shows "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
  apply (case_tac "finite S")
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto simp add: assms fmap_expand_nonfinite)
  done

lemma fmap_restr_le:
  assumes "\<rho>1 \<le> \<rho>2"
  assumes "S1 \<subseteq> S2"
  assumes [simp]:"finite S2"
  shows "fmap_restr S1 \<rho>1 \<le> fmap_restr S2 \<rho>2"
proof-
  have [simp]: "finite S1"
    by (rule finite_subset[OF `S1 \<subseteq> S2` `finite S2`])
  show ?thesis
  proof (rule fmap_less_eqI)
    have "fdom \<rho>1 \<subseteq> fdom \<rho>2"
      by (metis assms(1) less_eq_fmap_def)
    thus "fdom (fmap_restr S1 \<rho>1) \<subseteq> fdom (fmap_restr S2 \<rho>2)"
      using `S1 \<subseteq> S2`
      by auto
  next
    fix x
    assume "x \<in> fdom (fmap_restr S1 \<rho>1) "
    hence [simp]:"x \<in> fdom \<rho>1" and [simp]:"x \<in> S1" and [simp]: "x \<in> S2"
      by (auto intro: set_mp[OF `S1 \<subseteq> S2`])
    have "the (lookup \<rho>1 x) = the (lookup \<rho>2 x)"
      by (metis `x \<in> fdom \<rho>1` assms(1) less_eq_fmap_def)
    thus "the (lookup (fmap_restr S1 \<rho>1) x) = the (lookup (fmap_restr S2 \<rho>2) x)"
      by simp
  qed
qed


lemma HSem_subst_var_app:
  assumes cond1: "HSem_cond' ((x, App (Var n) y) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, App e y) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes cond1: "HSem_cond' ((x, Var n) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, e) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed


lemma HSem_subset_below:
  assumes cond2: "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
  assumes fresh: "atom ` fst ` set \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
  shows "fmap_expand (\<lbrace>\<Delta>\<rbrace>\<rho>) (fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma>) \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
proof (rule HSem_ind) back
case goal1 show ?case by (auto intro!: adm_is_adm_on adm_subst[OF fmap_expand_cont])
next
case goal2 show ?case by (auto simp add: to_bot_fmap_def)
next
show rho: "fmap_expand (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Delta>)) (fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma>) \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> "
  apply (subst fmap_expand_idem)
  apply auto[3]
  using HSem_refines[OF cond2]
  by (auto simp add: image_Un sup.assoc)

  from fresh
  have "fst`set \<Gamma> \<inter> (fdom \<rho> \<union> fst`set \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct[unfolded heapVars_def] simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma> - (fdom \<rho> \<union> fst ` set \<Delta>) = fst ` set \<Gamma>"
    by auto

case (goal3 x)
  note cond1 = goal3(1)
  have  "fdom x = fdom \<rho> \<union> fst ` set \<Delta>"
    using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond1] goal3(2)]
    by simp
  {
    fix v e
    assume "e \<in> snd` set \<Delta>"
    from fresh_star_heap_expr'[OF _ this]
    have fresh_e: "atom ` fst ` set \<Gamma> \<sharp>* e"
      by (metis fresh fresh_star_Pair)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>fmap_expand x (fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma>)\<^esub>"
      apply (rule ESem_ignores_fresh)
      apply (rule less_fmap_expand)
        using `fdom x = _` apply auto[2]
      apply (simp add: `fdom x = _` fdoms)
      apply (rule fresh_e)
      done
    with goal3(3)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (metis cont2monofunE[OF ESem_cont])
  } note e_less = this

  note compat = rho_F_compat_jfc''[OF cond1 goal3(2)]
  note compat2 = rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]
  show ?case
    apply (subst fmap_expand_join[OF _ compat], simp)
    apply (rule join_below[OF fmap_expand_compatible[OF _ compat] rho], simp)
    apply (subst fmap_expand_idem)
      apply auto[3]
    apply (rule fmap_expand_belowI)
      apply auto[1]
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF compat2])
    apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
    apply (subst lookup_fmap_expand1)
      apply auto[3]
    apply simp
    apply (subst lookupHeapToEnv, assumption)
    apply (subst lookupHeapToEnv)
      apply auto[1]
    apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
    apply (rule e_less)
    by (metis the_map_of_snd)
qed

lemma HSem_merge:
  assumes distinct1: "distinctVars (\<Delta> @ \<Gamma>)"
  assumes fresh: "atom ` fst ` set \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  assumes rho_fresh: "fdom \<rho> \<inter> fst ` set (\<Gamma> @ \<Delta>) = {}"
  shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof(rule below_antisym)
  from distinct1
  have distinct2: "distinctVars (\<Gamma> @ \<Delta>)"
    by (auto simp add: distinctVars_append)

  from fresh
  have Gamma_fresh: "fst`set \<Gamma> \<inter> (fdom \<rho> \<union> fst`set \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct[unfolded heapVars_def] simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma> - (fdom \<rho> \<union> fst ` set \<Delta>) = fst ` set \<Gamma>"
    by auto

  have cond1: "HSem_cond' \<Gamma> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
    apply (rule disjoint_is_HSem_cond)
    using Gamma_fresh by auto
  have cond2: "HSem_cond' (\<Gamma>@\<Delta>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond2': "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond3: "HSem_cond' \<Delta> \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto

  show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind) back
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  have "fmap_expand (\<lbrace>\<Delta>\<rbrace>\<rho>) (fdom \<rho> \<union> fst ` set \<Delta> \<union> fst ` set \<Gamma>) \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_subset_below[OF cond2' fresh])
  also have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
    apply (rule HSem_reorder[OF distinct1 distinct2])
    by auto
  finally
  show Delta_rho: "fmap_expand (\<lbrace>\<Delta>\<rbrace>\<rho>) (fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> fst ` set \<Gamma>) \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
    by simp

  case (goal3 \<rho>')
    note compat = rho_F_compat_jfc''[OF cond1 goal3(2)]
    note compat2 = rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]

    have "fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>\<^esub>)) (fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> fst ` set \<Gamma>) \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> "
    proof (rule fmap_expand_belowI)
    case goal1 thus ?case by auto
    case (goal2 x)
      hence x:"x \<in> fst ` set \<Gamma>" by auto
      thus ?case
        apply (subst lookupHeapToEnv, assumption)
        apply (subst (2) HSem_eq[OF cond2])
        apply (subst the_lookup_join[OF compat2])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        done
    qed       
    thus ?case
      by (rule join_below[OF compat Delta_rho 
          below_trans[OF cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(3)]]])
  qed

  show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
  proof (rule HSem_ind) back back
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case goal2 show ?case by (auto simp add: to_bot_fmap_def)
  next
  have "fmap_expand \<rho> (fdom \<rho> \<union> fst ` set (\<Gamma> @ \<Delta>)) = fmap_expand (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Delta>)) (fdom \<rho> \<union> fst ` set (\<Gamma> @ \<Delta>))"
    by (rule fmap_expand_idem[symmetric], auto)
  also have "... \<sqsubseteq> fmap_expand (\<lbrace>\<Delta>\<rbrace>\<rho>) (fdom \<rho> \<union> fst ` set (\<Gamma> @ \<Delta>))"
    by (rule cont2monofunE[OF fmap_expand_cont HSem_refines[OF cond3]])
  also have "... = fmap_expand (\<lbrace>\<Delta>\<rbrace>\<rho>) (fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> fst ` set (\<Gamma>))"
    apply (rule arg_cong) back
    by auto
  also have "... \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    by (rule HSem_refines[OF cond1])
  finally
  show rho: "fmap_expand \<rho> (fdom \<rho> \<union> fst ` set (\<Gamma> @ \<Delta>)) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> ".

  case (goal3 \<rho>')
    note compat = rho_F_compat_jfc''[OF cond2 goal3(2)]
    note compat2 = rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]
    note compat3 = rho_F_compat_jfc''[OF cond3 HSem_there[OF cond3]]

    have "fmap_expand (heapToEnv (\<Gamma> @ \<Delta>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)) (fdom \<rho> \<union> fst ` set (\<Gamma> @ \<Delta>)) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    proof (rule fmap_expand_belowI)
    case goal1 thus ?case by auto
    case (goal2 x)
      hence "x \<in> fst ` set \<Gamma> \<or> (x \<notin> fst ` set \<Gamma> \<and> x \<in> fst ` set \<Delta>)" by auto      
      thus ?case
      proof
        assume x: "x \<in> fst ` set \<Gamma>"
        thus ?thesis
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (subst (2) HSem_eq[OF cond1])
        apply (subst the_lookup_join[OF compat2])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat2]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv, assumption)
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        done
      next
        assume x: "x \<notin> fst ` set \<Gamma> \<and> x \<in> fst ` set \<Delta>"
        hence [simp]:"x \<notin> fst ` set \<Gamma>" and  "x \<in> fst ` set \<Delta>" by auto
        from this(2)
        show ?thesis
        apply (subst lookupHeapToEnv)
          apply auto[1]
        apply (subst the_lookup_HSem_other)
          apply simp
        apply (subst (2) HSem_eq[OF cond3])
        apply (subst the_lookup_join[OF compat3])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_compatible[OF compat3]]])
        apply (subst lookup_fmap_expand1)
          using x apply auto[3]
        apply (subst lookupHeapToEnv, assumption)
        apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
        apply (rule eq_imp_below)
        apply (rule ESem_ignores_fresh[symmetric])
        apply (rule HSem_disjoint_less)
          using Gamma_fresh apply auto[1]
        apply (simp add: fdoms)
        apply (erule fresh_star_heap_expr'[OF _ the_map_of_snd, rotated])
        by (metis fresh fresh_star_Pair)
      qed  
    qed
    thus ?case
      by (rule join_below[OF compat rho 
          below_trans[OF cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(3)]]])
  qed
qed

lemma HSem_unfold_let:
  assumes cond1: "HSem_cond' ((x, Let as body) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, body) # asToHeap as @ \<Gamma>) \<rho>"
  assumes cond3: "HSem_cond' (asToHeap as @ ((x, body) # \<Gamma>)) \<rho>"
  assumes distinct1: "distinctVars (asToHeap as)"
  assumes distinct2: "distinctVars ((x, body) # \<Gamma>)"
  assumes fresh: "set (bn as) \<sharp>* (x, Let as body, \<Gamma>, \<rho>)"
  assumes too_lazy_to_do_it_for_more_than_fempty: "\<rho> = fempty"
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>"
proof (rule iffD2[OF fmap_less_restrict])
  from fresh
  have fresh_Gamma: "atom ` fst ` set (asToHeap as) \<sharp>* \<Gamma>"
    by (metis fresh_star_Pair heapVars_def set_bn_to_atom_heapVars)

  from fresh
  have "set (bn as) \<sharp>* ((x, Let as body) # \<Gamma>)"
    by (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh fresh_Cons)
  note notInAs = fresh_assn_distinct[OF this]

  from fresh
  have notInRho: "heapVars (asToHeap as) \<inter> fdom \<rho> = {}"
    by (auto simp add: fresh_star_Pair heapVars_def  sharp_star_Env)

  have disjoint: "fst ` set (asToHeap as) \<inter> insert x (fdom \<rho> \<union> fst ` set \<Gamma>) = {}"
    using notInAs notInRho
    by (auto simp add: heapVars_def)
  hence x_not_as: "x \<notin> heapVars (asToHeap as)"
    by (auto simp add: heapVars_def)

  {
    fix x' e
    assume "e \<in> snd ` set \<Gamma>"

    have simp1: " fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<inter> insert x (fdom \<rho> \<union> fst ` set \<Gamma>) = insert x (fdom \<rho> \<union> fst ` set \<Gamma>)"
      by auto

    have simp2: "fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) - insert x (fdom \<rho> \<union> fst ` set \<Gamma>) = fst ` set (asToHeap as)"
      using disjoint
      by (auto simp del: fst_set_asToHeap)

    have fresh_e: "atom ` fst ` set (asToHeap as) \<sharp>* e"
      by (rule fresh_star_heap_expr'[OF fresh_Gamma `_ \<in> snd\` set \<Gamma>`])

    have "\<lbrakk> e \<rbrakk>\<^bsub>fmap_restr (insert x (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      apply (rule ESem_ignores_fresh[OF fmap_restr_less])
      apply (subst fdom_fmap_restr)
        apply simp
      apply (subst simp1)
      apply (subst simp2)
      apply (rule fresh_e)
      done
  } note Gamma_eq = this

case goal1
  have "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> = fmap_restr (insert x (fdom \<rho> \<union> fst`set \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
  proof(rule below_antisym)
    show below: "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> fmap_restr (insert x (fdom \<rho> \<union> fst`set \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
    proof (rule HSem_ind'[OF cond1])
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (auto simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      have fdom: "fdom \<rho>' = insert x (fdom \<rho> \<union> fst ` set \<Gamma>)"
        using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond1] goal3(1)]
        by simp

      hence [simp]: "set (bn as) \<sharp>* \<rho>'"
        using disjoint
        by (auto simp add: heapVars_def set_bn_to_atom_heapVars fresh_star_def sharp_Env simp del: fst_set_asToHeap)

      note compat1 = rho_F_compat_jfc''[OF cond1 goal3(1)]
      note compat2 = rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]
      show ?case
      proof(rule fmap_belowI')
      case goal1 show ?case by (auto simp add: fdom_join[OF compat1, simplified])
      case (goal2 x')
        hence x': "x' \<in> insert x (fdom \<rho> \<union> fst ` set \<Gamma>)"
          by (auto simp add: fdom_join[OF compat1, simplified])

        hence x'_not_as:"x' \<notin> fst ` set (asToHeap as)"
          using disjoint
          by (auto simp add: heapVars_def)

        have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>'\<^esub>" by simp
        also have "... \<sqsubseteq> \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>))\<^esub>"
          apply (rule cont2monofunE[OF ESem_cont])
          apply (rule HSem_mono[OF _ _ goal3(2)])
          apply (rule disjoint_is_HSem_cond)
          apply (subst fdom)
          using disjoint apply auto[1]
          apply (rule disjoint_is_HSem_cond)
          using disjoint apply auto[1]
          done
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<rho>))\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<rho>\<^esub>"
          apply (rule arg_cong) back
          apply (rule HSem_redo[OF cond3, simplified (no_asm)])
          apply (rule disjoint_is_HSem_cond)
          using disjoint apply (auto simp del: fst_set_asToHeap)
          done
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as], symmetric])
        also note x = calculation

        show ?case
          apply (subst lookup_fmap_restr[OF _ x', simplified])
          apply (subst HSem_eq[OF cond2])
          apply (subst the_lookup_join[OF compat1])
          apply (subst the_lookup_join[OF compat2])
          apply (rule join_mono[OF the_lookup_compatible[OF compat1] the_lookup_compatible[OF compat2]])
            using x' apply (cases "x' \<in> fdom \<rho>", simp_all)[1]
          apply (cases "x' \<in> insert x (fst ` set \<Gamma>)")
          defer
            using x' apply simp
          apply (cases "x' = x")
            using x apply simp
          apply (subst lookup_fmap_expand1)
            apply simp_all[3]
          apply (subst lookup_fmap_expand1)
            apply auto[3]
          apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as])
          apply (subst lookupHeapToEnv, assumption)
          apply (subst lookupHeapToEnv, assumption)
          apply (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below])
          apply (erule Gamma_eq[OF the_map_of_snd])
          done
      qed
    qed

    have [simp]: "set (bn as) \<sharp>* (\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>)"
      apply (rule HSem_fresh_star)
      using fresh by (auto simp add: fresh_star_Pair fresh_star_Cons)

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho>"
    proof (rule HSem_below)
    case goal1
      show ?case
        apply (rule fmap_expand_belowI)
          apply (auto simp del: fst_set_asToHeap)[1]
        apply (rule below_trans[OF HSem_refines_lookup[OF cond1]], assumption)
        apply (rule HSem_refines_lookup)
          apply (rule disjoint_is_HSem_cond)
          using disjoint apply (auto simp del: fst_set_asToHeap)[1]
        apply simp
        done
    case (goal2 x')
      have body: "\<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> the (lookup (\<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>) x)"
        apply (subst ESem.simps(4)[symmetric])
        apply simp
        apply (subst the_lookup_HSem_other)
        apply (metis heapVars_def x_not_as)
        apply (rule below_trans[OF eq_imp_below HSem_heap_below[OF cond1]])
        apply auto
        done
      show ?case
        apply (cases "x' = x")
          apply simp
          apply (rule body)
        
        apply (subst (1 2) HSem_merge)
          apply (metis distinct1 distinct2 distinctVars.intros(2) distinctVars_Cons distinctVars_ConsD(1) distinctVars_appendI inf_commute notInAs)
          using fresh apply (metis fresh_star_Pair fresh_star_Cons heapVars_def set_bn_to_atom_heapVars)
          using too_lazy_to_do_it_for_more_than_fempty apply simp
        apply (rule below_trans[OF eq_imp_below HSem_heap_below, rotated])
          apply (rule disjoint_is_HSem_cond) using too_lazy_to_do_it_for_more_than_fempty apply simp
          using goal2 apply simp
        apply (rule arg_cong) back
          apply (cases "x' \<in> fst ` set (asToHeap as)")
          apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst  del: fst_set_asToHeap)
          apply (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst  del: fst_set_asToHeap)
        done
    qed
    thus "fmap_restr (insert x (fdom \<rho> \<union> fst`set \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<rho>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>\<rho>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_HSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>\<rho>", simplified (no_asm)])
      using disjoint apply (auto simp del: fst_set_asToHeap)
      done
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed

theorem correctness:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<lbrace>\<Gamma>'@\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>'@\<Delta>\<rbrace>"
  using assms
proof(induct rule:reds_distinct_ind)
case (Lambda x y e \<Gamma> \<Gamma>')
  show ?case by simp
next

case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z  e')
  let "?restr \<rho>" = "fmap_restr (insert x (heapVars \<Gamma>' \<union> heapVars \<Gamma>)) (\<rho>::Env)"
  let "?restr2 \<rho>" = "fmap_restr (insert x (heapVars \<Delta>' \<union> heapVars \<Delta>)) (\<rho>::Env)"

  have "n \<noteq> z" using Application by (simp add: fresh_Pair fresh_at_base)

  from stack_unchanged[OF distinct_redsD1[OF Application.hyps(8)]]
  have "\<Delta>' = \<Gamma>'" by simp
  hence [simp]:"atom n \<sharp> \<Delta>'"  using Application by (simp add: fresh_Pair)+
  
  have "atom n \<sharp> (\<Gamma>, e)" using Application by (simp add: fresh_Pair)
  note reds_fresh[OF Application(8) this]
  hence "atom n \<sharp> (\<Delta>, Lam [z]. e')"
    using Application(5)
    by (metis (hide_lams, no_types) Application(1) fresh_Pair heapVars_not_fresh)
  with `n \<noteq> z`
  have [simp]: "atom n \<sharp> \<Delta>" "atom n \<sharp> e'"
    by (auto simp add: exp_assn.fresh fresh_Pair)

  note subset1 = reds_doesnt_forget'(1)[OF Application.hyps(8), unfolded append_Cons]
  from reds_doesnt_forget'(2)[OF Application.hyps(8), unfolded append_Cons]
  have subset2: "heapVars ((x, App (Var n) y) # \<Gamma>') \<subseteq> heapVars ((x, App (Var n) y) # \<Delta>')"
    apply (rule distinctVars_Cons_subset)
    apply (metis Application(4) distinctVars_appendD1)
    apply (metis Application(5) distinctVars_appendD1)
    done

  have "n \<noteq> x" 
    by (metis Application(1) fresh_PairD(1) fresh_PairD(2) not_self_fresh)

  have "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> = (\<lbrace>(x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by simp
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    (* Adding a fresh variable *)
    apply (subst HSem_add_fresh[of fempty "(x, App e y) # \<Gamma>' @ \<Gamma>" n e, symmetric])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append exp_assn.fresh)
    apply simp
    done
  also have  "... = ?restr (\<lbrace>(x, App e y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (rule arg_cong[OF HSem_reorder_head[OF `n \<noteq> x`]])
  also
  have "... = ?restr (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    (* Substituting the variable *)
    apply (rule arg_cong[OF HSem_subst_var_app[symmetric]])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... \<le> ?restr2  (\<lbrace>(n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>\<rbrace>)"
    (* Restriction and \<le> *)
    apply (rule fmap_restr_le[OF Application.hyps(9)[simplified]])
    using subset1 subset2 by auto
  also
  have "... \<le> ?restr2  (\<lbrace>(x, App (Var n) y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = ?restr2 (\<lbrace>(x, App (Lam [z]. e') y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    (* Substituting the variable *)
    apply (rule arg_cong[OF HSem_subst_var_app])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr2 (\<lbrace>(n, Lam [z]. e') # (x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = (\<lbrace>(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    (* Removing a fresh variable *)
    apply (subst HSem_add_fresh[of fempty "(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>" n "Lam [z]. e'", symmetric])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append exp_assn.fresh)
    apply simp
    done
  also
  have "... =  \<lbrace>(x, e'[z::=y]) # \<Delta>' @ \<Delta>\<rbrace>"
    (* Denotation of application *)
    apply (rule HSem_subst_exp[OF fempty_is_HSem_cond fempty_is_HSem_cond])
    apply (simp)
    apply (subgoal_tac "atom z \<sharp> \<rho>'")
    apply (subst ESem.simps, assumption)
    apply simp
    apply (rule ESem_subst[simplified])
      using Application(2) apply (auto simp add: fresh_Pair)[1]
      apply assumption
      
      using Application(2)
      apply (subst sharp_Env)
      apply auto[1]
      apply (metis fresh_Pair not_self_fresh)
      apply (metis (hide_lams, no_types) fresh_PairD(1) fresh_PairD(2) fresh_list_elem not_self_fresh)
      apply (metis (hide_lams, no_types) fresh_PairD(1) fresh_PairD(2) fresh_list_elem not_self_fresh)
    done
  also
  have "... \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>" by (rule Application.hyps(11)[simplified])
  finally
  show "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>".

next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have "x \<noteq> y"
    using Variable(3) by (auto simp add: distinctVars_Cons distinctVars_append)
  have "distinctVars \<Gamma>"
    using Variable(2) by (auto simp add: distinctVars_Cons distinctVars_append)

  have "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>\<rbrace>"
    (* Shifting a variable around *)
    apply (rule HSem_reorder[OF Variable.hyps(2,3)])
    using distinctVars_set_delete_insert[OF `distinctVars \<Gamma>` Variable(1)]
    by auto
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>"
    by fact
  also
  have "... =  \<lbrace>(y, z) # (x, Var y) # \<Delta>' @ \<Delta>\<rbrace>"
    by simp
  also
  have "... =  \<lbrace>(x, Var y) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>(x, z) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    (* Substituting a variable *)
    apply (rule HSem_subst_var_var)
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using `x \<noteq> y` by (simp add: fresh_Pair fresh_at_base)
  also
  have "... =  \<lbrace>(y, z) # (x, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>((y, z) # (x, z) # \<Delta>') @ \<Delta>\<rbrace>"
    by simp
  also
  {
  have "distinctVars (((y, z) # (x, z) # \<Delta>') @ \<Delta>)"
    using Variable.hyps(4)
    by (simp add: distinctVars_append distinctVars_Cons)
  }
  hence "... = \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>"
    apply (rule HSem_reorder[OF _ Variable.hyps(5)])
    by auto
  finally
  show "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>".

next
case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  have d1: "distinctVars (asToHeap as @ ((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
    by (metis Let(1) Let(2) Let(3) distinctVars_append_asToHeap fresh_star_Pair fresh_star_list(1) fresh_star_list(2))
  hence d2: "distinctVars ((x, Terms.Let as body) # asToHeap as @ \<Gamma>' @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)
  hence d3: "distinctVars ((x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)
  hence d4: "distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)
  hence d5: "distinctVars ((x, body) # \<Gamma>' @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)

  have "\<lbrace>((x, Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>(x, Let as body) # \<Gamma>' @ \<Gamma>\<rbrace>"
    by simp
  also
  have "... \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>\<rbrace>"
    (* Unrolling a let *)
    apply (rule HSem_unfold_let)
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    apply fact
    apply (rule d5)
    using Let(1) apply (auto simp add: fresh_star_Pair fresh_star_append)[1]
    apply (simp add: fresh_star_def)
    apply rule
    done
  also
  have "... = \<lbrace>((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>\<rbrace>"
    (* Unrolling a let *)
     by (rule HSem_reorder[OF d3 d4], auto)
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>".
qed


end

