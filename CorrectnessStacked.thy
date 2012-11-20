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

lemma heapToEnv_reorder_head:
  assumes "x \<noteq> y"
  shows "heapToEnv ((x,e1)#(y,e2)#\<Gamma>) eval = heapToEnv ((y,e2)#(x,e1)#\<Gamma>) eval"
  by (simp add: fmap_upd_twist[OF assms])

lemma heapToEnv_remove_insert:
  assumes "distinctVars \<Gamma>"
  assumes "(x,e) \<in> set \<Gamma>"
  shows "heapToEnv \<Gamma> eval = heapToEnv ((x,e) # removeAll (x,e) \<Gamma>) eval"
using assms
proof (induct \<Gamma> rule:distinctVars.induct)
  case goal1 thus ?case by simp
next
  case (goal2 y \<Gamma> e2)
  show ?case
  proof(cases "(x,e) = (y,e2)")
  case True
    from `y \<notin> heapVars \<Gamma>`
    have "x \<notin> heapVars \<Gamma>" using True by simp
    hence "removeAll (x, e) \<Gamma> = \<Gamma>" by (rule removeAll_no_there)
    with True show ?thesis by simp
  next
  case False
    hence "x \<noteq> y" by (metis goal2(1) goal2(4) member_remove removeAll_no_there remove_code(1) set_ConsD)
    hence "(x, e) \<in> set \<Gamma>" by (metis False goal2(4) set_ConsD)
    note hyp = goal2(3)[OF this]

    have "heapToEnv ((x, e) # removeAll (x, e) ((y, e2) # \<Gamma>)) eval 
      = heapToEnv ((x, e) # ((y, e2) # removeAll (x, e) \<Gamma>)) eval"
      using False by simp
    also have "... = heapToEnv ((y, e2) # ((x, e) # removeAll (x, e) \<Gamma>)) eval"
      by (rule heapToEnv_reorder_head[OF `x \<noteq> y`])
    also have "... = heapToEnv ((y, e2) # \<Gamma>) eval"
      using hyp
      by simp
    finally
    show ?thesis by (rule sym)
  qed
qed

lemma heapToEnv_reorder:
  assumes "distinctVars \<Gamma>"
  assumes "distinctVars \<Delta>"
  assumes "set \<Gamma> = set \<Delta>"
  shows "heapToEnv \<Gamma> eval = heapToEnv \<Delta> eval"
using assms
proof (induct \<Gamma> arbitrary: \<Delta> rule:distinctVars.induct)
case goal1 thus ?case by simp
next
case (goal2 x \<Gamma> e \<Delta>)
  hence "(x,e) \<in> set \<Delta>"
    by (metis ListMem_iff elem)
  note Delta' = heapToEnv_remove_insert[OF `distinctVars \<Delta>` this]

  have "distinctVars (removeAll (x, e) \<Delta>)" 
    by (rule distinctVars_removeAll[OF goal2(4)  `(x, e) \<in> set \<Delta>`])
  moreover
  from `set ((x, e) # \<Gamma>) = set \<Delta>`
  have "set \<Gamma> = set (removeAll (x, e) \<Delta>)"
    by (metis removeAll.simps(2) removeAll_no_there[OF `x \<notin> heapVars \<Gamma>`] remove_code(1))
  ultimately
  have "heapToEnv \<Gamma> eval = heapToEnv (removeAll (x, e) \<Delta>) eval"
    by (rule goal2(3))
  thus ?case
    by (simp add: Delta')
qed

lemma heapExtendJoin_reorder:
  assumes "distinctVars \<Gamma>"
  assumes "distinctVars \<Delta>"
  assumes "set \<Gamma> = set \<Delta>"
  shows "heapExtendJoin \<rho> \<Gamma> eval = heapExtendJoin \<rho> \<Delta> eval"
by (simp add: heapExtendJoin_def  heapToEnv_reorder[OF assms] assms(3))

lemma heapExtendJoin_reorder_head:
  assumes "x \<noteq> y"
  shows "heapExtendJoin \<rho> ((x,e1)#(y,e2)#\<Gamma>) eval = heapExtendJoin \<rho> ((y,e2)#(x,e1)#\<Gamma>) eval"
proof-
  have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
    by auto
  thus ?thesis      
    unfolding heapExtendJoin_def  heapToEnv_reorder_head[OF assms]
    apply simp
    done
qed

lemma HSem_reorder:
  assumes "distinctVars \<Gamma>"
  assumes "distinctVars \<Delta>"
  assumes "set \<Gamma> = set \<Delta>"
  shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<rho>"
by (simp add: HSem_def heapExtendJoin_reorder[OF assms])

lemma HSem_reorder_head:
  assumes "x \<noteq> y"
  shows "\<lbrace>((x,e1)#(y,e2)#\<Gamma>)\<rbrace>\<rho> = \<lbrace>((y,e2)#(x,e1)#\<Gamma>)\<rbrace>\<rho>"
by (simp add: HSem_def heapExtendJoin_reorder_head[OF assms])

lemma heapToEnv_subst_exp:
  assumes "eval e = eval e'"
  shows "heapToEnv ((x,e)#\<Gamma>) eval = heapToEnv ((x,e')#\<Gamma>) eval"
  by (simp add: assms)


lemma heapExtendJoin_subst_exp:
  assumes cond1: "heapExtendJoin_cond' ((x, e) # \<Gamma>) eval \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x, e') # \<Gamma>) eval \<rho>"
  assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (fst`set ((x,e)#\<Gamma>)) \<Longrightarrow> eval e \<rho>' = eval e' \<rho>'"
  shows "heapExtendJoin \<rho> ((x,e)#\<Gamma>) eval = heapExtendJoin \<rho> ((x,e')#\<Gamma>) eval"
  apply (rule parallel_heapExtendJoin_ind[OF cond1 cond2])
  apply (auto intro: adm_is_adm_on)[1]
  apply simp
  apply (subst heapToEnv_subst_exp)
  apply (rule assms(3))
  apply (drule fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond1]])
  apply simp
  apply simp
  done

lemma HSem_subst_exp:
  assumes cond1: "heapExtendJoin_cond' ((x, e) # \<Gamma>) ESem \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x, e') # \<Gamma>) ESem \<rho>"
  assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (fst`set ((x,e)#\<Gamma>)) \<Longrightarrow> ESem e \<rho>' = ESem e' \<rho>'"
  shows "\<lbrace>(x,e)#\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e')#\<Gamma>\<rbrace>\<rho>"
by (metis HSem_def heapExtendJoin_subst_exp[OF assms])

lemma HSem_subst_var_app:
  assumes cond1: "heapExtendJoin_cond' ((x, App (Var n) y) # (n, e) # \<Gamma>) ESem \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x, App e y) # (n, e) # \<Gamma>) ESem \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule below_antisym)
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  show "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>"
  apply (subst  HSem_def)
  proof (rule heapExtendJoin_ind'[OF cond1])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
   have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
      by simp
    also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
      apply (subst HSem_unroll[OF cond2])
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]])
      apply simp
      done
    finally
    have "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by simp
    hence app: "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below])
      
    show ?case
      apply (subst HSem_unroll[OF cond2])
      apply (rule join_mono[OF
        rho_F_compat_jfc''[OF cond1 goal3(1)]
        rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]
        ])
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (simp del: heapToEnv.simps ESem.simps)
      apply (rule cont2monofunE[OF fmap_expand_cont])
      apply (rule fmap_upd_mono[OF _ app])
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      done
  qed    

  show "\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>"
  apply (subst HSem_def)
  proof (rule heapExtendJoin_ind'[OF cond2])  
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
   have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
      by simp
    also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
      apply (subst HSem_unroll[OF cond1])
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]])
      apply simp
      done
    finally
    have "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by simp
    hence app: "\<lbrakk> App e y \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below])

    show ?case
      apply (subst HSem_unroll[OF cond1])
      apply (rule join_mono[OF
        rho_F_compat_jfc''[OF cond2 goal3(1)]
        rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]
        ])
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (simp del: heapToEnv.simps ESem.simps)
      apply (rule cont2monofunE[OF fmap_expand_cont])
      apply (rule fmap_upd_mono[OF _ app])
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      done
  qed
qed

lemma HSem_subst_var_var:
  assumes cond1: "heapExtendJoin_cond' ((x, Var n) # (n, e) # \<Gamma>) ESem \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x, e) # (n, e) # \<Gamma>) ESem \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule below_antisym)
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  show "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>"
  apply (subst  HSem_def)
  proof (rule heapExtendJoin_ind'[OF cond1])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
   have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
      by simp
    also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
      apply (subst HSem_unroll[OF cond2])
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]])
      apply simp
      done
    finally
    have app: "\<lbrakk> Var n \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below])
      
    show ?case
      apply (subst HSem_unroll[OF cond2])
      apply (rule join_mono[OF
        rho_F_compat_jfc''[OF cond1 goal3(1)]
        rho_F_compat_jfc''[OF cond2 HSem_there[OF cond2]]
        ])
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (simp del: heapToEnv.simps ESem.simps)
      apply (rule cont2monofunE[OF fmap_expand_cont])
      apply (rule fmap_upd_mono[OF _ app])
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      done
  qed    

  show "\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>"
  apply (subst HSem_def)
  proof (rule heapExtendJoin_ind'[OF cond2])  
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
   have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>) n)"
      by simp
    also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
      apply (subst HSem_unroll[OF cond1])
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]])
      apply simp
      done
    finally
    have app: "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] eq_imp_below[OF sym]])

    show ?case
      apply (subst HSem_unroll[OF cond1])
      apply (rule join_mono[OF
        rho_F_compat_jfc''[OF cond2 goal3(1)]
        rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]
        ])
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (simp del: heapToEnv.simps ESem.simps)
      apply (rule cont2monofunE[OF fmap_expand_cont])
      apply (rule fmap_upd_mono[OF _ app])
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      done
  qed
qed


theorem correctness:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<lbrace>\<Gamma>'@\<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>'@\<Delta>\<rbrace>fempty"
  using assms
proof(induct rule:reds_distinct_ind)
print_cases
case (Lambda x y e \<Gamma> \<Gamma>')
  show ?case by simp
next

case (Application n \<Gamma> \<Gamma>' x e y \<Theta> \<Theta>' z \<Delta> \<Delta>' e')
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
    by (metis (hide_lams, no_types) Application(1) Application(10) fresh_Pair heapVars_not_fresh reds_doesnt_forget'(1) set_rev_mp)
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

  have "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty = (\<lbrace>(x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>fempty)"
    by simp
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>fempty)"
    (* Adding a fresh variable *)
    apply (subst HSem_add_fresh[of fempty "(x, App e y) # \<Gamma>' @ \<Gamma>" n e, symmetric])
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append exp_assn.fresh)
    apply simp
    done
  also have  "... = ?restr (\<lbrace>(x, App e y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>fempty)"
    by (rule arg_cong[OF HSem_reorder_head[OF `n \<noteq> x`]])
  also
  have "... = ?restr (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>fempty)"
    (* Substituting the variable *)
    apply (rule arg_cong[OF HSem_subst_var_app[symmetric]])
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma>\<rbrace>fempty)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... \<le> ?restr2  (\<lbrace>(n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>\<rbrace>fempty)"
    (* Restriction and \<le> *)
    apply (rule fmap_restr_le[OF Application.hyps(9)[simplified]])
    using subset1 subset2 by auto
  also
  have "... \<le> ?restr2  (\<lbrace>(x, App (Var n) y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>fempty)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = ?restr2 (\<lbrace>(x, App (Lam [z]. e') y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>fempty)"
    (* Substituting the variable *)
    apply (rule arg_cong[OF HSem_subst_var_app])
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr2 (\<lbrace>(n, Lam [z]. e') # (x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>fempty)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = (\<lbrace>(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>fempty)"
    (* Removing a fresh variable *)
    apply (subst HSem_add_fresh[of fempty "(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>" n "Lam [z]. e'", symmetric])
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append exp_assn.fresh)
    apply simp
    done
  also
  have "... =  \<lbrace>(x, e'[z::=y]) # \<Delta>' @ \<Delta>\<rbrace>fempty"
    (* Denotation of application *)
    apply (rule HSem_subst_exp)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
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
      apply (metis fresh_Pair fst_conv heapVars_def heapVars_not_fresh imageI)
      apply (metis fresh_Pair fst_conv heapVars_def heapVars_not_fresh imageI)
    done
  also
  have "... \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>fempty" by (rule Application.hyps(11)[simplified])
  finally
  show "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>fempty".

next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have "x \<noteq> y"
    using Variable(3) by (metis Variable(4) Variable(5) distinctVars_ConsD(1) distinctVars_appendD1 not_Cons_self removeAll.simps(2) removeAll_no_there)

  have "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty = \<lbrace>((y, e) # (x, Var y) # \<Gamma>') @ removeAll (y, e) \<Gamma>\<rbrace>fempty"
    (* Shifting a variable around *)
    apply (rule HSem_reorder[OF Variable.hyps(2,3)])
    using Variable(1)
    by auto
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>fempty"
    by fact
  also
  have "... =  \<lbrace>(y, z) # (x, Var y) # \<Delta>' @ \<Delta>\<rbrace>fempty"
    by simp
  also
  have "... =  \<lbrace>(x, Var y) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>fempty"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>(x, z) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>fempty"
    (* Substituting a variable *)
    apply (rule HSem_subst_var_var)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    apply (metis fempty_is_heapExtendJoin_cond' ESem_cont)
    using `x \<noteq> y` by (simp add: fresh_Pair fresh_at_base)
  also
  have "... =  \<lbrace>(y, z) # (x, z) # \<Delta>' @ \<Delta>\<rbrace>fempty"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>((y, z) # (x, z) # \<Delta>') @ \<Delta>\<rbrace>fempty"
    by simp
  also
  {
  have "distinctVars (((y, z) # (x, z) # \<Delta>') @ \<Delta>)"
    using Variable.hyps(4)
    by (simp add: distinctVars_append distinctVars_Cons)
  }
  hence "... = \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>fempty"
    apply (rule HSem_reorder[OF _ Variable.hyps(5)])
    by auto
  finally
  show "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>fempty".

next
case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  have "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>\<rbrace>fempty"
    (* Unrolling a let *)
    sorry
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>fempty"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>fempty".
qed

end

