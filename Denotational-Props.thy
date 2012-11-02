theory "Denotational-Props"
  imports "Denotational"
begin



lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (ESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
print_cases
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (ESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    by (intro cont2cont cont_compose[OF `cont (ESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (ESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ Var.prems(2)])    
next
case (Let as e Y0 Y)
  have fdoms[simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have unset: "\<And>i. fdom (Y i) \<inter> (fst ` set (asToHeap as)) = {}"
    using Let by (metis fdoms disjoint_iff_not_equal sharp_star_Env)
  have conts: "\<forall>e\<in>snd ` set (asToHeap as). cont (ESem e)" using Let.hyps(2) by metis
  have "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)
  moreover
  have "range (\<lambda>i. heapExtendJoin (Y i) (asToHeap as) ESem) <<| heapExtendJoin (Lub Y) (asToHeap as) ESem"
    apply (rule range_is_lubI2)
    apply (rule heapExtendJoin_monofun'')
      apply (erule Let.hyps(2))
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule chainE[OF `chain Y`])
    apply (rule heapExtendJoin_monofun'')
      apply (erule Let.hyps(2))
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset[unfolded fdoms] conts])
      apply (rule is_ub_thelub[OF `chain Y`])
    apply (rule eq_imp_below)
    apply (rule heapExtendJoin_cont'')
      apply (erule Let.hyps(2))
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset[unfolded fdoms] conts])
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule `chain Y`)
   done
  moreover
  have "chain (\<lambda>i. heapExtendJoin (Y i) (asToHeap as) ESem)"
    apply (rule chainI)
    apply (rule heapExtendJoin_monofun'')
      apply (erule Let.hyps(2))
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule chainE[OF `chain Y`])
   done
  ultimately
  show ?case
    apply simp
    by (metis cont_def lub_eqI)
next
case ANil thus ?case by auto
next
case (ACons v e as Y0 Y)
  have "cont (ESem e)" using ACons.hyps(1) by (rule contI, auto)
  with ACons
  show ?case by auto
qed

lemma ESem_cont: "cont (ESem e)"  using ESem_cont'[OF refl] by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]


definition HSem ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> = heapExtendJoin \<rho> \<Gamma> ESem"

lemma Esem_simps4[simp]: "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as \<rbrace>\<rho>\<^esub>"
  by (simp add: HSem_def)

lemma HSem_def': "heapExtendJoin_cond' \<Gamma> ESem \<rho> \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> = fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lambda>\<rho>'. fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>)))
           (\<lambda>\<rho>'. fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>) \<squnion> fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>))
 "
  unfolding HSem_def heapExtendJoin_def
  by (subst if_P, auto)

declare ESem.simps(4)[simp del]

(*
lemma HSem_cont2: "cont (\<lambda>y. HSem \<Gamma> y)"
  unfolding HSem_def' by auto

lemmas HSem_cont2cont[cont2cont,simp] = cont_compose[OF HSem_cont2]
*)

lemma HSem_eqvt[eqvt]: "\<pi> \<bullet> (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<lbrace>\<pi> \<bullet> \<Gamma>\<rbrace>(\<pi> \<bullet> \<rho>)"
  unfolding HSem_def
  by (perm_simp, rule)

lemma fmap_expand_fempty[simp]: "fmap_expand fempty S = fmap_bottom S"
  by (transfer, auto)

lemma fmap_expand_fdom[simp]: "fmap_expand \<rho> (fdom \<rho>) = \<rho>"
  by (transfer, auto split:option.split)

lemma heapExtendJoin_cond'_Nil[simp]:
  "heapExtendJoin_cond' [] ESem \<rho>"
  by (rule disjoint_is_heapExtendJoin_cond', auto)

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  apply (subst HSem_def)
  apply (subst heapExtendJoin_eq[OF heapExtendJoin_cond'_Nil])
  apply auto
  by (metis below.r_refl is_joinI to_bot_fmap_def to_bot_minimal)

lemma [simp]:"fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fdom \<rho> \<union> fst ` set \<Gamma>"
  unfolding HSem_def by simp

lemma adm_lookup: assumes "adm P" shows "adm (\<lambda> \<rho>. P (the (lookup \<rho> x)))"
  apply (rule admI)
  apply (subst lookup_cont)
  apply assumption
  apply (erule admD[OF assms lookup_chain])
  apply metis
  done

lemma [simp]: "x \<notin> fst ` set \<Gamma> \<Longrightarrow> the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x) = the (lookup \<rho> x)"
  apply (cases "x \<in> fdom \<rho>")
  apply (rule below_antisym)
  unfolding HSem_def
  apply (rule heapExtendJoin_ind)
  apply (rule adm_is_adm_on)
  apply (rule adm_lookup)
  apply simp
  apply (subst to_bot_fmap_def)
  apply simp
  apply (subst the_lookup_join)
  apply (erule (1) rho_F_compat_jfc'')
  apply simp
  apply simp
  apply (cases "heapExtendJoin_cond' \<Gamma> ESem \<rho>")
  apply (subst heapExtendJoin_eq, assumption)
  apply (subst the_lookup_join)
  apply (rule rho_F_compat_jfc'', assumption)
  apply (erule heapExtendJoin_there)
  apply simp
  apply (simp add: heapExtendJoin_def)
  apply (simp add: lookup_not_fdom)
  done

(*
lemma fmap_upd_fix1: 
  assumes above: "x0 \<sqsubseteq> F\<cdot>x0"
    and permute: "\<And>z. (F\<cdot>z)(x f\<mapsto> y) = F\<cdot>(z(x f\<mapsto> y))"
    shows "(fix1 x0 F) (x f\<mapsto> y) = fix1 (x0 (x f\<mapsto> y)) (\<Lambda> z. (F\<cdot>z)(x f\<mapsto> y))"
  apply (rule parallel_fix1_ind)
  apply auto[1]
  apply (rule above)
  apply simp
  apply (subst permute[symmetric])
  apply simp
  apply (rule cont2monofunE[OF fmap_upd_cont[OF cont_id cont_const]])
  apply (rule above)
  apply (rule refl)
  apply simp
  apply (subst (1 2) permute)
  apply (rule cfun_arg_cong[of _ _ F])
  apply (drule sym)
  apply simp
  done

lemma fmap_update_fix1: 
  assumes above: "x0 \<sqsubseteq> F\<cdot>x0"
    and permute: "\<And>z. fmap_update \<rho> (F\<cdot>z) = F \<cdot> (fmap_update \<rho> z)"
    shows "fmap_update \<rho> (fix1 x0 F) = fix1 (fmap_update \<rho> x0) (\<Lambda> z. fmap_update \<rho> (F\<cdot>z))"
  apply (rule parallel_fix1_ind)
  apply auto[1]
  apply (rule above)
  apply simp
  apply (subst permute[symmetric])
  apply simp
  apply (rule cont2monofunE[OF fmap_update_cont2cont[OF cont_const cont_id]])
  apply (rule above)
  apply (rule refl)
  apply simp
  apply (subst (1 2) permute)
  apply (rule cfun_arg_cong[of _ _ F])
  apply (drule sym)
  apply simp
  done
*)

lemma  fmap_update_belowI:
  assumes "fdom x \<union> fdom y = fdom z"
  and "\<And> a. a \<in> fdom y \<Longrightarrow> the (lookup y a) \<sqsubseteq> the (lookup z a)"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> a \<notin> fdom y \<Longrightarrow> the (lookup x a) \<sqsubseteq> the (lookup z a)"
  shows  "fmap_update x y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI)
  apply auto[1]
  by (metis fdomIff lookup_fmap_update1 lookup_fmap_update2 the.simps)

lemma  fmap_join_belowI:
  assumes "compatible x y"
  assumes "fdom z = fdom x"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> the (lookup x a) \<sqsubseteq> the (lookup z a)"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> the (lookup y a) \<sqsubseteq> the (lookup z a)"
  shows  "x \<squnion> y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI')
  apply (metis join_above1 below_fmap_def)
  by (metis "HOLCF-Join.join_above1" "HOLCF-Join.join_above2" below_fmap_def join_below)

lemma HSem_compat: "compatible (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
  unfolding HSem_def
  by (rule heapExtendJoin_compatible)

lemma HSem_unroll: "heapExtendJoin_cond' \<Gamma> ESem \<rho> 
  \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>) \<squnion> (fmap_expand (heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>))"
  apply (subst (1 2) HSem_def)
  by (rule heapExtendJoin_eq)

lemma HSem_there:
  "heapExtendJoin_cond' \<Gamma> ESem \<rho> \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>))
          (\<lambda>\<rho>'. fmap_expand (heapToEnv \<Gamma> (\<lambda>e. ESem e \<rho>')) (fdom \<rho> \<union> fst ` set \<Gamma>))"
  unfolding HSem_def by (drule heapExtendJoin_there)
 

lemma HSem_refines:
  "heapExtendJoin_cond' \<Gamma> ESem \<rho>' \<Longrightarrow> fmap_expand \<rho>' (fdom \<rho>' \<union> fst ` set \<Gamma>)  \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>'"
  apply (subst HSem_unroll, assumption)
  apply (rule join_above1)
  apply (rule rho_F_compat_jfc'', assumption)
  apply (subst HSem_def)
  apply (erule heapExtendJoin_there)
  done

lemma fdom_fix_on:
  assumes "fix_on_cond S b F"
  shows  "fdom (fix_on' b F) = fdom b"
proof-
  have "fix_on S F \<in> S"
    by (rule fix_on_there[OF assms])
  hence "b \<sqsubseteq> fix_on' b F"
    by (metis assms bottom_of_subpcpo_bot_minimal fix_on_cond.simps subpcpo_is_subpcpo_bot)
  thus ?thesis
    by (metis fmap_below_dom)
qed

lemma fdom_fix_join_compat'':
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat'' \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_jfc'' fmap_below_dom subpcpo.bottom_of_minimal subpcpo_jfc'' to_bot_minimal)


lemma fjc'_of_member:
  assumes "fix_on_cond_jfc' \<rho> F"
  assumes "\<rho>' \<in> fix_join_compat'' \<rho> F" (is "_ \<in> ?S")
  assumes "to_bot \<rho> = to_bot \<rho>'"
  shows "fix_on_cond_jfc' \<rho>' F"
proof (rule fix_on_cond_jfc'I)
case goal1
  have "cont F" by (rule cont_F_jfc''[OF assms(1)])
  thus ?case by simp
case (goal2 i)
  show ?case
  apply (rule compat_jfc''[OF assms(2) F_pres_compat''[OF assms(1)]])

  apply (induct_tac i)
  apply (simp only: funpow.simps id_apply fjc''_iff)
  apply (rule to_bot_belowI)
  apply (simp add: assms(3))

  apply (simp only: funpow.simps o_apply id_apply)
  apply (erule join_jfc''[OF assms(2) F_pres_compat''[OF assms(1)]])
  done
qed

lemma fjc'_of_fun_below:
  fixes \<rho> :: "'a\<Colon>{Bounded_Nonempty_Meet_cpo,subpcpo_partition}"
  assumes "fix_on_cond_jfc' \<rho> F"
  assumes "G \<sqsubseteq> F"
  assumes "cont G"
  shows "fix_on_cond_jfc' \<rho> G"
  apply (rule fix_on_cond_jfc'I[OF assms(3)])
  apply (rule compat_jfc''[OF rho_jfc''[OF assms(1)]])
  apply (rule down_closed.down_closedE[OF down_closed_jfc'' _ fun_belowD[OF assms(2)]])
  apply (rule F_pres_compat''[OF assms(1)])
  
  apply (induct_tac i)
  apply (simp only: funpow.simps id_apply fjc''_iff)
  apply (rule to_bot_belowI)
  apply (simp add: assms(3))

  apply (simp only: funpow.simps o_apply id_apply)
  apply (rule join_jfc''[OF rho_jfc''[OF assms(1)]])
  apply (rule down_closed.down_closedE[OF down_closed_jfc'' _ fun_belowD[OF assms(2)]])
  apply (erule F_pres_compat''[OF assms(1)])
  done


lemma heapExtendJoin_cond'_of_member:
  assumes "heapExtendJoin_cond' \<Gamma> eval \<rho>"
  assumes "\<rho>' \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>))
                (\<lambda> \<rho>'.  fmap_expand (heapToEnv \<Gamma> (\<lambda>e. eval e \<rho>')) (fdom \<rho> \<union> fst ` set \<Gamma>))" (is "_ \<in> ?S")
  shows "heapExtendJoin_cond' \<Gamma> eval \<rho>'"
proof-
  let "fix_join_compat'' (fmap_expand \<rho> ?d) ?F" = "?S"
  have "fdom \<rho>' = ?d"
    using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF assms(1)] assms(2)]
    by auto
  have fdom[simp]:"fdom \<rho>' \<union> fst ` set \<Gamma> = ?d"
    using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF assms(1)] assms(2)]
    by auto
  show ?thesis
    apply (rule fjc'_of_member)
    apply (rule assms(1)[unfolded fdom[symmetric]])
    apply (subst fmap_expand_noop)
    apply (metis `fdom \<rho>' = fdom \<rho> \<union> fst \` set \<Gamma>` `fdom \<rho>' \<union> fst \` set \<Gamma> =fdom \<rho> \<union> fst \` set \<Gamma>`)
    apply (rule assms(2)[unfolded fdom[symmetric]])
    apply (simp add:to_bot_fmap_def)
    done
qed

lemma fmap_expand_belowI:
  assumes "fdom \<rho>' = S"
  assumes "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<in> S \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> the (lookup \<rho>' x)"
  shows "fmap_expand \<rho> S \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI')
  apply (metis assms(1) fdom_fmap_expand finite_fdom)
  apply (case_tac "x \<in> fdom \<rho>")
  apply (metis assms(1) assms(2) finite_fdom lookup_fmap_expand1)
  apply (metis assms(1) finite_fdom lookup_fmap_expand2 minimal the.simps)
  done

lemma subcpo_mem_adm:
  "subcpo S \<Longrightarrow> adm (\<lambda> x. x \<in> S)"
  by (rule admI, metis subcpo.cpo')

lemma heapToEnv_mono:
  "finite d1 \<Longrightarrow>
   d1 = d2 \<Longrightarrow>
   x \<notin> fst ` set \<Gamma> \<Longrightarrow>
  fmap_expand (heapToEnv \<Gamma> eval) d1 \<sqsubseteq> fmap_expand (heapToEnv ((x,e) # \<Gamma>) eval) d2"
   apply (erule subst)
   apply (rule fmap_expand_belowI)
   apply simp
   apply (rule eq_imp_below)
   apply simp
   apply (metis the_lookup_fmap_upd_other[symmetric])
   done

lemma iterative_HSem:
  assumes "heapExtendJoin_cond' ((x, e) # \<Gamma>) ESem \<rho>"
  assumes "x \<notin> fst `set \<Gamma>"
  shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> =
      fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))) (\<lambda> \<rho>'.  fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))))
              (\<lambda> \<rho>'. (\<lbrace>\<Gamma>\<rbrace>\<rho>')
                      \<squnion> (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))(x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>) 
                      \<squnion> (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))))" (is "_ = fix_on ?S ?R")
apply (subst HSem_def'[OF assms(1)])
proof(rule below_antisym)
  interpret subpcpo ?S by (rule subpcpo_jfc'')

  let "?d" = "fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)"

  let "fix_on _ ?L" = "fix_on ?S
                       (\<lambda>\<rho>'. fmap_expand \<rho> ?d \<squnion>
                             fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))"
  let "(\<lambda> \<rho>'. ?L1 \<rho>' \<squnion> ?L2 \<rho>')" = ?L
  let "(\<lambda> \<rho>'. ?R1 \<rho>' \<squnion> (?R2 \<rho>' \<squnion> ?R3 \<rho>'))" = ?R

  { fix \<rho>' assume "\<rho>' \<in> ?S"
    hence fdom1: "fdom \<rho>' = ?d"
    apply (subst (asm) fjc''_iff)
    apply (drule fmap_below_dom)
    apply (subst (asm) fdom_fix_on[OF fix_on_cond_jfc''[OF assms(1)], unfolded bottom_of_jfc''])
    apply auto
    done
  } note fdom = this

  { fix \<rho>' assume "\<rho>' \<in> ?S"
    have fdom1: "(fdom \<rho>' \<union> fst ` set \<Gamma>) = ?d" using fdom[OF `\<rho>' \<in> ?S`] by auto
    have fdom2: "(fdom \<rho>' \<union> fst ` set ((x,e) # \<Gamma>)) = ?d" using fdom1 by auto
    have "heapExtendJoin_cond' ((x,e) # \<Gamma>) ESem \<rho>'" by (rule heapExtendJoin_cond'_of_member[OF assms(1) `\<rho>'\<in>?S`])
    from this[unfolded fdom2]
    have "heapExtendJoin_cond' \<Gamma> ESem \<rho>'"
      apply (subst (1 2) fdom1, rule fjc'_of_fun_below)
      apply (rule fun_belowI)
      apply (rule heapToEnv_mono)
      apply simp
      apply rule
      apply (simp add: assms(2))
      apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]])
      done
  } note heapExtendJoin_cond'_Gamma = this

  have closedL: "closed_on ?S ?L"
    by (rule closed_on_jfc''[OF assms(1)])

  have closedR1: "closed_on ?S ?R1"
    apply (rule closed_onI)
    apply (subst HSem_def)
    apply (rule heapExtendJoin_ind)
    apply (rule adm_is_adm_on[OF subcpo_mem_adm[OF subcpo_jfc'']])
    apply (rule down_closed.down_closedE[OF down_closed_jfc''], assumption)
    apply (frule fdom)
    apply (auto simp add:to_bot_fmap_def simp del:fjc''_iff)[1]
    apply (rule join_jfc'')
     apply (subst fmap_expand_noop)
     apply (frule fdom, auto)[1]
     apply assumption
    
    apply (rule down_closed.down_closedE[OF down_closed_jfc'' F_pres_compat''[OF assms(1)]], assumption) back
    apply (rule heapToEnv_mono)
    apply simp
    apply (frule fdom, auto)[1]
    apply (simp add: assms(2))
    apply (subst fmap_expand_noop)
    apply (frule fdom, auto)[1]
    apply assumption
    done
    
  have closedR2: "closed_on ?S ?R2"
    apply (rule closed_onI)
    apply (rule down_closed.down_closedE[OF down_closed_jfc'' F_pres_compat''[OF assms(1)]], assumption)
    apply (rule fmap_belowI')
    apply (frule fdom, auto)[1]
    apply (case_tac "xaa = x", simp_all)
    done    
    
  have closedR3: "closed_on ?S ?R3"
    apply (rule closed_onI)
    by (rule rho_jfc''[OF assms(1)])

  have closedR: "closed_on ?S ?R"
    by (rule closed_on_join_jfc''[OF closedR1 closed_on_join_jfc''[OF closedR2 closedR3]])

  have contL: "cont_on ?S ?L"
    by (rule cont_on_jfc''[OF assms(1)])
    
  have contR1: "cont_on ?S ?R1"
    apply (subst HSem_def)
    apply (rule cont_onI2)
    apply (rule monofun_onI)
    apply (erule (2) heapExtendJoin_monofun''[OF ESem_cont heapExtendJoin_cond'_Gamma heapExtendJoin_cond'_Gamma])
    apply (rule eq_imp_below[OF heapExtendJoin_cont''])
    apply auto[1]
    apply (erule heapExtendJoin_cond'_Gamma[OF chain_on_lub_on])
    apply (erule heapExtendJoin_cond'_Gamma[OF chain_on_is_on])
    apply (erule chain_on_is_chain)
    done

  have contR2: "cont_on ?S ?R2"
    by (rule cont_is_cont_on[OF fmap_upd_cont[OF cont_const ESem_cont]])

  have contR3: "cont_on ?S ?R3"
    by (rule cont_is_cont_on[OF cont_const])

  have contR: "cont_on ?S ?R"
    apply (rule cont_on_join_jfc')
    apply (rule closedR1)
    apply (rule closed_on_join_jfc''[OF closedR2 closedR3])
    apply (rule contR1)
    apply (rule cont_on_join_jfc')
    apply (rule closedR2)
    apply (rule closedR3)
    apply (rule contR2)
    apply (rule contR3)
    done

  note fix_on_condL = fix_on_cond_jfc''[OF assms(1)]

  have fix_on_condR: "fix_on_cond ?S (bottom_of ?S) ?R"
    by (rule fix_on_condI[OF subpcpo_jfc'' refl closedR contR])

  have R_there: "fix_on ?S ?R \<in> ?S"
    by (rule fix_on_there[OF fix_on_condR])

    
  have compatL: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?L1 x) (?L2 x)"
    by (rule compat_jfc''[OF rho_jfc''[OF assms(1)]  F_pres_compat''[OF assms(1)]])
    
  have compatR2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R2 x) (?R3 x)"
    by (rule compat_jfc''[OF closed_onE[OF closedR2] closed_onE[OF closedR3]])
  have compatR1R2: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x)"
    by (rule compat_jfc''[OF closed_onE[OF closedR1] closed_onE[OF closedR2]])
  have compatR1R2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x \<squnion> ?R3 x)"
    by (rule compat_jfc''[OF closed_onE[OF closedR1] closed_onE[OF closed_on_join_jfc''[OF closedR2 closedR3]]])
  have compatR1R2R3': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x \<squnion> ?R2 x) (?R3 x)"
    by (rule compat_jfc''[OF closed_onE[OF closed_on_join_jfc''[OF closedR1 closedR2]] closed_onE[OF closedR3]])

  show "fix_on ?S ?L \<sqsubseteq> fix_on ?S ?R"
  proof (rule fix_on_mono[OF fix_on_condL fix_on_condR])
    fix \<rho>'
    assume there: "\<rho>' \<in> ?S"
    hence [simp]:"fdom \<rho>' = ?d" by (rule fdom)

    have inner_cond: "heapExtendJoin_cond' \<Gamma> ESem \<rho>'"
      by (rule heapExtendJoin_cond'_Gamma[OF there])
    have inner_refine: "\<rho>' \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>'"
      apply (insert HSem_refines[OF inner_cond])
      apply (subst (asm) fmap_expand_noop)
      apply auto
      done

    have belowL1: "?L1 \<rho>' \<sqsubseteq> ?R \<rho>'"
      by (rule below_trans[OF join_above2[OF compatR2R3[OF there]] join_above2[OF compatR1R2R3[OF there]]])

    have "?L2 \<rho>' \<sqsubseteq> ?R1 \<rho>' \<squnion> ?R2 \<rho>'"
    proof (rule fmap_belowI')
    case goal1 show ?case
      by (subst fdom_join[OF compatR1R2[OF there]], auto)
    case (goal2 x')
      hence "x' \<in> ?d" by simp
      show ?case
      proof(cases "x' = x")
      case True
        show ?thesis
          apply (subst the_lookup_join[OF compatR1R2[OF there]])
          apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
          apply (simp add: True)
          apply (erule join_above2)
          done
      next
      case False
        show ?thesis
        proof (cases "x' \<in> fst ` set \<Gamma>")
        case True
          have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) x') \<sqsubseteq> the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>') x')"
            apply (subst HSem_unroll[OF inner_cond])
            apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF inner_cond  HSem_there[OF inner_cond]]])
            apply (insert the_lookup_compatible[OF rho_F_compat_jfc''[OF inner_cond  HSem_there[OF inner_cond]], of x'])
            apply (subst (2) lookup_fmap_expand1)
            apply (simp_all add: True)[3]
            apply (subst (asm) (2) lookup_fmap_expand1)
            apply (simp_all add: True)[3]
            apply (erule below_trans[OF _ join_above2, rotated])
            apply (rule cont2monofunE[OF _ inner_refine])
            apply (intro cont2cont)
            done
          thus ?thesis
            apply (subst lookup_fmap_expand1)
            apply simp
            apply (simp add: True)
            apply (simp add: True)
            apply (subst the_lookup_join[OF compatR1R2[OF there]])
            apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
            apply (simp add: True False)
            done
        next
        case False
          show ?thesis
          apply (subst lookup_fmap_expand2)
          apply simp
          apply fact
          apply (simp add: False `x' \<noteq> x`)
          apply simp
          done
        qed
      qed
    qed
    hence belowL2: "?L2 \<rho>' \<sqsubseteq> ?R \<rho>'"
      apply (subst join_assoc[symmetric, OF compatR1R2[OF there] compatR1R2R3[OF there] compatR2R3[OF there]])
      apply (erule below_trans[OF _ join_above1[OF compatR1R2R3'[OF there]]])
      done

    show "?L \<rho>' \<sqsubseteq> ?R \<rho>'"
      apply (rule join_below[OF compatL[OF there]])
      apply (rule belowL1)
      apply (rule belowL2)
      done
  qed

  show "fix_on ?S ?R \<sqsubseteq> fix_on ?S ?L"
    unfolding bottom_of_jfc''
    by (rule R_there[unfolded fjc''_iff, unfolded bottom_of_jfc''])
qed

(*
lemma iterative_HSem:
  assumes "x \<notin> fst ` set \<Gamma>"
  shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x,e) # \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))(x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)))" (is "_ = fix1 _ ?R")
apply (subst HSem_def''')
proof(rule below_antisym)
  let "fix1 ?x0 ?L" = "fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)))"

  have "?x0 \<sqsubseteq> ?L\<cdot>?x0"
    by (auto intro: cont2monofunE[OF fmap_update_cont2])
  (* have "?x0 \<sqsubseteq> ?R\<cdot>?x0" 
    apply (rule fmap_bottom_below)
    by (auto)*)
  have "?x0 \<sqsubseteq> ?R\<cdot>?x0" 
    by simp

{
  show "fix1 ?x0 ?L \<sqsubseteq> fix1 ?x ?R"
  proof(rule fix_least_below[OF `?x0 \<sqsubseteq> ?L\<cdot>?x0`])
    let "?y" = "fix1 ?x ?R"
    show  "?x0 \<sqsubseteq> ?y"
      apply (rule start_below_fix1)
      apply (rule fmap_bottom_below)
      apply auto
      done

    have large_fdom[simp]: "fdom ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) = insert x (fst ` set \<Gamma>)"
      by simp

    have "?L\<cdot>?y \<sqsubseteq> ?R\<cdot>?y"
    proof (rule fmap_belowI')
      show "fdom (?L\<cdot>?y) = fdom (?R\<cdot>?y)" using fmap_below_dom[OF `?x0 \<sqsubseteq> ?y`] by auto
    next
      fix x'
      assume "x' \<in> fdom (?L\<cdot>?y)" and "x' \<in> fdom (?R\<cdot>?y)"
      show "the (lookup (?L\<cdot>?y) x') \<sqsubseteq> the (lookup (?R\<cdot>?y) x')"
      proof (cases "x' = x")
        case True thus ?thesis by auto
      next
        case False note F1 = this thus ?thesis
        proof (cases "x' \<in> fdom (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>))")
        case True
          moreover
          hence "x' \<in> fdom ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>))" by auto
          moreover
          hence "x' \<in> fst ` set \<Gamma>" using F1 by auto
          moreover
          {
            (*
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x')  \<sqsubseteq>
              the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>)\<^esub>))\<^esub>)) x') "
              
              sorry
            also have "... \<sqsubseteq> the (lookup (fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>)\<^esub>))\<^esub>))) x')"
              using `x' \<in> fst \` set \<Gamma>` by simp
            also have "... = the (lookup (iterate (Suc 1) (\<Lambda> \<rho>'. fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)))\<cdot>(fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>))) x')"
                (is "_ = the (lookup ?rhs _)")
              by simp
            also
            have "?rhs \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              unfolding HSem_def'''
              by (rule iterate_below_fix[of _ _ "Suc 1"], simp)
            have "?rhs \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              unfolding HSem_def'''
              by (rule iterate_below_fix[of _ _ "Suc 1"], simp)
            hence "the (lookup ?rhs x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')"
              apply (subst lookup_fmap_restr[OF _ `x' \<in> fst \` set \<Gamma>`])
              apply auto[1]              
              by (rule fmap_belowE)
            finally
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')".

            have "fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              thm fix1_ind
              apply (rule fix1_ind[OF _ _ `?x0 \<sqsubseteq> ?R\<cdot>?x0`]) back back back back back
              apply auto[1]

              (* Base case *)
              apply (subst (2) HSem_unroll)
              apply (rule cont2monofunE) back back              
              apply auto[1]
              apply (rule fmap_bottom_below)
              apply auto[1]

              apply (subst (3) HSem_unroll)
              apply simp
              apply (rule cont2monofunE) back back
              apply auto[1]
              apply (erule rev_below_trans)
              




            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')"
              using  `x' \<in> fst \` set \<Gamma>`  `x' \<noteq> x`
              apply (subst (2) HSem_def'')
              apply simp
              apply (subst lookup_fmap_restr[OF _ `x' \<in> fst \` set \<Gamma>`])
              apply simp
              apply (rule fix1_ind) back
              defer
              apply (subst fix_eq)
              apply auto[1]
              apply simp
              apply (rule cont2monofunE) back back back
              apply simp
              apply (rule fmap_bottom_below)
              apply auto[1]
              apply (rule fmap_bottom_below)
              apply auto[1]
              
              apply (subst fix_eq) apply auto[1]
              
              apply simp
              apply (rule cont2monofunE) back back back 
              apply simp
              apply auto[1]
              thm fmap_belowE[OF below_trans[OF _ iterate_below_fix[of _ _ "1", simplified]]]
              apply (rule  fmap_belowE[OF below_trans[OF _ iterate_below_fix[of _ _ "1", simplified]]])
              apply simp
              find_theorems "fix"
              apply (subst (3) fix_eq)
              apply auto[1]
              apply simp
              sorry
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ?y x')" sorry
            *)
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup (?R \<cdot> ?y) x')" sorry
          }
          ultimately
          show ?thesis using `x' \<noteq> x` by simp
        next
        case False with F1 show ?thesis by auto
        qed
      qed
    qed
    thus "?L\<cdot>?y \<sqsubseteq> ?y"
      apply (subst (asm)  fix_eq[symmetric])
      by (auto intro!:fmap_bottom_below)
  qed
next
  show "fix1 ?x0 ?R \<sqsubseteq> fix1 ?x0 ?L"
  proof (rule fix_least_below[OF `?x0 \<sqsubseteq> ?R\<cdot>?x0`])
    show "?x0 \<sqsubseteq> fix1 ?x0 ?L" by (rule start_below_fix1[OF `?x0 \<sqsubseteq> ?L\<cdot>?x0`])
  next
    show "?R\<cdot>(fix1 ?x0 ?L) \<sqsubseteq> fix1 ?x0 ?L"
    proof (rule fmap_belowI')
      show "fdom (?R\<cdot>(fix1 ?x0 ?L)) = fdom (fix1 ?x0 ?L)" by auto
    next
      fix x'
      assume "x' \<in> fdom (?R\<cdot>(fix1 ?x0 ?L))" and "x' \<in> fdom (fix1 ?x0 ?L)"
      show "the (lookup (?R\<cdot>(fix1 ?x0 ?L)) x') \<sqsubseteq> the (lookup ((fix1 ?x0 ?L)) x')"
      proof (cases "x' = x")
      case True thus ?thesis  by (subst (2) fix_eq, auto)
      next
      case False note F1 = this
        show ?thesis
        proof (cases "x' \<in> fst ` set \<Gamma>")
        case True
          from `x \<notin> fst \` set \<Gamma>`
          have "fmap_update (fix1 ?x0 ?L) (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fix1 ?x0 ?L)\<^esub>)) \<sqsubseteq> (fix1 ?x0 ?L)"
            apply -
            apply (rule fmap_update_belowI[OF _ _ below_refl])
            apply auto[1]
            apply (subst (2) fix_eq)
            apply auto[1]
            apply (subst beta_cfun)
            apply auto[1]
            apply (subgoal_tac "a \<noteq> x")
            apply auto
            done
          hence "fix1 (fmap_bottom (fdom ((fix1 ?x0 ?L)) \<union> fst ` set ((x, e) # \<Gamma>))) (\<Lambda> y. fmap_update (fix1 ?x0 ?L) (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>))) \<sqsubseteq> (fix1 ?x0 ?L)"
            apply -
            apply (rule fix_least_below)
            apply (rule fmap_bottom_below)
            apply auto[1]
            apply (rule fmap_bottom_below)
            apply auto
            done
          hence "(\<lbrace>\<Gamma>\<rbrace>(fix1 ?x0 ?L)) \<sqsubseteq> (fix1 ?x0 ?L)"
            unfolding HSem_def'''
            by auto
          with True F1
          show ?thesis
            apply simp
            apply (subst lookup_fmap_restr)
            apply auto[2]
            apply (erule fmap_belowE)
            done
       next
       case False note F2 = this
         with F1 show ?thesis 
          apply (subst (2) fix_eq)
          apply auto[1]
          apply simp
          done
       qed
     qed
   qed
  qed
}
qed
*)

lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt]
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]

lemma fresh_fmap_upd'[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom x \<sharp> a ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)"
  by (metis fresh_at_base(2) fresh_fmap_upd)
  
lemma[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x  \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> the (lookup \<rho> y))"
  apply (auto simp add: fresh_star_def) 
  apply (rule fresh_fmap_upd)
  apply (auto simp add: pure_fresh)
  done    

lemma ESem_subst: "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> the (lookup \<rho> y))\<^esub>)
                    = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
proof (nominal_induct e and as  avoiding: \<rho> x y rule:exp_assn.strong_induct)
case (Var var \<rho> x y) thus ?case by auto
next
case (App exp var \<rho> x y) thus ?case by auto
next
case (Let as exp \<rho> x y)
  from `set (bn as) \<sharp>* x` `set (bn as) \<sharp>* y` 
  have "x \<notin> assn_vars as " "y \<notin> assn_vars as "
    by (induct as rule: assn_vars.induct, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"assn_vars (as[x::a=y]) = assn_vars as" 
     by (induct as rule: assn_vars.induct, auto)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>(x f\<mapsto> the (lookup \<rho> y))  = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap as)(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<rho>'a\<^esub>))))"
    apply (subst HSem_def') .. also
  have "... = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap as)(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)(x f\<mapsto> the (lookup (fmap_update \<rho> \<rho>'a) y))\<^esub>))))"
    apply (rule arg_cong)back
    using `x \<notin> _`  `y \<notin> _`
    apply (auto intro: fix1_cong simp add: fmap_update_upd_swap)
    done also
  have "... = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap (as[x ::a= y]))(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)\<^esub>))))"
      apply (rule arg_cong)back
      apply (rule fix1_cong)
      apply auto[2]
      apply simp
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y`])
      using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as`
      apply (auto simp add:sharp_Env)
    done also
  have "... = (fmap_update \<rho>
     (fix1 (fmap_bottom (fst ` set (asToHeap (as[x ::a= y]))))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap (as[x ::a= y]))(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)\<^esub>)))))(x f\<mapsto> the (lookup \<rho> y))"
       using `x \<notin> assn_vars as` by (auto simp add: fmap_update_upd_swap) also
  have "... = (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) (x f\<mapsto> the (lookup \<rho> y))"
    by (subst HSem_def', simp) also
  have "... = (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) (x f\<mapsto> the (lookup (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) y))"
    using `y \<notin> assn_vars as`
    by (auto simp add: the_lookup_HSem_other)
  finally
  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> the (lookup \<rho> y))) = (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> the (lookup (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>) y))" .
  with Let
  show ?case
  by (auto simp add: fresh_star_Pair fresh_at_base)
next
case (Lam var exp \<rho> x' y) thus ?case
  apply (auto simp add: fresh_star_Pair pure_fresh)
  apply (subst fmap_upd_twist)
  apply (auto)[1]
  apply (rule cfun_eqI) 
  apply (erule_tac x = "x'" in meta_allE)
  apply (erule_tac x = "y" in meta_allE)
  apply (erule_tac x = "\<rho>(var f\<mapsto> x)" in meta_allE)
  apply (auto simp add: pure_fresh fresh_at_base)[1]
  done
next
case (ANil \<rho> x y) thus ?case by auto
next
case(ACons var exp as \<rho> x y)  thus ?case by auto
qed


end
