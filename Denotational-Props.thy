theory "Denotational-Props"
  imports "Denotational"
begin


lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (ESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
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
  have "range (\<lambda>i. heapExtendJoin (Y i) (asToHeap as)) <<| heapExtendJoin (Lub Y) (asToHeap as)"
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
  have "chain (\<lambda>i. heapExtendJoin (Y i) (asToHeap as))"
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

definition HSem ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> = heapExtendJoin \<rho> \<Gamma>"

abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

lemma Esem_simps4[simp]: "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as \<rbrace>\<rho>\<^esub>"
  by (simp add: HSem_def)

lemma HSem_def': "heapExtendJoin_cond' \<Gamma> \<rho> \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> = fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)) (\<lambda>\<rho>'. fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>)))
           (\<lambda>\<rho>'. fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>) \<squnion> fmap_expand (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>))
 "
  unfolding HSem_def heapExtendJoin_def
  by (subst if_P, auto)

declare ESem.simps(4)[simp del]

lemma HSem_mono:
  assumes "heapExtendJoin_cond' \<Gamma> \<rho>1"
  assumes "heapExtendJoin_cond' \<Gamma> \<rho>2"
  assumes "\<rho>1 \<sqsubseteq> \<rho>2"
  shows "\<lbrace>\<Gamma>\<rbrace>\<rho>1 \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>2"
  unfolding HSem_def
  by(rule heapExtendJoin_monofun''[OF ESem_cont assms])

lemma disjoint_is_heapExtendJoin_cond'_ESem:
  assumes "fdom \<rho> \<inter> fst ` set h = {}"
  shows "heapExtendJoin_cond' h \<rho>" 
  by (metis disjoint_is_heapExtendJoin_cond'[OF assms] ESem_cont)

lemma fempty_is_heapExtendJoin_cond'_ESem[simp]:
  "heapExtendJoin_cond' h fempty"
  apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
  by auto

lemma HSem_eqvt[eqvt]: "\<pi> \<bullet> (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<lbrace>\<pi> \<bullet> \<Gamma>\<rbrace>(\<pi> \<bullet> \<rho>)"
  unfolding HSem_def
  by (perm_simp, rule)

lemma fmap_expand_fempty[simp]: "fmap_expand fempty S = fmap_bottom S"
  by (transfer, auto)

lemma fmap_expand_fmap_bottom[simp]: "fmap_expand (fmap_bottom S') S = fmap_bottom S"
  by (transfer, auto)

lemma fmap_expand_fdom[simp]: "fmap_expand \<rho> (fdom \<rho>) = \<rho>"
  by (transfer, auto split:option.split)

lemma heapExtendJoin_cond'_Nil[simp]:
  "heapExtendJoin_cond' [] \<rho>"
  by (rule disjoint_is_heapExtendJoin_cond'_ESem, simp)

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  apply (subst HSem_def)
  apply (subst heapExtendJoin_eq[OF heapExtendJoin_cond'_Nil])
  apply auto
  by (metis below.r_refl is_joinI to_bot_fmap_def to_bot_minimal)

lemma fdom_HSem[simp]:"fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fdom \<rho> \<union> fst ` set \<Gamma>"
  unfolding HSem_def by simp

lemma adm_lookup: assumes "adm P" shows "adm (\<lambda> \<rho>. P (the (lookup \<rho> x)))"
  apply (rule admI)
  apply (subst lookup_cont)
  apply assumption
  apply (erule admD[OF assms lookup_chain])
  apply metis
  done

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

lemma HSem_unroll: "heapExtendJoin_cond' \<Gamma> \<rho> 
  \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>) \<squnion> (fmap_expand (heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)) (fdom \<rho> \<union> fst ` set \<Gamma>))"
  apply (subst (1 2) HSem_def)
  by (rule heapExtendJoin_eq)

lemma HSem_there:
  "heapExtendJoin_cond' \<Gamma> \<rho> \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> \<in> fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>))
          (\<lambda>\<rho>'. fmap_expand (heapToEnv \<Gamma> (\<lambda>e. ESem e \<rho>')) (fdom \<rho> \<union> fst ` set \<Gamma>))"
  unfolding HSem_def by (drule heapExtendJoin_there)

lemma HSem_refines:
  "heapExtendJoin_cond' \<Gamma> \<rho>' \<Longrightarrow> fmap_expand \<rho>' (fdom \<rho>' \<union> fst ` set \<Gamma>)  \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>'"
  by (metis HSem_def heapExtendJoin_refines)

lemma HSem_refines_lookup: "heapExtendJoin_cond' \<Gamma> \<rho> \<Longrightarrow> x \<in> fdom \<rho> \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x)"
  apply (drule HSem_refines)
  apply (drule fmap_belowE[of _ _ x])
  apply simp
  done

lemma the_lookup_HSem_other:
  assumes "y \<notin> fst ` set h"
  shows "the (lookup (\<lbrace>h\<rbrace>\<rho>) y) = the (lookup \<rho> y)"
by (metis HSem_def the_lookup_heapExtendJoin_other[OF assms])

lemma the_lookup_HSem_both:
  assumes "heapExtendJoin_cond' h \<rho>"
  assumes "y \<in> fst ` set h"
  shows "the (lookup (\<lbrace>h\<rbrace>\<rho>) y) =
    the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) y) \<squnion> (\<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>)"
  by (metis HSem_def the_lookup_heapExtendJoin_both[OF assms])

lemma the_lookup_HSem_both_compatible:
  assumes "heapExtendJoin_cond' h \<rho>"
  assumes "y \<in> fst ` set h"
  shows "compatible (the (lookup (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h)) y)) (\<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>)"
  by (metis HSem_def the_lookup_heapExtendJoin_both_compatible[OF assms])


lemma the_lookup_HSem_heap:
  assumes "heapExtendJoin_cond' h \<rho>"
  assumes "y \<in> fst ` set h"
  assumes "y \<notin> fdom \<rho>"
  shows "the (lookup (\<lbrace>h\<rbrace>\<rho>) y) = \<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>"
  by (metis HSem_def the_lookup_heapExtendJoin_heap[OF assms])

lemma HSem_heap_below: "heapExtendJoin_cond' \<Gamma> \<rho> \<Longrightarrow> x \<in> fst ` set \<Gamma> \<Longrightarrow> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x)"
  apply (subst the_lookup_HSem_both, assumption+)
  apply (rule join_above2)
  apply (rule the_lookup_HSem_both_compatible, assumption+)
  done

lemma HSem_below:
  assumes "fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>) \<sqsubseteq> r"
  assumes "\<And>x. x \<in> fst ` set \<Gamma> \<Longrightarrow> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> the (lookup r x)"
  shows "\<lbrace>\<Gamma>\<rbrace>\<rho> \<sqsubseteq> r"
  unfolding HSem_def
  by (rule heapExtendJoin_below[OF assms ESem_cont])

lemma fdom_fix_on:
  assumes "fix_on_cond S b F"
  shows  "fdom (fix_on' b F) = fdom b"
proof-
  have "fix_on' b F \<in> S"
    by (rule fix_on_there[OF assms])
  hence "b \<sqsubseteq> fix_on' b F"
    by (metis assms bottom_of_subpcpo_bot_minimal fix_on_cond.simps subpcpo_is_subpcpo_bot)
  thus ?thesis
    by (metis fmap_below_dom)
qed


lemma iterative_HSem:
  assumes "heapExtendJoin_cond' ((x, e) # \<Gamma>) \<rho>"
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
    have "heapExtendJoin_cond' ((x,e) # \<Gamma>) \<rho>'" by (rule heapExtendJoin_cond'_of_member[OF assms(1) `\<rho>'\<in>?S`])
    from this[unfolded fdom2]
    have "heapExtendJoin_cond' \<Gamma> \<rho>'"
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

    have inner_cond: "heapExtendJoin_cond' \<Gamma> \<rho>'"
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


lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt]
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt]
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]

lemma fresh_fmap_upd'[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom x \<sharp> a ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)"
  by (metis fresh_at_base(2) fresh_fmap_upd)
  
lemma[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x  \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> the (lookup \<rho> y))"
  apply (auto simp add: fresh_star_def) 
  apply (rule fresh_fmap_upd)
  apply (auto simp add: pure_fresh)
  done

lemma fmap_upd_expand:
  "finite S \<Longrightarrow>
   x \<in> S \<Longrightarrow>
   fmap_expand (\<rho>(x f\<mapsto> y)) S = (fmap_expand \<rho> (S - {x}))(x f\<mapsto> y)"
   apply (rule fmap_eqI, auto)
   apply (case_tac "xa \<in> fdom (\<rho>(x f\<mapsto> y))", auto)
   apply (case_tac "xa = x", auto)
   done

lemma fmap_bottom_insert:
  "finite S \<Longrightarrow>
  fmap_bottom (insert x S) = (fmap_bottom S)(x f\<mapsto> \<bottom>)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "xa = x", auto)
  done

lemma fmap_upd_below:
  assumes "fdom \<rho>' = insert x (fdom \<rho>)"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> the (lookup \<rho> z) \<sqsubseteq> the (lookup \<rho>' z)" 
  assumes "y \<sqsubseteq> the (lookup \<rho>' x)"
  shows  "\<rho>(x f\<mapsto> y) \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI')
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_upd_below2:
  assumes "fdom \<rho> = insert x (fdom \<rho>')"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> the (lookup \<rho> z) \<sqsubseteq> the (lookup \<rho>' z)" 
  assumes "the (lookup \<rho> x) \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x f\<mapsto> y)"
  apply (rule fmap_belowI')
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma compatible_insert:
  assumes [simp]: "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat: "compatible \<rho>1 (fmap_expand \<rho>2 (fdom \<rho>1))"  
  shows "compatible (\<rho>1(x f\<mapsto> y)) (fmap_expand \<rho>2 S)"
proof(rule compatible_fmap_is_compatible[OF compatible_fmapI])
case (goal1 z)
  show ?case
  apply(cases "z = x")
  using `x \<notin> fdom \<rho>2` apply simp
  using goal1(1) the_lookup_compatible[OF compat, of z]
  apply (cases "z \<in> fdom \<rho>2")
  by auto
next
case goal2 with assms(1) show ?case by simp
qed
    

lemma fmap_upd_join:
  assumes "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat1: "compatible (\<rho>1(x f\<mapsto> y)) (fmap_expand \<rho>2 S)"
  shows "(\<rho>1(x f\<mapsto> y)) \<squnion> (fmap_expand \<rho>2 S) = (\<rho>1 \<squnion> (fmap_expand \<rho>2 (S - {x})))(x f\<mapsto> y)" (is "?L = ?R")
proof(rule fmap_eqI)
  have "finite S" using assms(1) by auto

  have *: "\<And> xa . xa \<in> S \<Longrightarrow> xa \<noteq> x \<Longrightarrow> the (lookup (fmap_expand \<rho>2 (S - {x})) xa) = the (lookup (fmap_expand \<rho>2 S) xa)"
    using `finite S` by (case_tac "xa \<in> fdom \<rho>2", auto)

  have compat2: "compatible \<rho>1 (fmap_expand \<rho>2 (S - {x}))"
    apply (rule compatible_fmap_is_compatible)
    apply (rule compatible_fmapI)
    using compat1
    apply -
    apply (drule_tac x = xa in compatible_fmapE[OF compatible_is_compatible_fmap])
    apply auto[1]
    using assms(1) apply auto[1]
    apply (subst *)
    using assms(1) apply simp
    apply (metis assms(2))

    apply (subst (asm) the_lookup_fmap_upd_other)
    apply (metis `x \<notin> fdom \<rho>1`)
    apply assumption
    using assms(2) assms(1)
    by auto

  show "fdom ?L = fdom ?R"
    using compat1 compat2 by auto
  fix xa
  assume "xa \<in> fdom ?L"
  hence "xa \<in> S" by (metis assms(1) compat1 fdom_join fmap_upd_fdom)
  show "the (lookup ?L xa) = the (lookup ?R xa)"
  proof(cases "xa = x")
    case True
    thus ?thesis
      apply (subst the_lookup_join[OF compat1])
      apply (subst lookup_fmap_expand2[OF `finite S` `xa \<in> S`])
      using `x \<notin> fdom \<rho>2` compat2  `xa \<in> S`
      by auto
  next
    case False
    thus ?thesis
      apply simp
      apply (subst the_lookup_join[OF compat1], auto)
      apply (subst the_lookup_join[OF compat2])
      apply (case_tac "xa \<in> fdom \<rho>2")
      using `finite S`  `xa \<in> S`
      by auto
  qed
qed


lemma ESem_subst: "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow>  heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> the (lookup \<rho> y))\<^esub>)
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

  have cond1: "heapExtendJoin_cond' (asToHeap as) (\<rho>(x f\<mapsto> the (lookup \<rho> y)))"
      (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    apply (auto simp add:  `x \<notin> assn_vars as`)
    by (metis Let(1) fst_set_asToHeap sharp_star_Env)
  have cond2: "heapExtendJoin_cond' (asToHeap as[x::a=y]) \<rho>"
      (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    apply (auto simp add:  `x \<notin> assn_vars as`)
    by (metis Let(1) fst_set_asToHeap sharp_star_Env)

  have lookup_other: "\<And> \<rho> . the (lookup (\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>) y) = the (lookup \<rho> y)"
    using `y \<notin> assn_vars as`
    by (auto simp add: the_lookup_HSem_other)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>(x f\<mapsto> the (lookup \<rho> y)) = heapExtendJoin (\<rho>(x f\<mapsto> the (lookup \<rho> y))) (asToHeap as)"
    apply (subst HSem_def) .. 

  have [simp]:"fdom \<rho> \<union> assn_vars as - {x} = fdom \<rho> \<union> assn_vars as"
    using `x \<notin> assn_vars as` `atom x \<sharp> \<rho>` by (auto simp add: sharp_Env)

  have *: "fmap_expand (\<rho>(x f\<mapsto> the (lookup \<rho> y))) (fdom (\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<union> fst ` set (asToHeap as))
        = (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set (asToHeap as)))(x f\<mapsto> the (lookup \<rho> y))" (is "_ = ?\<rho>1'(x f\<mapsto> _)")
    apply (subst fmap_upd_expand)
    apply auto[3]
    done

  have "fix_on (fix_join_compat'' ?\<rho>1 ?F1) (\<lambda> \<rho>'. ?\<rho>1 \<squnion> ?F1 \<rho>') \<sqsubseteq> (fix_on (fix_join_compat'' ?\<rho>2 ?F2) (\<lambda> \<rho>'. ?\<rho>2 \<squnion> ?F2 \<rho>')) ( x f\<mapsto> the (lookup (fix_on (fix_join_compat'' ?\<rho>2 ?F2) (\<lambda> \<rho>'. ?\<rho>2 \<squnion> ?F2 \<rho>')) y))"
    (is "?L \<sqsubseteq> ?R( x f\<mapsto> the (lookup ?R y))")
  proof (rule fix_on_ind[OF fix_on_cond_jfc''[OF cond1]])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2
    show ?case
      apply (subst bottom_of_jfc'')
      apply (subst to_bot_fmap_def)
      apply (rule fmap_bottom_below)
      apply (subst (2) fmap_upd_fdom)
      apply (subst fdom_fix_on[OF fix_on_cond_jfc''[OF cond2]])
      apply (simp add: bottom_of_jfc'' to_bot_fmap_def)
      done
  case (goal3 \<rho>')
    let "?F1' \<rho>'" = "fmap_expand (heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set (asToHeap as))"

    have "?\<rho>1 \<squnion> ?F1 \<rho>' = ?\<rho>1'(x f\<mapsto> the (lookup \<rho> y)) \<squnion> ?F1 \<rho>'"
      by (subst *, rule)
    also
    have "\<dots> = (?\<rho>1' \<squnion> ?F1' \<rho>')(x f\<mapsto> the (lookup \<rho> y))"
      apply (subst fmap_upd_join)
      using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as` apply (auto simp add: sharp_Env)[3]
      using rho_F_compat_jfc''[OF cond1 goal3(1)] apply (metis *)
      by auto
    also
    { have "?F1' \<rho>' \<sqsubseteq> ?F1' (?R( x f\<mapsto> the (lookup ?R y)))"
        by (rule cont2monofunE[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] goal3(2)])
      also
      have "... = ?F2 ?R"
        apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
          using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as` fdom_fix_on[OF fix_on_cond_jfc''[OF cond2]]
          apply (simp add: sharp_Env bottom_of_jfc'')
        by simp
      also note calculation     
    } 
    hence "... \<sqsubseteq> (?\<rho>2 \<squnion> ?F2 ?R)( x f\<mapsto> the (lookup \<rho> y))"
      apply (rule cont2monofunE[OF
              fmap_upd_cont[OF cont_id cont_const]
              join_mono'[OF rho_F_compat_jfc''[OF cond2 fix_on_there[OF fix_on_cond_jfc''[OF cond2]]]]
              , rotated])
      apply simp
    done
    also have "... = ?R( x f\<mapsto> the (lookup \<rho> y))"
      by (rule arg_cong[OF fix_on_eq[OF fix_on_cond_jfc''[OF cond2], symmetric]])
    also have "... = ?R( x f\<mapsto> the (lookup ?R y))"
      by (subst lookup_other[of \<rho>, unfolded HSem_def'[OF cond2]], rule)
    finally show "?\<rho>1 \<squnion> ?F1 \<rho>' \<sqsubseteq> ?R( x f\<mapsto> the (lookup ?R y))".
  qed
  also
  have "?R (x f\<mapsto> the (lookup ?R y)) \<sqsubseteq> ?L"
  proof (rule fix_on_ind[OF fix_on_cond_jfc''[OF cond2]])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2
    show ?case
      apply (subst fix_on_eq[OF fix_on_cond_jfc''[OF cond1]])
      apply (subst bottom_of_jfc'')
      apply (subst to_bot_fmap_def)
      apply (subst fdom_fmap_expand)
        apply simp
      
      apply (rule fmap_upd_below)
        apply (subst fdom_join[OF rho_F_compat_jfc''[OF cond1 fix_on_there[OF fix_on_cond_jfc''[OF cond1]]]])
        apply simp

      apply simp
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond1 fix_on_there[OF fix_on_cond_jfc''[OF cond1]]]])
      apply (rule rev_below_trans[OF join_above1[OF the_lookup_compatible[OF rho_F_compat_jfc''[OF cond1 fix_on_there[OF fix_on_cond_jfc''[OF cond1]]]]]])
      apply (cases "y \<in> fdom \<rho>")
      using  `y \<notin> assn_vars as` apply (auto simp add: bottom_of_jfc'' to_bot_fmap_def lookup_not_fdom)
      done
  case (goal3 \<rho>')
    let "?F1' \<rho>'" = "fmap_expand (heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set (asToHeap as))"
    let "?F2' \<rho>'" = "fmap_expand (heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (insert x (fdom \<rho> \<union> assn_vars as))"
    have "fdom \<rho>' = fdom \<rho> \<union> fst `set (asToHeap as)"
      using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond2] goal3(1)] by simp

    have "(?\<rho>2 \<squnion> ?F2 \<rho>') (x f\<mapsto> the (lookup (?\<rho>2 \<squnion> ?F2 \<rho>') y)) = (?\<rho>2 \<squnion> ?F2 \<rho>')(x f\<mapsto> the (lookup \<rho> y))"
      apply (rule arg_cong) back
      apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF cond2 goal3(1)]])
      apply (case_tac "y \<in> fdom \<rho>")
      using `y \<notin> assn_vars as`
      by (auto simp add: sharp_Env lookup_not_fdom)
    also
    have "... = (?\<rho>1'(x f\<mapsto> the (lookup \<rho> y)) \<squnion> ?F2' \<rho>')"
      apply (subst fmap_upd_join)
      using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as` apply (auto simp add: sharp_Env)[3]
      apply (rule compatible_insert)
        using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as` apply (auto simp add: sharp_Env)[3]
      apply simp
      apply (rule rho_F_compat_jfc''[OF cond2 goal3(1), simplified])
      apply simp
      done
    also
    have "... = ?\<rho>1 \<squnion> ?F2' \<rho>'"
      by (subst *, rule)
    also
    have "... = ?\<rho>1 \<squnion> ?F1 (\<rho>'(x f\<mapsto> the (lookup \<rho>' y)))"
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
        using `atom x \<sharp> \<rho>` `fdom \<rho>' = _` `x \<notin> assn_vars as` fdom_fix_on[OF fix_on_cond_jfc''[OF cond2]]
        apply (simp add: sharp_Env bottom_of_jfc'')
      by simp
    also
    from `\<rho>'(x f\<mapsto> the (lookup \<rho>' y)) \<sqsubseteq> ?L`
    have  "... \<sqsubseteq> ?L"
      unfolding bottom_of_jfc''
      by (rule join_jfc''[OF rho_jfc''[OF cond1] F_pres_compat''[OF cond1], unfolded fjc''_iff])
    finally
    show "(?\<rho>2 \<squnion> ?F2 \<rho>') (x f\<mapsto> the (lookup (?\<rho>2 \<squnion> ?F2 \<rho>') y)) \<sqsubseteq> ?L".
  qed
  finally
  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> the (lookup \<rho> y))) = (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> the (lookup (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>) y))"
    unfolding  HSem_def'[OF cond1] subst HSem_def'[OF cond2] .
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

lemma fmap_expand_compatible:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (auto simp add: fdom_compatible[OF compat] intro: the_lookup_compatible[OF compat])
  done


lemma fmap_expand_join:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "fmap_expand (\<rho>1 \<squnion> \<rho>2) S = fmap_expand \<rho>1 S \<squnion> fmap_expand \<rho>2 S"
proof-
  have [simp]: "fdom \<rho>2 = fdom \<rho>1" by (metis fdom_compatible[OF compat])
  have [simp]: "fdom (\<rho>1 \<squnion> \<rho>2) = fdom \<rho>1" by (rule fdom_join[OF compat])
  have compat2: "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
    by (rule fmap_expand_compatible[OF assms])
  show ?thesis
    apply (rule fmap_eqI)
    apply (simp add: fdom_join[OF compat2])
    apply (case_tac "x \<in> fdom \<rho>1")
    by (auto simp add: the_lookup_join[OF compat2] the_lookup_join[OF compat])
qed



lemma ESem_mono_fdom_changes:
  shows "\<rho>2 \<sqsubseteq> fmap_expand \<rho>1 (fdom \<rho>2) \<Longrightarrow> fdom \<rho>1 \<subseteq> fdom \<rho>2 \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>"
  and
   "\<rho>2 \<sqsubseteq> fmap_expand \<rho>1 (fdom \<rho>2) \<Longrightarrow> fdom \<rho>1 \<subseteq> fdom \<rho>2 \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda> e. ESem e \<rho>2) \<sqsubseteq> heapToEnv (asToHeap as) (\<lambda> e. ESem e \<rho>1)"
proof(nominal_induct e and as avoiding: \<rho>1 \<rho>2  rule:exp_assn.strong_induct)
print_cases
case (Var v \<rho>1 \<rho>2)
  have "\<lbrakk> Var v \<rbrakk>\<^bsub>\<rho>2\<^esub> \<sqsubseteq> \<lbrakk> Var v \<rbrakk>\<^bsub>fmap_expand \<rho>1 (fdom \<rho>2)\<^esub>"
    by (rule cont2monofunE[OF ESem_cont Var(1)])
  also
  from Var(2)
  have "\<lbrakk> Var v \<rbrakk>\<^bsub>fmap_expand \<rho>1 (fdom \<rho>2)\<^esub> \<sqsubseteq> \<lbrakk> Var v \<rbrakk>\<^bsub>\<rho>1\<^esub>"
    apply (cases "v \<in> fdom \<rho>2")
    apply (cases "v \<in> fdom \<rho>1")
    apply (auto simp add: lookup_not_fdom)
    apply (cases "v \<in> fdom \<rho>1")
    apply (auto simp add: lookup_not_fdom)
    done
  finally show ?case.
next
case (App e v \<rho>1 \<rho>2)
  have "the (lookup \<rho>2 v) \<sqsubseteq> the (lookup (fmap_expand \<rho>1 (fdom \<rho>2)) v)"
     by (rule cont2monofunE[OF cont2cont_lookup[OF cont_id] App(2)])
  also
  from App(3)
  have "... \<sqsubseteq> the (lookup \<rho>1 v)"
    apply (cases "v \<in> fdom \<rho>2")
    apply (cases "v \<in> fdom \<rho>1")
    apply (auto simp add: lookup_not_fdom)
    apply (cases "v \<in> fdom \<rho>1")
    apply (auto simp add: lookup_not_fdom)
    done
  finally have "the (lookup \<rho>2 v) \<sqsubseteq> the (lookup \<rho>1 v)".
  moreover
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>"
    by (rule App.hyps[OF App.prems])
  ultimately
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub> \<down>Fn the (lookup \<rho>2 v) \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub> \<down>Fn the (lookup \<rho>1 v)"
    by (metis monofun_cfun monofun_cfun_arg)
  thus ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have cond1: "heapExtendJoin_cond' (asToHeap as) \<rho>1"
    (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    using Let(1) by (auto simp add: sharp_star_Env)
  have cond2: "heapExtendJoin_cond' (asToHeap as) \<rho>2"
    (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    using Let(2) by (auto simp add: sharp_star_Env)
  let "?S1" = "fix_join_compat'' ?\<rho>1 ?F1"
  let "?S2" = "fix_join_compat'' ?\<rho>2 ?F2"

  have "\<lbrace>asToHeap as\<rbrace>\<rho>2 \<sqsubseteq> fmap_expand (\<lbrace>asToHeap as\<rbrace>\<rho>1) (fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2))"
    apply (subst HSem_def)
    apply (rule heapExtendJoin_ind'[OF cond2 adm_is_adm_on])
    apply auto[1]
    apply (auto simp add: to_bot_fmap_def)[1]
    apply (subst HSem_unroll[OF cond1])
    apply (subst fmap_expand_join[OF finite_fdom rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]])

    apply (erule join_mono[OF
        rho_F_compat_jfc''[OF cond2]
        fmap_expand_compatible[OF finite_fdom rho_F_compat_jfc''[OF cond1 HSem_there[OF cond1]]]
        ])
    
    apply (rule below_trans[OF cont2monofunE[OF fmap_expand_cont `\<rho>2 \<sqsubseteq> fmap_expand \<rho>1 (fdom \<rho>2)`]])
    apply (subst fmap_expand_idem)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[3]
    apply (subst fmap_expand_idem)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[3]
    apply simp

    apply (subst fmap_expand_idem)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[3]

    using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply simp

    apply (rule cont2monofunE[OF fmap_expand_cont]) 
    apply (rule Let.hyps(3))
    apply (frule fmap_below_dom, simp)
    apply (drule fmap_below_dom)
    apply auto
    done
  moreover
  have "fdom (\<lbrace>asToHeap as\<rbrace>\<rho>1) \<subseteq> fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2)"
    using Let(6) by auto
  ultimately
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>2\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>1\<^esub> "
    by (rule Let.hyps)
  thus ?case
    using Let(1,2)
    by simp
next
case (Lam v e \<rho>1 \<rho>2)
  from `atom v \<sharp> \<rho>2`
  have "v \<notin> fdom \<rho>2" by (simp add: sharp_Env)
  {
  fix x
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>2(v f\<mapsto> x)\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>(fmap_expand \<rho>1 (fdom \<rho>2))(v f\<mapsto> x)\<^esub>"
    by (rule cont2monofunE[OF cont_compose[OF ESem_cont fmap_upd_cont[OF cont_id cont_const]] Lam(4)])
  also
  have "... = \<lbrakk> e \<rbrakk>\<^bsub>(fmap_expand (\<rho>1(v f\<mapsto> x)) (fdom (\<rho>2(v f\<mapsto> x))))\<^esub>"
    using `v \<notin> fdom \<rho>2` by (auto simp add: fmap_upd_expand)
  also
  have "... \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1(v f\<mapsto> x)\<^esub>"
    apply (rule Lam.hyps(3))
    using `fdom \<rho>1 \<subseteq> fdom \<rho>2`
    by (auto intro: Lam.hyps(3) fmap_expand_belowI)
  also note calculation 
  }
  thus ?case
    by (auto intro: cfun_belowI simp add: Lam(1) Lam(2) beta_cfun[OF cont_compose[OF ESem_cont fmap_upd_cont[OF cont_const cont_id]]])
next
case (ANil \<rho>1 \<rho>2) thus ?case by simp
next
case (ACons v e as \<rho>1 \<rho>2)
  have "heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)(v f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>) \<sqsubseteq> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>)(v f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)"
    by (rule cont2monofunE[OF fmap_upd_cont[OF cont_id cont_const] ACons.hyps(2)[OF ACons.prems]])
  also
  have "... \<sqsubseteq>  heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>)(v f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>) "
    by (rule cont2monofunE[OF fmap_upd_cont[OF cont_const cont_id] ACons.hyps(1)[OF ACons.prems]])
  finally
  show ?case by simp
qed

lemma ESem_ignores_fresh:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>"
  and
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>) = heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)"
proof (nominal_induct e and as avoiding: \<rho>1 \<rho>2 rule:exp_assn.strong_induct)
case (Var x \<rho>1 \<rho>2)
  show ?case
  proof(cases "x \<in> fdom \<rho>1")
  case True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      hence "atom x \<sharp> Var x"
        using Var(2) by (simp add: fresh_star_def)
      thus False
        by (auto simp add: exp_assn.fresh)
    qed
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
next
case (App e x \<rho>1 \<rho>2)
  from App(3)
  have "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e"
    by (auto simp add: fresh_star_def exp_assn.fresh)
  note hyps = App.hyps[OF App.prems(1) this]
  moreover
  have "the (lookup \<rho>1 x) = the (lookup \<rho>2 x)"
  proof(cases "x \<in> fdom \<rho>1")
  case True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      hence "atom x \<sharp> App e x"
        using App(3) by (simp add: fresh_star_def)
      thus False
        by (auto simp add: exp_assn.fresh)
    qed
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
  ultimately
  show ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have cond1: "heapExtendJoin_cond' (asToHeap as) \<rho>1"
      (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    using Let(1)
    by (auto simp add: sharp_star_Env)
  have cond2: "heapExtendJoin_cond' (asToHeap as) \<rho>2"
      (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
    apply (rule disjoint_is_heapExtendJoin_cond'_ESem)
    using Let(2)
    by (auto simp add: sharp_star_Env)

  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_restrict)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  unfolding HSem_def
  proof (rule parallel_heapExtendJoin_ind[OF cond1 cond2])
  case goal1 show ?case by (rule adm_is_adm_on, simp)
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[2]
      done
  case (goal3 \<rho>1' \<rho>2')
    have [simp]:"fdom \<rho>1' = fdom \<rho>1 \<union> fst ` set (asToHeap as)" and [simp]:"fdom \<rho>2' = fdom \<rho>2 \<union> fst ` set (asToHeap as)"
      using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond1] goal3(1)]
      using fdom_fix_join_compat''[OF fix_on_cond_jfc''[OF cond2] goal3(2)]
      by simp+  
    note compat1 = rho_F_compat_jfc''[OF cond1 goal3(1)]
    note compat2 = rho_F_compat_jfc''[OF cond2 goal3(2)]

    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* as"
      using Let(6) Let(1) Let(2)
      apply (auto simp add: sharp_star_Env fresh_star_def exp_assn.fresh)
      by (metis Diff_iff sharp_Env)

    show "?\<rho>1 \<squnion> ?F1 \<rho>1' \<le> ?\<rho>2 \<squnion> ?F2 \<rho>2'"
    proof(rule fmap_less_eqI)
    case goal1
      show ?case
        apply (subst fdom_join[OF compat1])
        apply (subst fdom_join[OF compat2])
        using `fdom \<rho>1 \<subseteq> fdom \<rho>2`
        by auto
    next
    case (goal2 x)
      hence dom: "x \<in> fdom \<rho>1 \<union> fst ` set (asToHeap as)"      
        apply (subst (asm) fdom_join[OF compat1])
        by simp
      hence dom2: "x \<in> fdom \<rho>2 \<union> fst ` set (asToHeap as)"
        by (auto intro: set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])

      have "lookup ?\<rho>1 x = lookup ?\<rho>2 x"
      proof (cases "x \<in> fdom \<rho>1")
      case True
        hence "x \<in> fdom \<rho>2" by (rule set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])
        with True show ?thesis
          by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
      next
      case False
        hence "x \<notin> fdom \<rho>2"
          using Let(2) dom 
          by (auto simp add: sharp_star_Env)
        with False dom show ?thesis by (simp add: lookup_not_fdom)
      qed
      moreover
      have "lookup (?F1 \<rho>1') x = lookup (?F2 \<rho>2') x"
      proof (cases "x \<in> fst`set (asToHeap as)")
      case True
        thus ?thesis
          by (simp add: Let(3)[OF goal3(3) prem])
      next
      case False
        thus ?thesis
          using dom dom2 by simp
      qed
      ultimately
      show ?case
        apply (subst the_lookup_join[OF compat1])
        apply (subst the_lookup_join[OF compat2])
        by simp
    qed
  qed
  moreover
  have "atom ` (fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2) - fdom (\<lbrace>asToHeap as\<rbrace>\<rho>1)) \<sharp>* e "
    using Let(6) Let(1) Let(2)
    apply (auto simp add: sharp_star_Env fresh_star_def exp_assn.fresh)
    by (metis Diff_iff sharp_Env)
  ultimately
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>2\<^esub>"
    apply (rule Let.hyps(4))
    done
  thus "\<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Let.hyps(1,2) by simp
next
case (Lam x e \<rho>1 \<rho>2)
  { fix v
    have "\<rho>1(x f\<mapsto> v) \<le> \<rho>2(x f\<mapsto> v)"
      apply (rule fmap_less_eqI)
      using fmap_less_fdom[OF Lam(4)] apply auto[1]
      apply (case_tac "xa = x")
      by (auto simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
    moreover
    have "atom ` (fdom (\<rho>2(x f\<mapsto> v)) - fdom (\<rho>1(x f\<mapsto> v))) \<sharp>* e"
      using Lam(5)
      by (auto simp add: fresh_star_def exp_assn.fresh)
    ultimately
    have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1(x f\<mapsto> v)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2(x f\<mapsto> v)\<^esub>"
      by (rule Lam(3))
  }
  thus "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Lam(1,2)
    by simp
next
case ANil
  thus ?case by simp
next
case (ACons x e as \<rho>1 \<rho>2)
  from ACons(4)
  have prem1: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e" and  prem2: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as"
    by (auto simp add: fresh_star_def exp_assn.fresh)
  from ACons.hyps(1)[OF `\<rho>1 \<le> \<rho>2` prem1] ACons.hyps(2)[OF `\<rho>1 \<le> \<rho>2` prem2]
  show ?case by simp
qed

lemma HSem_add_fresh:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x,e) # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
  shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
unfolding HSem_def
proof(rule heapExtendJoin_add_fresh[OF assms, unfolded heapVars_def[symmetric]])
case (goal1 e \<rho>')
  assume "e \<in> snd ` set \<Gamma>"
  hence "atom x \<sharp> e"
    apply auto
    by (metis fresh fresh_PairD(2) fresh_list_elem)

  assume "fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"
  hence [simp]:"fdom \<rho>' - fdom \<rho>' \<inter> (fdom \<rho>' - {x}) = {x}" by auto

  show ?case
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
    apply (simp add: fresh_star_def)
    using `atom x \<sharp> e`.
qed

lemma ESem_add_fresh:
  assumes cond1: "heapExtendJoin_cond' \<Gamma> \<rho>"
  assumes cond2: "heapExtendJoin_cond' ((x,e') # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>, e)"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
proof(rule ESem_ignores_fresh[symmetric])
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_restr (fdom \<rho> \<union> fst ` set \<Gamma>) (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) "
    apply (rule HSem_add_fresh[OF assms(1,2), symmetric, unfolded heapVars_def])
    using fresh by (simp add: fresh_Pair)
  thus "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (auto simp add: fmap_less_restrict)

  have "(insert x (fdom \<rho> \<union> fst ` set \<Gamma>) - (fdom \<rho> \<union> fst ` set \<Gamma>)) = {x}"
    using fresh
    apply (auto simp add: fresh_Pair sharp_Env)
    by (metis fresh_PairD(1) fresh_list_elem not_self_fresh)
  thus "atom ` (fdom (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) - fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>)) \<sharp>* e"
    using fresh
    by (simp add: fresh_star_def fresh_Pair)
qed


end
