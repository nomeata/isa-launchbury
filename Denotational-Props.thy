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
    apply (rule heapExtendJoin_cont'')
      apply (erule Let.hyps(2))
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset[unfolded fdoms] conts])
      apply (rule disjoint_is_heapExtendJoin_cond'[OF unset conts])
      apply (rule `chain Y`)
   done
  moreover
  have "chain (\<lambda>i. heapExtendJoin (Y i) (asToHeap as) ESem)" sorry
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

thm disjoint_is_heapExtendJoin_cond'

lemma HSem_def': "heapExtendJoin_cond' \<Gamma> ESem \<rho> \<Longrightarrow>
  \<lbrace>\<Gamma>\<rbrace>\<rho> = fix_on (fix_join_compat' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set \<Gamma>)))
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
  by(auto intro: disjoint_is_heapExtendJoin_cond')

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  apply (subst HSem_def') apply auto
  apply (subst subpcpo.fix_on_const[OF subpcpo_jfc'])
  apply auto[1]
  apply (metis join_above1 below.r_refl compatibleI to_bot_fmap_def to_bot_minimal)
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
  apply simp
  apply (subst the_lookup_join)
  apply (metis heapExtendJoin_cond'D)
  apply simp
  apply simp
  
  apply (cases "heapExtendJoin_cond' \<Gamma> ESem \<rho>")
  apply (subst heapExtendJoin_eq, assumption)
  apply (subst the_lookup_join)
  apply (erule heapExtendJoin_cond'D)
  apply (rule heapExtendJoin_compatible)
  apply simp
  apply (simp add: heapExtendJoin_def)
  apply (simp add: lookup_not_fdom)
  done

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


lemma tmp:"fmap_update \<rho> ((iterate i F) \<cdot> x) = (iterate i (\<Lambda> x. fmap_update \<rho> (F \<cdot> x))) \<cdot> (fmap_update \<rho> x)" sorry

lemmas tmp2 =  cont2contlubE[of "\<lambda> y. (iterate i (\<Lambda> \<rho>'. fmap_update \<rho> ((y)(x f\<mapsto> G \<rho>'))))\<cdot>x0", standard]
thm tmp2


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

lemma HSem_refines:
  "heapExtendJoin_cond' \<Gamma> ESem \<rho>' \<Longrightarrow> fmap_expand \<rho>' (fdom \<rho>' \<union> fst ` set \<Gamma>)  \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>'"
  apply (subst HSem_unroll, assumption)
  apply (rule join_above1)
  apply (erule heapExtendJoin_cond'D)
  apply (rule HSem_compat)
  done

lemma iterative_HSem:
  assumes "heapExtendJoin_cond' ((x, e) # \<Gamma>) ESem \<rho>"
  shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> =
      fix_on (fix_join_compat' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))))
              (\<lambda> \<rho>'. (\<lbrace>\<Gamma>\<rbrace>\<rho>')
                      \<squnion> (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))(x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>) 
                      \<squnion> (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))))" (is "_ = fix_on ?S ?R")
apply (subst HSem_def'[OF assms])
proof(rule below_antisym)
  interpret subpcpo ?S by (rule subpcpo_jfc')

  let "?d" = "fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)"

  let "fix_on _ ?L" = "fix_on ?S
                       (\<lambda>\<rho>'. fmap_expand \<rho> ?d \<squnion>
                             fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))"
  let "(\<lambda> \<rho>'. ?L1 \<rho>' \<squnion> ?L2 \<rho>')" = ?L
  let "(\<lambda> \<rho>'. ?R1 \<rho>' \<squnion> (?R2 \<rho>' \<squnion> ?R3 \<rho>'))" = ?R

  have contL: "cont_on ?S ?L"
    by (rule cont_on_jfc'[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] heapExtendJoin_cond'D[OF assms]])
  have closedL: "closed_on ?S ?L"
    by (rule closed_on_jfc'[OF cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]] heapExtendJoin_cond'D[OF assms]])
  have contR: "cont_on ?S ?R" sorry
  have closedR: "closed_on ?S ?R" sorry

  have R_there: "fix_on ?S ?R \<in> ?S"
    by (rule fix_on_there[OF contR closedR])

  have compatL: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?L1 x) (?L2 x)"
    by (metis assms fjc'_iff heapExtendJoin_cond'D)
  have compatR2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R2 x) (?R3 x)"
    sorry
  have compatR1R2: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x)"
    sorry
  have compatR1R2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x \<squnion> ?R3 x)"
    sorry
  have compatR1R2R3': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x \<squnion> ?R2 x) (?R3 x)"
    sorry

  show "fix_on ?S ?L \<sqsubseteq> fix_on ?S ?R"
    proof (rule fix_on_mono[OF closedL contL closedR contR])
    fix \<rho>'
    assume there: "\<rho>' \<in> ?S"
    hence [simp]:"fdom \<rho>' = ?d"
      apply (simp)
      apply (erule subst[OF fdom_compatible])
      apply simp
      done
    hence Gamma_in_fdom[simp]: "fdom \<rho>' \<union> fst ` set \<Gamma> = fdom \<rho>'" by auto

    have inner_cond: "heapExtendJoin_cond' \<Gamma> ESem \<rho>'"
      apply (rule heapExtendJoin_cond'I)
      defer
      apply (simp)
      apply (subst (asm) fmap_expand_noop[OF Gamma_in_fdom])
      apply (subst fmap_expand_noop[OF Gamma_in_fdom])
      thm there
      thm there[unfolded fix_join_compat'_def, simplified]
      (* Here be dragons *)
      sorry
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
            apply (subst the_lookup_join[OF heapExtendJoin_cond'D[OF inner_cond HSem_compat]])
            apply (insert the_lookup_compatible[OF heapExtendJoin_cond'D[OF inner_cond HSem_compat], of x'])
            apply (subst (2) lookup_fmap_expand1)
            apply (simp_all add: True)[3]
            apply (subst (asm) (2) lookup_fmap_expand1)
            apply (simp_all add: True)[3]
            apply (erule below_trans[OF _ join_above2, rotated])
            thm cont2monofunE[OF _ inner_refine]
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

  show "fix_on ?S ?R \<sqsubseteq> fix_on ?S ?L" sorry
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
