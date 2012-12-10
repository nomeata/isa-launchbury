theory "Denotational-PropsUpd"
  imports "DenotationalUpd"  "HOLCF-Utils"
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
  have "range (\<lambda>i. HSem (asToHeap as)  (Y i)) <<| HSem (asToHeap as) (Lub Y)"
    apply (rule range_is_lubI2)
    apply (rule HSem_monofun'')
      apply (erule Let.hyps(2))
      apply (rule chainE[OF `chain Y`])
    apply (rule HSem_monofun'')
      apply (erule Let.hyps(2))
      apply (rule is_ub_thelub[OF `chain Y`])
    apply (rule HSem_cont'')
      apply (erule Let.hyps(2))
      apply (rule `chain Y`)
   done
  moreover
  have "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule HSem_monofun'')
      apply (erule Let.hyps(2))
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

interpretation has_cont_ESem ESem
  apply default
  using ESem_cont'[OF refl]
  by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation HSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"

abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"


(*

lemma fresh_fmap_upd'[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom x \<sharp> a ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)"
  by (metis fresh_at_base(2) fresh_fmap_upd)
  
lemma fresh_fmap_upd_lookup[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> the (lookup \<rho> y))"
  by (auto simp add: fresh_append fresh_star_fmap_upd_eq intro: eqvt_fresh_star_cong2[where f = fmap_delete, OF fmap_delete_eqvt])


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
    apply (subst * )
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
*)

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

  have lookup_other: "\<And> \<rho> . the (lookup (\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>) y) = the (lookup \<rho> y)"
    using `y \<notin> assn_vars as`
    by (auto simp add: the_lookup_HSem_other)

  have [simp]:"fdom \<rho> \<union> assn_vars as - {x} = fdom \<rho> \<union> assn_vars as"
    using `x \<notin> assn_vars as` `atom x \<sharp> \<rho>` by (auto simp add: sharp_Env)

  have *: "fmap_expand (\<rho>(x f\<mapsto> the (lookup \<rho> y))) (fdom (\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<union> fst ` set (asToHeap as))
        = (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set (asToHeap as)))(x f\<mapsto> the (lookup \<rho> y))" (is "_ = ?\<rho>1'(x f\<mapsto> _)")
    apply (subst fmap_upd_expand)
    apply auto[3]
    done

  let ?b1 = "fmap_bottom (fdom (\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<union> fst ` set (asToHeap as))"
  let ?b2 = "fmap_bottom (fdom \<rho> \<union> fst ` set (asToHeap as[x::a=y]))"
  let ?\<rho>1 = "\<rho>(x f\<mapsto> the (lookup \<rho> y))"
  let ?\<rho>2 = \<rho>
  let ?F1 = "\<lambda>\<rho>' . heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  let ?F2 = "\<lambda>\<rho>' . heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  let ?L = "fix_on' ?b1 (\<lambda> \<rho>'. ?\<rho>1 f++ ?F1 \<rho>')"
  let ?R = "fix_on' ?b2 (\<lambda> \<rho>'. ?\<rho>2 f++ ?F2 \<rho>')"

  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<sqsubseteq> (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> the (lookup (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>) y))"
    (is "?L \<sqsubseteq> ?R( x f\<mapsto> the (lookup ?R y))")
  proof (rule HSem_ind) back back back
  case goal1 show ?case by simp
  case goal2 show ?case by simp
  case (goal3 \<rho>')
    have "?\<rho>1 f++ ?F1 \<rho>' = (\<rho> f++ ?F1 \<rho>')(x f\<mapsto> the (lookup \<rho> y))"
      apply (rule fmap_add_upd_swap)
      using `x \<notin> assn_vars as` by simp
    also
    have  "... \<sqsubseteq> (\<rho> f++ ?F2 ?R)( x f\<mapsto> the (lookup \<rho> y))"
    proof (rule cont2monofunE[OF fmap_upd_cont[OF fmap_add_cont2 cont_const]])
      have "?F1 \<rho>' \<sqsubseteq> ?F1 (?R( x f\<mapsto> the (lookup ?R y)))"
        by (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      also
      have "... = ?F2 ?R"
        apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
        using `x \<notin> assn_vars as`  `atom x \<sharp> \<rho>` apply (simp add: sharp_Env)
        by rule
      finally
      show "?F1 \<rho>' \<sqsubseteq> ?F2 ?R".
    qed
    also have "... = ?R( x f\<mapsto> the (lookup \<rho> y))"
      by (rule arg_cong[OF HSem_eq[symmetric]])
    also have "... = ?R( x f\<mapsto> the (lookup ?R y))"
      using `y \<notin> assn_vars as` by (simp add: the_lookup_HSem_other)
    finally
    show "?\<rho>1 f++ ?F1 \<rho>' \<sqsubseteq> ?R( x f\<mapsto> the (lookup ?R y))".
  qed
  also
  have "?R (x f\<mapsto> the (lookup ?R y)) \<sqsubseteq> ?L"
  proof (rule HSem_ind) back 
  case goal1 show ?case by auto
  case goal2 show ?case
    using `y \<notin> assn_vars as` `x \<notin> assn_vars as`
    apply (auto intro!: fmap_upd_belowI simp  add: the_lookup_HSem_other)
    apply (cases "y \<in> fdom \<rho>")
    apply simp
    apply (simp add: lookup_not_fdom)
    done
  case (goal3 \<rho>')
    (* show "(?\<rho>2 f++ ?F2 \<rho>') (x f\<mapsto> the (lookup (?\<rho>2 f++ ?F2 \<rho>') y)) \<sqsubseteq> ?L". *)

    have "(?\<rho>2 f++ ?F2 \<rho>') (x f\<mapsto> the (lookup (?\<rho>2 f++ ?F2 \<rho>') y)) = (?\<rho>2 f++ ?F2 \<rho>')(x f\<mapsto> the (lookup \<rho> y))"
      using `y \<notin> assn_vars as` by simp
    also
    have "... = (?\<rho>1 f++ ?F2 \<rho>')"
      apply (rule fmap_add_upd_swap[symmetric])
      using `x \<notin> assn_vars as` by simp
    also
    have "... = ?\<rho>1 f++ ?F1 (\<rho>'(x f\<mapsto> the (lookup \<rho>' y)))"
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y` ])
      using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as` goal3(1) apply (simp add: sharp_Env)
      by rule
    also
    have  "... \<sqsubseteq> ?\<rho>1 f++ ?F1 ?L"
      by (rule cont2monofunE[OF fmap_add_cont2cont[OF cont_const cont2cont_heapToEnv[OF ESem_cont]]  `\<rho>'(x f\<mapsto> the (lookup \<rho>' y)) \<sqsubseteq> ?L`])
    also
    have  "... = ?L"
      by (rule HSem_eq[symmetric])
    finally
    show "(?\<rho>2 f++ ?F2 \<rho>') (x f\<mapsto> the (lookup (?\<rho>2 f++ ?F2 \<rho>') y)) \<sqsubseteq> ?L".
  qed
  finally
  show ?case
    using Let
    by (auto simp add: fresh_star_Pair fresh_at_base)[1]
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

(*
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
  have cond1: "HSem_cond' (asToHeap as) \<rho>1"
    (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    using Let(1) by (auto simp add: sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as) \<rho>2"
    (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    using Let(2) by (auto simp add: sharp_star_Env)
  let "?S1" = "fix_join_compat'' ?\<rho>1 ?F1"
  let "?S2" = "fix_join_compat'' ?\<rho>2 ?F2"

  have "\<lbrace>asToHeap as\<rbrace>\<rho>2 \<sqsubseteq> fmap_expand (\<lbrace>asToHeap as\<rbrace>\<rho>1) (fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2))"
    apply (rule HSem_ind'[OF cond2 adm_is_adm_on]) back back
    apply auto[1]
    apply (auto simp add: to_bot_fmap_def)[1]
    apply (subst HSem_eq[OF cond1])
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
*)

(*
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
  have cond1: "HSem_cond' (asToHeap as) \<rho>1"
      (is "fix_on_cond_jfc' ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    using Let(1)
    by (auto simp add: sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as) \<rho>2"
      (is "fix_on_cond_jfc' ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    using Let(2)
    by (auto simp add: sharp_star_Env)

  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_restrict)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_HSem_ind[OF cond1 cond2])
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
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e) # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
  shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
proof(rule HSem_add_fresh[OF assms, unfolded heapVars_def[symmetric]])
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
*)

(*
lemma ESem_add_fresh:
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e') # \<Gamma>) \<rho>"
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
*)

end
