theory ArityEtaExpandInst
imports ArityCorrectSestoft EtaExpansionSestoft TransformTools AbstractTransform
begin

lift_definition Aeta_expand :: "Arity \<Rightarrow> exp \<Rightarrow> exp" is "eta_expand".

lemma Aeta_expand_eqvt[eqvt]: "\<pi> \<bullet> Aeta_expand a e = Aeta_expand (\<pi> \<bullet> a) (\<pi> \<bullet> e)"
  apply (cases a)
  apply simp
  apply transfer
  apply simp
  done

lemma Aeta_expand_0[simp]: "Aeta_expand 0 e = e"
  by transfer simp

lemma Aeta_expand_inc[simp]: "Aeta_expand (inc\<cdot>n) e = (Lam [fresh_var e]. Aeta_expand n (App e (fresh_var e)))"
  apply (simp add: inc_def)
  by transfer simp

lemma subst_Aeta_expand:
  "(Aeta_expand n e)[x::=y] = Aeta_expand n e[x::=y]"
  by transfer (rule subst_eta_expand)

lemma Aeta_expand_correct:
  assumes "ae ` upds S \<subseteq> {up \<cdot> 0}"  
  assumes "Astack ae S \<sqsubseteq> a"
  shows "(\<Gamma>, Aeta_expand a e, S) \<Rightarrow>\<^sup>* (\<Gamma>, e, S)"
proof-
  from assms(1)
  have "arg_prefix S = Rep_Arity (Astack ae S)"
    by (induction S arbitrary: a rule: arg_prefix.induct) (auto simp add: Arity.zero_Arity.rep_eq[symmetric])
  also
  from assms(2)
  have "Rep_Arity a \<le> Rep_Arity (Astack ae S)" by (metis below_Arity.rep_eq)
  finally
  show ?thesis by transfer (rule eta_expansion_correct')
qed

lemma isLam_Aeta_expand: "isLam e \<Longrightarrow> isLam (Aeta_expand a e)"
  by transfer (rule isLam_eta_expand)

lemma Aeta_expand_fresh[simp]: "a \<sharp> Aeta_expand n e = a \<sharp> e" by transfer simp
lemma Aeta_expand_fresh_star[simp]: "a \<sharp>* Aeta_expand n e = a \<sharp>* e" by (auto simp add: fresh_star_def)

interpretation supp_bounded_transform Aeta_expand
  apply default
  using Aeta_expand_fresh
  apply (auto simp add: fresh_def)
  done

locale ArityEtaExpand = CorrectArityAnalysisLet
begin
  lemma Aeta_expand_pres_Aexp:
  "Aexp (Aeta_expand n e)\<cdot>n = Aexp e\<cdot>n"
    apply (induction n arbitrary:e rule: Arity_ind)
    apply simp
    apply (simp add: Aexp_App Aexp_Lam)
    apply (subgoal_tac "fresh_var e \<notin> edom (Aexp e\<cdot>(inc\<cdot>n))")
    apply simp
    by (metis Aexp_lookup_fresh edomIff fresh_var_fresh)

  sublocale AbstractTransformBound
    "\<lambda> e x a . inc\<cdot>a"
    "\<lambda> x e a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . a"
    "\<lambda> \<Delta> e a . Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)"
    "Aeta_expand"
  apply default
  apply ((rule eq_reflection)?, perm_simp, rule)+
  done

  abbreviation Atransform where "Atransform \<equiv> transform"

  lemma the_map_option_domA[simp]: "x \<in> domA \<Gamma> \<Longrightarrow> the (map_option f (map_of \<Gamma> x)) = f (the (map_of \<Gamma> x))"
    by (induction \<Gamma>) auto

 (*
  lemma trans_pres_Aexp: "Aexp (Atransform a e)\<cdot>a = Aexp e\<cdot>a"
  apply (nominal_induct e arbitrary: a  rule: exp_strong_induct)
  apply (case_tac b)
  apply simp_all[2]
  apply (auto simp add: Aexp_App)[1]
  defer
  apply (auto cong add: Aexp_Lam)[1]
  apply simp
  apply (rule Aexp_Let_cong)
  apply simp
  defer
  apply simp
  thm Aheap_cong[where \<Gamma> = "map_transform Atransform (Aheap \<Gamma>\<cdot>(Aexp exp\<cdot>a)) \<Gamma>" and \<Gamma>' = \<Gamma> for \<Gamma> exp]
  apply (subgoal_tac "Aheap (map_transform Atransform (Aheap \<Gamma>\<cdot>(Aexp exp\<cdot>a)) \<Gamma>)\<cdot>(Aexp exp\<cdot>a) = Aheap \<Gamma>\<cdot>(Aexp exp\<cdot>a)")
  apply simp
  defer
  apply (rule Aheap_cong)
    apply simp
    apply (simp add: map_of_map_transform option.map_comp)
  apply (rule Aheap_cong)
    apply simp
    apply (simp add: map_of_map_transform option.map_comp Aeta_expand_pres_Aexp)
  done
  
  lemma trans_pres_Aheap: "Aheap (map_transform Atransform (Aheap \<Delta>\<cdot>ae) \<Delta>)\<cdot>ae = (Aheap \<Delta>\<cdot>ae)"
    by (rule Aheap_cong) (simp_all add: map_of_map_transform trans_pres_Aexp)
  *)

  (* Check simp rules *)
  lemma "transform a (App e x) = App (transform (inc\<cdot>a) e) x" by simp
  lemma "transform a (Lam [x]. e) = Lam [x].(transform (pred\<cdot>a) e)" by simp
  lemma "transform a (GVar b x) = GVar b x" by (cases b) simp_all
  lemma "transform a (Terms.Let \<Delta> e) = Let (map_transform Aeta_expand (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) (map_transform transform (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<Delta>))
           (transform a e)" by (simp del: Let_eq_iff)

lemma supp_transform: "supp (transform a e) \<subseteq> supp e"
  by (induction rule: transform.induct)
     (auto simp add: exp_assn.supp Let_supp dest!: set_mp[OF supp_map_transform] set_mp[OF supp_map_transform_step] )

lemma subst_Aeta_expand_transform: "(transform a e)[x ::= y] = transform a e[x ::= y]"
proof (nominal_induct e avoiding: x y arbitrary: a  rule: exp_strong_induct_set)
  case (Let \<Delta> body x y)
    hence *: "x \<notin> domA \<Delta>" "y \<notin> domA \<Delta>" by (auto simp add: fresh_star_def fresh_at_base)
    
    note Let
    moreover                         
    from * have "Aheap \<Delta>[x::h=y] = Aheap \<Delta>" by (rule Aheap_subst)
    moreover
    have "(Aexp body[x::=y]\<cdot>a) f|` domA \<Delta> = (Aexp body\<cdot>a) f|` domA \<Delta>"
      by (rule Aexp_subst_restr[OF *])
    hence "Aheap \<Delta>\<cdot>(Aexp body[x::=y]\<cdot>a) = Aheap \<Delta>\<cdot>(Aexp body\<cdot>a)"
      by (rule Aheap_cong)
    ultimately
    show ?case
    apply (auto simp add: fresh_star_Pair simp del: Let_eq_iff)
    apply (rule arg_cong2[where f = Let, OF _ refl])
    apply (subst subst_map_transform)
    apply (rule subst_Aeta_expand)
    apply (subst subst_map_transform)
    apply assumption
    apply (rule map_transform_cong)
    apply simp
    apply (rule map_transform_cong)
    apply simp
    apply simp
    done
qed (case_tac b, auto)

  fun conf_transform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "conf_transform (ae, a) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>), 
     transform a e,
     S)"

  inductive consistent :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ae \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> upds S \<subseteq> edom ae
    \<Longrightarrow> Astack ae S \<sqsubseteq> a
(*    \<Longrightarrow> AEstack ae S \<sqsubseteq> ae  *)
    \<Longrightarrow> Aexp e \<cdot> a \<sqsubseteq> ae
    \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> Aexp' e \<cdot> (ae x) \<sqsubseteq> ae)
    \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> ae ` ap S \<subseteq> {up\<cdot>0}
    \<Longrightarrow> ae ` upds S \<subseteq> {up\<cdot>0}
    \<Longrightarrow> consistent (ae, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, a) (\<Gamma>, e, S)"

  interpretation supp_bounded_transform transform
    by default (auto simp add: fresh_def supp_transform)
  
  lemma isLam_Aeta_expand_transform[simp]:
    "isLam (Atransform a e) \<longleftrightarrow> isLam e"
    by (induction e rule:isLam.induct) (case_tac b, auto)

(*
  sublocale AbstractConforms step consistent.
*)

lemma foo:
  fixes c c' R 
  assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,a) c"
  shows "\<exists>ae' a'. consistent (ae',a') c' \<and> conf_transform (ae,a) c \<Rightarrow>\<^sup>* conf_transform (ae',a') c'"
using assms
proof(induction c c' arbitrary: ae a rule:step_induction)
case (app\<^sub>1 \<Gamma> e x S)
  from app\<^sub>1 have "consistent (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"  by (fastforce simp add: Aexp_App join_below_iff)
  moreover
  have "conf_transform (ae, a) (\<Gamma>, App e x, S) \<Rightarrow> conf_transform (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)" by simp rule
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (app\<^sub>2 \<Gamma> y e x S)
  have "Aexp (e[y ::= x])\<cdot>(pred\<cdot>a) \<sqsubseteq> ae" using app\<^sub>2
    apply (auto simp add:  join_below_iff)
    apply (rule below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]])
    apply (auto simp add: Aexp_App Aexp_Lam join_below_iff)
    done
  hence "consistent (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)"  using app\<^sub>2
    apply  (auto intro!:  below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]] simp add: Aexp_App join_below_iff monofun_cfun_arg)
    apply (metis image_eqI singletonD subsetCE)+
    done
  moreover
  have "conf_transform (ae, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> conf_transform (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_Aeta_expand_transform[symmetric]) rule
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (thunk \<Gamma> x e S)
  hence "consistent (ae, 0) (delete x \<Gamma>, e, Upd x # S)" using thunk by (fastforce simp add: join_below_iff)
  moreover
  {
  from thunk
  have "ae x = up\<cdot>0" by auto
  with  `map_of \<Gamma> x = Some e`
  have "map_of (map_transform Aeta_expand ae (map_transform Atransform ae \<Gamma>)) x = Some (transform 0 e)"
    by (simp add: map_of_map_transform)
  with `\<not> isLam e`
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow> conf_transform (ae, 0) (delete x \<Gamma>, e, Upd x # S)"
    by (auto simp add: map_transform_delete intro!: step.intros)
  }
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (lamvar \<Gamma> x e S)
  from lamvar have "ae ` upds S \<subseteq> {up \<cdot> 0}" by fastforce
  from lamvar have "Astack ae S \<sqsubseteq> a" by auto

  from lamvar have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto


  from this(2)
  have "Aexp e\<cdot>a \<sqsubseteq> Aexp e\<cdot>u" by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> u` lamvar by fastforce
  finally have "Aexp e\<cdot>a \<sqsubseteq> ae" by this simp
  moreover
  have "Aexp' e\<cdot>(ae x) \<sqsubseteq> ae" using lamvar by auto
  hence "Aexp e\<cdot>u \<sqsubseteq> ae" using `ae x = up\<cdot>u` by simp
  ultimately
  have "consistent (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    using lamvar by (auto  simp add: join_below_iff split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`])
  moreover
  {
  from `isLam e`
  have "isLam (Atransform u e)" by simp
  hence "isLam (Aeta_expand u (Atransform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u`
  have "map_of (map_transform Aeta_expand ae (map_transform Atransform ae \<Gamma>)) x = Some (Aeta_expand u (Atransform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
        ((x, Aeta_expand u (Atransform u e)) # (map_transform Aeta_expand ae (map_transform Atransform ae (delete x \<Gamma>))), Aeta_expand u  (Atransform u e), S)"
     by (auto intro: lambda_var simp add: map_transform_delete)
  also have "\<dots> = ((map_transform Aeta_expand ae (map_transform Atransform ae ((x,e) # delete x \<Gamma>))), Aeta_expand u  (Atransform u e), S)"
    using `ae x = up \<cdot> u` by (simp add: map_transform_Cons)
  also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* conf_transform (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    apply simp
    by (rule Aeta_expand_correct[OF `ae \` upds S \<subseteq> {up \<cdot> 0}` below_trans[OF `Astack ae S \<sqsubseteq> a` `a \<sqsubseteq> u`]])
  finally(rtranclp_trans)
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* conf_transform (ae, u) ((x, e) # delete x \<Gamma>, e, S)".
  }
  ultimately show ?case by (blast del: consistentI consistentE)
next
case (var\<^sub>2 \<Gamma> x e S)
  hence "ae x = up\<cdot>0" by auto

  have "Astack ae (Upd x # S) \<sqsubseteq> a" using var\<^sub>2 by auto
  with `ae x = up \<cdot> 0`
  have "a = 0" by auto

  have "consistent (ae, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
    by (fastforce  simp add: join_below_iff split:if_splits)
  moreover
  have "conf_transform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> conf_transform (ae, 0) ((x, e) # \<Gamma>, e, S)"
    using `ae x = up\<cdot>0` `a = 0` var\<^sub>2 by (auto intro!: step.intros simp add: map_transform_Cons)
  ultimately show ?case by (blast del: consistentI consistentE)
next
  case (let\<^sub>1 \<Delta> \<Gamma> e S)

  let ?ae = "Aheap \<Delta> \<cdot> (Aexp e\<cdot>a)"
  let ?new = "(domA (\<Delta> @ \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S))"
  have new: "?new = domA \<Delta>"
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (auto dest: set_mp[OF ups_fv_subset])

  have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: set_mp[OF ups_fv_subset])
  hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))"
    using edom_Aheap[where \<Gamma> = \<Delta> and ae = "Aexp e\<cdot>a"] by auto
  hence stack: "AEstack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a) \<squnion> ae) S = AEstack ae S"
               "Astack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a) \<squnion> ae) S = Astack ae S"
    by (auto simp add: edomIff cong: AEstack_cong Astack_cong)


  have "edom ae \<subseteq> - domA \<Delta>" using let\<^sub>1(3)
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (fastforce dest: set_mp[OF ups_fv_subset])
  hence "(?ae \<squnion> ae) f|` (- domA \<Delta>) = ae"
    by (auto simp add: env_restr_join  env_restr_useless disjoint_eq_subset_Compl edom_Aheap)
  moreover
  {
  have "edom (?ae \<squnion> ae) \<subseteq> domA (\<Delta> @ \<Gamma>) \<union> upds S"
    using let\<^sub>1(3) by (auto dest: set_mp[OF edom_Aheap])
  moreover
  have "upds S \<subseteq> edom (?ae \<squnion> ae)"
    using let\<^sub>1(3) by auto
  (*
  moreover
  have "AEstack ae S \<sqsubseteq> ae" using let\<^sub>1(3) by auto
  hence "AEstack ae S \<sqsubseteq> ?ae \<squnion> ae" by (metis join_above1 below_refl box_below join_comm)
  *)
  moreover
  { fix x e'
    assume "map_of \<Delta> x = Some e'"
    hence "x \<notin> edom ae" using `edom ae \<subseteq> - domA \<Delta>` by (metis Compl_iff contra_subsetD domI dom_map_of_conv_domA)
    hence "Aexp' e'\<cdot>((?ae \<squnion> ae) x) = Aexp' e'\<cdot>(?ae x)" by (auto simp add: edomIff)
    also
    have "Aexp' e'\<cdot>(?ae x) \<sqsubseteq> (Aexp' e'\<cdot>(?ae x) f|` domA \<Delta>) \<squnion> (Aexp' e'\<cdot>(?ae x) f|` (- domA \<Delta>))"
      by (rule eq_imp_below[OF join_env_restr_UNIV[symmetric]]) auto
    also
    from `map_of \<Delta> x = Some e'`
    have "Aexp' e'\<cdot>(?ae x) f|` domA \<Delta> \<sqsubseteq> ?ae" by (rule Aheap_heap)
    also
    from `map_of \<Delta> x = Some e'`
    find_theorems Aheap name:heap
    have "Aexp' e'\<cdot>(?ae x) f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>a" by (rule Aheap_heap2)
    also
    have "Aexp (Terms.Let \<Delta> e)\<cdot>a \<sqsubseteq> ae" using let\<^sub>1(3) by auto
    finally
    have "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ?ae \<squnion> ae" by this auto
  }
  moreover
  { fix x e'
    assume "map_of \<Gamma> x = Some e'"
    hence "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
    hence "x \<notin> edom ?ae" using fresh_distinct[OF let\<^sub>1(1)]  by (auto dest: set_mp[OF edom_Aheap])
    with let\<^sub>1 `map_of \<Gamma> x = Some e'`
    have "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ae" by (auto simp add: edomIff)
    hence "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ?ae \<squnion> ae" by (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" below_trans)
  }
  moreover
  { fix x e'
    assume "\<not> isLam e'"
    assume "map_of \<Gamma> x = Some e'"
    hence "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
    hence "x \<notin> edom ?ae" using fresh_distinct[OF let\<^sub>1(1)]  by (auto dest: set_mp[OF edom_Aheap])
    with let\<^sub>1 `map_of \<Gamma> x = Some e'` `\<not> isLam e'`
    have "(?ae \<squnion> ae) x = up \<cdot>0" by (auto simp add: edomIff)
  }
  moreover
  { fix x e'
    assume "map_of \<Delta> x = Some e'" and "\<not> isLam e'"
    hence "?ae x = up \<cdot> 0" using Aheap_heap3 by auto
    hence "(?ae \<squnion> ae) x = up \<cdot> 0" by simp
  }
  moreover
  have "(?ae \<squnion> ae) ` upds S \<subseteq> {up \<cdot> 0}" using let\<^sub>1 * by fastforce
  moreover
  have "(?ae \<squnion> ae) ` ap S \<subseteq> {up \<cdot> 0}" using let\<^sub>1 * by fastforce
  moreover
  have "Astack (?ae \<squnion> ae) S \<sqsubseteq> a" unfolding stack using let\<^sub>1 by auto
  moreover
  {
  have "Aexp e\<cdot>a \<sqsubseteq> (Aexp e\<cdot>a f|` domA \<Delta>) \<squnion> (Aexp e\<cdot>a f|` (- domA \<Delta>))"
    by (rule eq_imp_below[OF join_env_restr_UNIV[symmetric]]) auto
  also have "Aexp e\<cdot>a f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>a" by (rule Aexp_Let_above)
  also have "\<dots> \<sqsubseteq> ae" using let\<^sub>1(3) by auto
  also have "Aexp e\<cdot>a f|` domA \<Delta> \<sqsubseteq> ?ae" by (rule Aheap_above_arg)
  finally have "Aexp e\<cdot>a \<sqsubseteq> ?ae \<squnion> ae" by this auto
  }
  ultimately
  have "consistent (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S) "
    by (auto  simp add: stack)
  }
  moreover
  {
    have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))"
      using fresh_distinct[OF let\<^sub>1(1)]
      by (auto dest!: set_mp[OF edom_Aheap])
    hence "map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) (map_transform Atransform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) \<Gamma>)
       = map_transform Aeta_expand ae (map_transform Atransform ae \<Gamma>)"
      by (auto intro!: map_transform_cong simp add: edomIff)
    moreover
    from let\<^sub>1 have *: "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
    have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
       using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
       by (auto dest!: set_mp[OF *] set_mp[OF ups_fv_subset])
    hence "map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) (map_transform Atransform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) \<Delta>)
       = map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))) (map_transform Atransform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))) \<Delta>)"
      by (auto intro!: map_transform_cong simp add: edomIff)
    ultimately
    have "conf_transform (ae, a) (\<Gamma>, Terms.Let \<Delta> e, S) \<Rightarrow> conf_transform (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S)"
      apply (simp add: map_transform_append)
      apply rule
      using let\<^sub>1(1,2)
      by auto
  }
  ultimately
  show ?case  by (blast del: consistentI consistentE)
next
  case refl thus ?case by auto
next
  case trans
    from trans(5)
    show ?case
      apply (auto dest!: trans(3,4))
      apply (metis (poly_guards_query) rtranclp_trans)
      done
qed

(*
  sublocale AbstractTransform step consistent conf_transform
    apply default
    using foo
    apply (auto del: consistentI consistentE)
    done
*)

end
end

