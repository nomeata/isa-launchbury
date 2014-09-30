theory ArityEtaExpand
imports ArityCorrectSestoft EtaExpansion TransformTools
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

  nominal_function Aeta_expand_transform where
    "Aeta_expand_transform a (App e x) = App (Aeta_expand_transform (inc\<cdot>a) e) x"
  | "Aeta_expand_transform a (Lam [x]. e) = Lam [x].(Aeta_expand_transform (pred\<cdot>a) e)"
  | "Aeta_expand_transform a (Var x) = Var x"
  | "Aeta_expand_transform a (Terms.Let \<Delta> e) = Terms.Let (map_transform Aeta_expand (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) (map_transform Aeta_expand_transform (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<Delta>)) (Aeta_expand_transform a e)"
  proof-
  case goal1
    thus ?case
    unfolding eqvt_def Aeta_expand_transform_graph_aux_def
    apply rule
    apply perm_simp
    apply (rule refl)
    done
  case (goal3 P x)
    show ?case
    proof (cases x)
      fix a b
      assume "x = (a, b)"
      thus ?case
      using goal3
      apply (cases b rule:Terms.exp_strong_exhaust)
      apply auto
      done
    qed
  next
case (goal8 a x e a' x' e')
  from goal8(5)
  have "a' = a" and  "Lam [x]. e = Lam [x']. e'" by simp_all
  from this(2)
  show ?case
  unfolding `a' = a`
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm

    assume "supp \<pi> \<sharp>* (Lam [x]. e)" 
    hence *: "supp \<pi> \<sharp>* Lam [x]. Aeta_expand_transform_sumC (pred\<cdot>a, e)"
      by (auto simp add: fresh_star_def fresh_def  exp_assn.supp supp_Pair pure_supp exp_assn.fsupp dest!:  set_mp[OF supp_eqvt_at[OF goal8(1)], rotated])

    have "Lam [(\<pi> \<bullet> x)]. Aeta_expand_transform_sumC (pred\<cdot>a, \<pi> \<bullet> e) = \<pi> \<bullet> (Lam [x]. Aeta_expand_transform_sumC (pred\<cdot>a, e))"
      by (simp add: eqvt_at_apply'[OF goal8(1)])
    also have "\<dots> = Lam [x]. Aeta_expand_transform_sumC (pred\<cdot>a, e)"
      by (rule perm_supp_eq[OF *])
    finally show "Lam [(\<pi> \<bullet> x)]. Aeta_expand_transform_sumC (pred\<cdot>a, \<pi> \<bullet> e) = Lam [x]. Aeta_expand_transform_sumC (pred\<cdot>a, e)" by simp
  qed
next
case (goal13 a as body a' as' body')
  from supp_eqvt_at[OF goal13(1)]
  have "\<And> x e a. (x, e) \<in> set as \<Longrightarrow> supp (Aeta_expand_transform_sumC (a, e)) \<subseteq> supp e"
    by (auto simp add: exp_assn.fsupp supp_Pair pure_supp)
  hence supp_map: "\<And>ae. supp (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) ae as) \<subseteq> supp as"
    by (rule supp_map_transform_step)

  from goal13(9)
  have "a' = a" and  "Terms.Let as body = Terms.Let as' body'" by simp_all
  from this(2)
  show ?case
  unfolding `a' = a`
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Terms.Let as body"
    hence *: "supp \<pi> \<sharp>* Terms.Let (map_transform Aeta_expand (Aheap as\<cdot>(Aexp body\<cdot>a)) (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap as\<cdot>(Aexp body\<cdot>a)) as)) (Aeta_expand_transform_sumC (a, body))"
      by (auto simp add: fresh_star_def fresh_def  Let_supp supp_Pair pure_supp exp_assn.fsupp
               dest!:  set_mp[OF supp_eqvt_at[OF goal13(2)], rotated] set_mp[OF supp_map_transform] set_mp[OF supp_map])

    have "Terms.Let (map_transform Aeta_expand (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (map_transform (\<lambda>x xa. (\<pi> \<bullet> Aeta_expand_transform_sumC) (x, xa)) (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (\<pi> \<bullet> as))) ((\<pi> \<bullet> Aeta_expand_transform_sumC) (a, \<pi> \<bullet> body)) = 
        \<pi> \<bullet> (Terms.Let (map_transform Aeta_expand (Aheap as\<cdot>(Aexp body\<cdot>a)) (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap as\<cdot>(Aexp body\<cdot>a)) as)) (Aeta_expand_transform_sumC (a, body)))"
       by (simp del: Let_eq_iff Pair_eqvt add:  eqvt_at_apply[OF goal13(2)])
    also have "\<dots> = (Terms.Let (map_transform Aeta_expand (Aheap as\<cdot>(Aexp body\<cdot>a)) (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap as\<cdot>(Aexp body\<cdot>a)) as)) (Aeta_expand_transform_sumC (a, body)))"
      by (rule perm_supp_eq[OF *])
    also
    have "map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (\<pi> \<bullet> as)
        = map_transform (\<lambda>x xa. (\<pi> \<bullet> Aeta_expand_transform_sumC) (x, xa)) (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (\<pi> \<bullet> as)"
        apply (rule map_transform_fundef_cong[OF _ refl refl])
        apply (subst (asm) set_eqvt[symmetric])
        apply (subst (asm) mem_permute_set)
        apply (auto simp add: permute_self  dest: eqvt_at_apply''[OF goal13(1)[where aa = "(- \<pi> \<bullet> a)" for a], where p = \<pi>, symmetric])
        done
    moreover
    have " ((\<pi> \<bullet> Aeta_expand_transform_sumC) (a, \<pi> \<bullet> body)) =  (Aeta_expand_transform_sumC) (a, \<pi> \<bullet> body)"
      using eqvt_at_apply''[OF goal13(2), where p = \<pi>]  by (simp add: permute_pure)
    ultimately
    show "Terms.Let (map_transform Aeta_expand (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap (\<pi> \<bullet> as)\<cdot>(Aexp (\<pi> \<bullet> body)\<cdot>a)) (\<pi> \<bullet> as))) (Aeta_expand_transform_sumC (a, \<pi> \<bullet> body)) =
         Terms.Let (map_transform Aeta_expand (Aheap as\<cdot>(Aexp body\<cdot>a)) (map_transform (\<lambda>x0 x1. Aeta_expand_transform_sumC (x0, x1)) (Aheap as\<cdot>(Aexp body\<cdot>a)) as)) (Aeta_expand_transform_sumC (a, body))" by metis
  qed
qed auto
nominal_termination by lexicographic_order

lemma supp_Aeta_expand_transform: "supp (Aeta_expand_transform a e) \<subseteq> supp e"
  by (induction rule: Aeta_expand_transform.induct)
     (auto simp add: exp_assn.supp Let_supp dest!: set_mp[OF supp_map_transform] set_mp[OF supp_map_transform_step] )

lemma subst_Aeta_expand_transform: "(Aeta_expand_transform a e)[x ::= y] = Aeta_expand_transform a e[x ::= y]"
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
    apply (rule arg_cong) back
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
qed auto


  fun Atransform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "Atransform (ae, a) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>), 
     Aeta_expand_transform a e,
     S)"

  inductive_set thunks :: "heap \<Rightarrow> var set" for \<Gamma> where
    "map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> x \<in> thunks \<Gamma>"

  lemma Aheap_thunks: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma>\<cdot>ae) x = up\<cdot>0"
    by (metis thunks.cases Aheap_heap3)

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


  interpretation supp_bounded_transform Aeta_expand_transform
    by default (auto simp add: fresh_def supp_Aeta_expand_transform)
  
  lemma isLam_Aeta_expand_transform[simp]:
    "isLam (Aeta_expand_transform a e) \<longleftrightarrow> isLam e"
    by (induction e rule:isLam.induct) auto

(*
  sublocale AbstractConforms step consistent.
*)

lemma foo:
  fixes c c' R 
  assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,a) c"
  shows "\<exists>ae' a'. consistent (ae',a') c' \<and> Atransform (ae,a) c \<Rightarrow>\<^sup>* Atransform (ae',a') c'"
using assms
proof(induction c c' arbitrary: ae a rule:step_induction)
case (app\<^sub>1 \<Gamma> e x S)
  from app\<^sub>1 have "consistent (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"  by (fastforce simp add: Aexp_App join_below_iff)
  moreover
  have "Atransform (ae, a) (\<Gamma>, App e x, S) \<Rightarrow> Atransform (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)" by simp rule
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
  have "Atransform (ae, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> Atransform (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_Aeta_expand_transform[symmetric]) rule
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
  have "map_of (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>)) x = Some (Aeta_expand_transform 0 e)"
    by (simp add: map_of_map_transform)
  with `\<not> isLam e`
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow> Atransform (ae, 0) (delete x \<Gamma>, e, Upd x # S)"
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
  have "isLam (Aeta_expand_transform u e)" by simp
  hence "isLam (Aeta_expand u (Aeta_expand_transform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u`
  have "map_of (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>)) x = Some (Aeta_expand u (Aeta_expand_transform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
        ((x, Aeta_expand u (Aeta_expand_transform u e)) # (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae (delete x \<Gamma>))), Aeta_expand u  (Aeta_expand_transform u e), S)"
     by (auto intro: lambda_var simp add: map_transform_delete)
  also have "\<dots> = ((map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae ((x,e) # delete x \<Gamma>))), Aeta_expand u  (Aeta_expand_transform u e), S)"
    using `ae x = up \<cdot> u` by (simp add: map_transform_Cons)
  also have "\<dots> \<Rightarrow>\<^sup>* Atransform (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    apply simp
    by (rule Aeta_expand_correct[OF `ae \` upds S \<subseteq> {up \<cdot> 0}` below_trans[OF `Astack ae S \<sqsubseteq> a` `a \<sqsubseteq> u`]])
  finally
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* Atransform (ae, u) ((x, e) # delete x \<Gamma>, e, S)".
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
  have "Atransform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> Atransform (ae, 0) ((x, e) # \<Gamma>, e, S)"
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
    hence "map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) (map_transform Aeta_expand_transform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) \<Gamma>)
       = map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>)"
      by (auto intro!: map_transform_cong simp add: edomIff)
    moreover
    from let\<^sub>1 have *: "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
    have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
       using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
       by (auto dest!: set_mp[OF *] set_mp[OF ups_fv_subset])
    hence "map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) (map_transform Aeta_expand_transform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<squnion> ae) \<Delta>)
       = map_transform Aeta_expand ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))) (map_transform Aeta_expand_transform ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))) \<Delta>)"
      by (auto intro!: map_transform_cong simp add: edomIff)
    ultimately
    have "Atransform (ae, a) (\<Gamma>, Terms.Let \<Delta> e, S) \<Rightarrow> Atransform (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S)"
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
  sublocale AbstractTransform step consistent Atransform
    apply default
    using foo
    apply (auto del: consistentI consistentE)
    done
*)

end
end

