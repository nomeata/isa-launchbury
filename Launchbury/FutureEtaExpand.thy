theory FutureEtaExpand
imports CallFutures AEnv Terms EtaExpansionArity EtaExpansionSestoft AbstractTransform Set_Cpo_Nominal  Sestoft SestoftGC
begin

default_sort type

type_synonym oneShot = "one"
abbreviation notOneShot :: oneShot where "notOneShot \<equiv> ONE"
abbreviation oneShot :: oneShot where "oneShot \<equiv> \<bottom>"

type_synonym two = "oneShot\<^sub>\<bottom>"
abbreviation many :: two where "many \<equiv> up\<cdot>notOneShot"
abbreviation once :: two where "once \<equiv> up\<cdot>oneShot"
abbreviation none :: two where "none \<equiv> \<bottom>"

definition two_pred where "two_pred = (\<Lambda> x. if x = once then \<bottom> else x)"

definition record_call where "record_call x = (\<Lambda> ce. (\<lambda> y. if x = y then two_pred\<cdot>(ce y) else ce x))"

lemma two_conj: "c = many \<or> c = once \<or> c = none" sorry

lemma two_cases[case_names many once none]:
  obtains "c = many" | "c = once" | "c = none" using two_conj by metis


definition abstractPath :: "var list set \<Rightarrow> var \<Rightarrow> two"
  where "abstractPath ps v = undefined"

text {* Expands only if it is safe to do so, i.e. either one-shot or already a function. *}

fun rhsExpand :: "(Arity \<times> one) \<Rightarrow> exp \<Rightarrow> exp"
  where "rhsExpand (a,c) e = (if isLam e \<or> c = \<bottom> then Aeta_expand a e else e)"

interpretation supp_bounded_transform rhsExpand sorry

lemma rhsExpand[eqvt]: "\<pi> \<bullet> rhsExpand = rhsExpand" sorry


fun Astack :: "stack \<Rightarrow> Arity"
  where "Astack [] = 0"
      | "Astack (Arg x # S) = inc\<cdot>(Astack S)"
      | "Astack (Upd x # S) = 0"
      | "Astack (Dummy x # S) = 0"


lemma Aeta_expand_correct:
  assumes "Astack S \<sqsubseteq> a"
  shows "(\<Gamma>, Aeta_expand a e, S) \<Rightarrow>\<^sup>* (\<Gamma>, e, S)"
proof-
  have "arg_prefix S = Rep_Arity (Astack S)"
    by (induction S arbitrary: a rule: arg_prefix.induct) (auto simp add: Arity.zero_Arity.rep_eq[symmetric])
  also
  from assms(1)
  have "Rep_Arity a \<le> Rep_Arity (Astack S)" by (metis below_Arity.rep_eq)
  finally
  show ?thesis by transfer (rule eta_expansion_correct')
qed


fun restr_stack :: "var set \<Rightarrow> stack \<Rightarrow> stack"
  where "restr_stack V [] = []"
      | "restr_stack V (Arg x # S) = Arg x # restr_stack V S"
      | "restr_stack V (Upd x # S) = (if x \<in> V then Upd x # restr_stack V S else restr_stack V S)"
      | "restr_stack V (Dummy x # S) = Dummy x # restr_stack V S"

lemma Astack_restr_stack_below:
  "Astack (restr_stack V S) \<sqsubseteq> Astack S"
  by (induction V S rule: restr_stack.induct) auto



definition fup_fst :: "(var \<Rightarrow> (Arity \<times> one)\<^sub>\<bottom>) \<Rightarrow> AEnv"
    where "fup_fst e x = fup\<cdot>(\<Lambda> p. up\<cdot>(cfst\<cdot>p))\<cdot>(e x)"

lemma fup_fst_eqvt[eqvt]: "\<pi> \<bullet> (fup_fst e x) = fup_fst (\<pi> \<bullet> e) (\<pi> \<bullet> x)"
  unfolding fup_fst_def
  by perm_simp rule

locale FutureAnalysis =
  fixes aExp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
  fixes fExp :: "exp \<Rightarrow> Arity \<rightarrow> future set"
  fixes fHeap :: "heap \<Rightarrow> (AEnv \<times> future set) \<rightarrow> (var \<Rightarrow> (Arity \<times> one)\<^sub>\<bottom>)"

  assumes aExp_Var: "up \<cdot> n \<sqsubseteq> (aExp (Var x)\<cdot>n) x"
  assumes aExp_App: "aExp (App e x) \<cdot> n = aExp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes aExp_subst_App_Lam: "aExp (e[y::=x]) \<sqsubseteq> aExp (App (Lam [y]. e) x)"
  assumes aExp_Lam: "aExp (Lam [y]. e) \<cdot> n = env_delete y (aExp e \<cdot>(pred\<cdot>n))"


  assumes fExp_App: "fExp (App e x)\<cdot>n = may_call x (fExp e \<cdot>(inc\<cdot>n))"

  assumes aExp[eqvt]: "\<pi> \<bullet> aExp = aExp"
  assumes fExp[eqvt]: "\<pi> \<bullet> fExp = fExp"
  assumes fHeap[eqvt]: "\<pi> \<bullet> fHeap = fHeap"
begin

  sublocale AbstractTransformBound
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, fHeap \<Delta>\<cdot>(aExp e\<cdot>a, fExp e\<cdot>a))"
    "fst"
    "\<lambda> b . fup_fst (snd b)"
    "rhsExpand"
    "snd"
  apply default
  apply (((rule eq_reflection)?, perm_simp, rule)+)[7]
  done

  sublocale AbstractTransformBoundSubst
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, fHeap \<Delta>\<cdot>(aExp e\<cdot>a, fExp e\<cdot>a))"
    "fst"
    "\<lambda> b . fup_fst (snd b)"
    "rhsExpand"
    "snd"
  apply default
  apply (simp add: Aheap_subst  Aheap_cong[OF Aexp_subst_restr])[1]
  apply (rule subst_Aeta_expand)  
  sorry

  abbreviation ccTransform where "ccTransform \<equiv> transform"

  type_synonym tstate = "(AEnv \<times> (var \<Rightarrow> two) \<times> Arity)"

  fixrec u_com :: "'a::cpo\<^sub>\<bottom> \<rightarrow> 'b::cpo\<^sub>\<bottom> \<rightarrow> ('a \<times> 'b)\<^sub>\<bottom>"
    where "u_com\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>y) = up\<cdot>(x, y)"
  lemma u_com_strict[simp]: "u_com\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>" by fixrec_simp

  definition env_u_com ::  "('c::type \<Rightarrow> 'a::cpo\<^sub>\<bottom>) \<Rightarrow> ('c \<Rightarrow> 'b::cpo\<^sub>\<bottom>) \<Rightarrow> ('c \<Rightarrow> ('a \<times> 'b)\<^sub>\<bottom>)"
    where [simp]: "env_u_com e1 e2 x = u_com\<cdot>(e1 x)\<cdot>(e2 x)"
  lemma env_u_com_delete: "env_u_com (env_delete x e1) (env_delete x e2) = env_delete x (env_u_com e1 e2)"
    by (rule, case_tac "xa = x") auto
  

  fun conf_transform :: "tstate \<Rightarrow> conf \<Rightarrow> conf"
  where "conf_transform (ae, ce,  a) (\<Gamma>, e, S) =
    (restrictA (edom ae) (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>)), 
     ccTransform a e,
     restr_stack (edom ae) S)"

  definition anal_env :: "(exp \<Rightarrow> 'a::cpo \<rightarrow> 'b::pcpo) \<Rightarrow> heap \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<rightarrow> (var \<Rightarrow> 'b)"
    where "anal_env f \<Gamma> = (\<Lambda> e. (\<lambda> x . fup\<cdot>(f (the (map_of \<Gamma> x)))\<cdot>(e x)))"

  fun fstack :: "stack \<Rightarrow> future set \<rightarrow> future set"
    where "fstack [] = (\<Lambda> f. f)"
        | "fstack (Arg x # S) = (\<Lambda> f . fstack S \<cdot> (may_call x f))"
        | "fstack (Upd x # S) = fstack S"
        | "fstack (Dummy x # S) = fstack S"


  definition const_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
    where "const_on f S x = (\<forall> y \<in> S . f y = x)"

  lemma const_on_simp:
   "const_on f S r \<Longrightarrow> x \<in> S \<Longrightarrow> f x = r"
   by (simp add: const_on_def)

  lemma const_onE[elim]: "const_on f S r ==> x : S ==> r = r' ==> f x = r'"     by (simp add: const_on_def)

  lemma const_on_insert[simp]: "const_on f (insert x S) y \<longleftrightarrow> const_on f S y \<and> f x = y"
    unfolding const_on_def by auto

  lemma thunks_delete[simp]: "thunks (delete x \<Gamma>) = thunks \<Gamma> - {x}" sorry

  fun prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> (var \<Rightarrow> two)"
    where "prognosis ae a (\<Gamma>, e, S) = abstractPath (paths (anal_env fExp \<Gamma> \<cdot> ae) (fstack S \<cdot>(fExp e \<cdot> a)))"
  lemmas prognosis.simps[simp del]

  inductive consistent :: "tstate \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ae \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> edom ce = edom ae
    \<Longrightarrow> Astack (restr_stack (edom ae) S) \<sqsubseteq> a
    \<Longrightarrow> aExp e \<cdot> a \<sqsubseteq> ae
    \<Longrightarrow> prognosis ae a  (\<Gamma>, e, S) \<sqsubseteq> ce
    \<Longrightarrow> (\<And> x. x \<in> thunks \<Gamma> \<Longrightarrow>  many \<sqsubseteq> ce x \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> (\<And> x e'. map_of \<Gamma> x = Some e' \<Longrightarrow> x \<in> edom (prognosis ae a  (\<Gamma>, e, S)) \<Longrightarrow> fup\<cdot>(aExp e')\<cdot>(ae x) \<sqsubseteq> ae)
    \<Longrightarrow> const_on ae (ap S) (up\<cdot>0)
    \<Longrightarrow> const_on ae (upds (restr_stack (edom ae) S)) (up\<cdot>0)
    \<Longrightarrow> consistent (ae, ce, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, ce, a) (\<Gamma>, e, S)"
  
  lemma isLam_transform[simp]:
    "isLam (transform a e) \<longleftrightarrow> isLam e"
    by (induction e rule:isLam.induct) (case_tac b, auto)

  lemma foo:
    fixes c c' R 
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,ce,a) c"
    shows "\<exists>ae' ce' a'. consistent (ae',ce',a') c' \<and> conf_transform (ae,ce,a) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae',ce',a') c'"
  using assms
  proof(induction c c' arbitrary: ae ce a rule:step_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    have " prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) = prognosis ae a (\<Gamma>, App e x, S)" sorry
    with app\<^sub>1 have "consistent (ae, ce, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by (auto simp add: join_below_iff fExp_App aExp_App)
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, App e x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by simp rule
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
case (app\<^sub>2 \<Gamma> y e x S)
  have "aExp (e[y ::= x])\<cdot>(pred\<cdot>a) \<sqsubseteq> ae" using app\<^sub>2
    apply (auto simp add:  join_below_iff)
    apply (rule below_trans[OF monofun_cfun_fun[OF aExp_subst_App_Lam]])
    apply (auto simp add: aExp_App aExp_Lam join_below_iff)
    done
  moreover
  have "fExp e[y::=x]\<cdot>(pred\<cdot>a) \<sqsubseteq> may_call x (fExp (Lam [y]. e)\<cdot>a)" sorry
  hence "fstack S\<cdot>(fExp e[y::=x]\<cdot>(pred\<cdot>a)) \<sqsubseteq> fstack S\<cdot>(may_call x (fExp (Lam [y]. e)\<cdot>a))" by (rule monofun_cfun_arg)
  hence "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, (Lam [y]. e), Arg x # S)"
    sorry
  moreover
  hence "edom (prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S)) \<subseteq> edom (prognosis ae a (\<Gamma>, (Lam [y]. e), Arg x # S))" 
    by (rule edom_mono)
  ultimately
  have "consistent (ae, ce, pred\<cdot>a) (\<Gamma>, e[y::=x], S)"  using app\<^sub>2
    by (auto elim: below_trans)
  moreover
  have "conf_transform (ae, ce, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
  ultimately
  show ?case by (blast  del: consistentI consistentE)
next
case (thunk \<Gamma> x e S)
  hence "x \<in> thunks \<Gamma>" sorry

  from thunk have "aExp (Var x)\<cdot>a \<sqsubseteq> ae" by auto
  from below_trans[OF aExp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".    
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
  hence [simp]: "x \<in> edom ae" by (simp add: edom_def)

  have "Astack (restr_stack (edom ae) S) \<sqsubseteq> u" using thunk `a \<sqsubseteq> u` by (auto elim: below_trans)

  have "x \<in> edom (prognosis ae a (\<Gamma>, Var x, S))" sorry
  hence "fup\<cdot>(aExp e)\<cdot>(ae x) \<sqsubseteq> ae " using  thunk by blast
  hence "aExp e\<cdot>u \<sqsubseteq> ae" using  `ae x = up\<cdot>u` by auto


  show ?case
  proof(cases "ce x" rule:two_cases)
    case none
    hence "ae x = \<bottom>" using thunk by (auto simp add: edom_def)
    with `x \<in> edom ae` have False by (auto simp add: edom_def)
    thus ?thesis..
  next
    case once

    note `ae x = up\<cdot>u` `a \<sqsubseteq> u`
    moreover

    have "prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce" using thunk by auto
    hence "prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once"
      using once by (metis (mono_tags) fun_belowD)
    hence "x \<notin> ap S" sorry
    moreover

    have *: "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)"
      sorry

    from `prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once`
    have **:  "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) x = \<bottom>" sorry

    have [simp]: "restr_stack (edom ae - {x}) S = restr_stack (edom ae) S" sorry
    have "x \<notin> upds (restr_stack (edom ae) S)" sorry
  
    have "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> env_delete x ce"
      using ** below_trans[OF * `prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce`]
      by (rule below_env_deleteI)
    moreover

    from **
    have "(aExp e\<cdot>u) x = \<bottom>" sorry
    hence "aExp e\<cdot>u \<sqsubseteq> env_delete x ae" using `aExp e\<cdot>u \<sqsubseteq> ae` by (metis below_env_deleteI)
    moreover

    {
    fix x' e'
    assume "map_of \<Gamma> x' = Some e'" and "x' \<noteq> x"
    moreover
    assume "x' \<in> edom (prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S))"
    hence "x' \<in> edom (prognosis ae a (\<Gamma>, Var x, S))" using edom_mono[OF *]..
    ultimately
    have "fup\<cdot>(aExp e')\<cdot>(ae x') \<sqsubseteq> ae" using thunk by auto
    moreover
    have "(fup\<cdot>(aExp e')\<cdot>(ae x')) x = \<bottom>" sorry
    ultimately
    have "fup\<cdot>(aExp e')\<cdot>(ae x') \<sqsubseteq> env_delete x ae" sorry
    }
    moreover

    have "const_on ae (ap S) (up\<cdot>0)" using thunk by auto
    hence "const_on (env_delete x ae) (ap S) (up\<cdot>0)" using `x \<notin>  ap S`
      by (auto simp add: const_on_def env_delete_def)
    moreover

    have "const_on ae  (upds (restr_stack (edom ae) S)) (up\<cdot>0)" using thunk by auto
    hence "const_on (env_delete x ae) (upds (restr_stack (edom ae) S)) (up\<cdot>0)" using `x \<notin> upds _`
      by (auto simp add: const_on_def env_delete_def)
    ultimately
    have "consistent (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)" using thunk `a \<sqsubseteq> u`
      by (auto simp add: join_below_iff insert_absorb elim:below_trans)
      
     
    moreover
    
    {
    from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` once
    have "map_of (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>)) x = Some (Aeta_expand u (transform u e))"
      by (simp add: map_of_map_transform)
    hence "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G
           (restrictA (edom ae) (delete x (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), Upd x # restr_stack (edom ae) S)"
        by (auto simp add: env_u_com_delete  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist simp del: restr_delete)
    also
    have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ae) (delete x (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), restr_stack (edom ae) S)"
      by (rule r_into_rtranclp, rule)
    also
    have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ae)  (delete x (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>))), ccTransform u e, restr_stack (edom ae) S)"
      by (intro normal_trans Aeta_expand_correct `Astack (restr_stack (edom ae) S) \<sqsubseteq> u`)
    also(rtranclp_trans)
    have "\<dots> = conf_transform (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)" 
      by (auto simp add: env_u_com_delete  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist)
    finally(back_subst)
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)".
    }
    ultimately
    show ?thesis by (blast del: consistentI consistentE)

  next
    case many
    have *: "prognosis ae 0 (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" sorry

    have "ae x = up\<cdot>0" using thunk many `x \<in> thunks \<Gamma>` by (auto)
    hence "u = 0" using `ae x = up\<cdot>u` by simp
    
    have "prognosis ae 0 (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> ce" using * thunk by (auto elim: below_trans)
    hence "consistent (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)" using thunk  `aExp e\<cdot>u \<sqsubseteq> ae` `ae x = up\<cdot>u` `u = 0` edom_mono[OF *]
      by (auto simp add: join_below_iff)
    moreover
    from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>0` many
    have "map_of (map_transform rhsExpand (env_u_com ae ce) (map_transform ccTransform ae \<Gamma>)) x = Some (transform 0 e)"
      by (simp add: map_of_map_transform)
    with `\<not> isLam e`
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)"
      by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
    ultimately
    show ?thesis by (blast del: consistentI consistentE)
  qed
next
case (lamvar \<Gamma> x e S)
  from lamvar have "aExp (Var x)\<cdot>a \<sqsubseteq> ae" by auto
  from below_trans[OF aExp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
  
  from `ae x = up\<cdot>u` have "ce x \<noteq> \<bottom>" using lamvar by (auto simp add: edom_def)
  then obtain c where "ce x = up\<cdot>c" by (cases "ce x") auto

  have "Astack (restr_stack (edom ae) S) \<sqsubseteq> u" using lamvar  below_trans[OF _ `a \<sqsubseteq> u`] by auto

  have *: "prognosis ae u ((x, e) # delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" sorry

  have "x \<in> edom (prognosis ae a (\<Gamma>, Var x, S))" sorry
  hence "fup\<cdot>(aExp e)\<cdot>(ae x) \<sqsubseteq> ae" using lamvar by auto
  hence "aExp e\<cdot>u \<sqsubseteq> ae" using `ae x = up\<cdot>u` by simp
  hence "consistent (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)"
    using lamvar `ae x = up\<cdot>u` edom_mono[OF *]
    by (fastforce  simp add: join_below_iff split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`] below_trans[OF *])
  moreover
  {
  from `isLam e`
  have "isLam (transform u e)" by simp
  hence "isLam (Aeta_expand u (transform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isLam (transform u e)`
  have "map_of (restrictA (edom ae) (map_transform rhsExpand (env_u_com ae ce) (map_transform transform ae \<Gamma>))) x = Some (Aeta_expand u (transform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
        ((x, Aeta_expand u (transform u e)) # delete x (restrictA (edom ae) (map_transform rhsExpand (env_u_com ae ce) (map_transform transform ae \<Gamma>))), Aeta_expand u  (transform u e), restr_stack (edom ae) S)"
     by (auto intro: lambda_var simp add: map_transform_delete simp del: restr_delete)
  also have "\<dots> = (restrictA (edom ae) ((map_transform rhsExpand (env_u_com ae ce) (map_transform transform ae ((x,e) # delete x \<Gamma>)))), Aeta_expand u  (transform u e), restr_stack (edom ae) S)"
    using `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isLam (transform u e)`
    by (simp add: map_transform_Cons map_transform_delete restr_delete_twist del: restr_delete)
  also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* conf_transform (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)"
    by simp (rule Aeta_expand_correct[OF `Astack (restr_stack (edom ae) S) \<sqsubseteq> u`])
  finally(rtranclp_trans)
  have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* conf_transform (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)".
  }
  ultimately show ?case by (blast intro: normal_trans del: consistentI consistentE)
next
case (var\<^sub>2 \<Gamma> x e S)
  show ?case
  proof(cases  "x \<in> edom ae")
    case True[simp]
    hence "ae x = up\<cdot>0" using var\<^sub>2 by auto

    hence "ce x \<noteq> \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)
    then obtain c where "ce x = up\<cdot>c" by (cases "ce x") auto

    have *: "prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)" sorry

    have "Astack (Upd x # S) \<sqsubseteq> a" using var\<^sub>2 by auto
    hence "a = 0" by auto

    have "consistent (ae, ce, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2  edom_mono[OF *]
      by (auto simp add: join_below_iff split:if_splits elim:below_trans[OF *])
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) ((x, e) # \<Gamma>, e, S)"
      using `ae x = up\<cdot>0` `a = 0` var\<^sub>2 `ce x = up\<cdot>c`
      by (auto intro!: step.intros simp add: map_transform_Cons)
    ultimately show ?thesis by (blast del: consistentI consistentE)
  next
    case False[simp]
    hence [simp]: "ae x = \<bottom>" "ce x = \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)

    have *: "prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq>  prognosis ae a (\<Gamma>, e, Upd x # S)" sorry

    have "consistent (ae, ce, a) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2  edom_mono[OF *]
      by (auto simp add: join_below_iff split:if_splits elim:below_trans[OF *])
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, e, Upd x # S) = conf_transform (ae, ce, a) ((x, e) # \<Gamma>, e, S)"
      by(simp add: map_transform_restrA[symmetric])
    ultimately show ?thesis by (auto del: consistentI consistentE)
  qed
next

    

next






end
