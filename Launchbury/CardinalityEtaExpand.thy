theory CardinalityEtaExpand
imports CardinalityAnalysis AbstractTransform Sestoft SestoftGC ArityEtaExpansionSestoft
begin

locale CardinalityArityTransformation = CardinalityPrognosisEdom + CardinalityPrognosisCorrectLet 
begin

  sublocale AbstractTransformBound
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
    "fst"
    "snd"
    "Aeta_expand"
    "snd"
  apply default
  apply (((rule eq_reflection)?, perm_simp, rule)+)[7]
  done

  sublocale AbstractTransformBoundSubst
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
    "fst"
    "snd"
    "Aeta_expand"
    "snd"
  apply default
  apply (simp add: Aheap_subst)
  apply (rule subst_Aeta_expand)
  done

  abbreviation ccTransform where "ccTransform \<equiv> transform"

  lemma supp_transform: "supp (transform a e) \<subseteq> supp e"
    by (induction rule: transform.induct)
       (auto simp add: exp_assn.supp Let_supp dest!: set_mp[OF supp_map_transform] set_mp[OF supp_map_transform_step] )
  interpretation supp_bounded_transform transform
    by default (auto simp add: fresh_def supp_transform) 

  type_synonym tstate = "(AEnv \<times> (var \<Rightarrow> two) \<times> Arity)"

  fun conf_transform :: "tstate \<Rightarrow> conf \<Rightarrow> conf"
  where "conf_transform (ae, ce,  a) (\<Gamma>, e, S) =
    (restrictA (edom ae) (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)), 
     ccTransform a e,
     restr_stack (edom ae) S)"

  definition anal_env :: "(exp \<Rightarrow> 'a::cpo \<rightarrow> 'b::pcpo) \<Rightarrow> heap \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<rightarrow> (var \<Rightarrow> 'b)"
    where "anal_env f \<Gamma> = (\<Lambda> e. (\<lambda> x . fup\<cdot>(f (the (map_of \<Gamma> x)))\<cdot>(e x)))"

  inductive consistent :: "tstate \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ae \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> heap_upds_ok (\<Gamma>, S)
    \<Longrightarrow> edom ce = edom ae
    \<Longrightarrow> Astack (restr_stack (edom ae) S) \<sqsubseteq> a
    \<Longrightarrow> prognosis ae a (\<Gamma>, e, S) \<sqsubseteq> ce
    \<Longrightarrow> ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a \<sqsubseteq> ae
    \<Longrightarrow> (\<And> x. x \<in> thunks \<Gamma> \<Longrightarrow>  many \<sqsubseteq> ce x \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> const_on ae (ap S) (up\<cdot>0)
    \<Longrightarrow> const_on ae (upds (restr_stack (edom ae) S)) (up\<cdot>0)
    \<Longrightarrow> consistent (ae, ce, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, ce, a) (\<Gamma>, e, S)"
  
  lemma foo:
    fixes c c' R 
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,ce,a) c"
    shows "\<exists>ae' ce' a'. consistent (ae',ce',a') c' \<and> conf_transform (ae,ce,a) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae',ce',a') c'"
  using assms
  proof(induction c c' arbitrary: ae ce a rule:step_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    have "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)" by (rule prognosis_App)
    with app\<^sub>1 have "consistent (ae, ce, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by (auto simp add: join_below_iff  dest!: below_trans[OF Aexp_App] elim: below_trans)
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, App e x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by simp rule
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
case (app\<^sub>2 \<Gamma> y e x S)
  have "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, (Lam [y]. e), Arg x # S)"
     by (rule prognosis_subst_Lam)
  moreover
  {
  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) \<sqsubseteq> env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<squnion> AE_singleton x\<cdot>(up\<cdot>0)" by (rule Aexp_subst)
  also have "env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<sqsubseteq> Aexp (Lam [y]. e)\<cdot>a" by (rule Aexp_Lam)
  also have "\<dots> \<sqsubseteq> ae" using app\<^sub>2 by (auto simp add: join_below_iff)
  also have "AE_singleton x\<cdot>(up\<cdot>0) \<sqsubseteq> ae" using app\<^sub>2 by auto
  also have "ae \<squnion> ae = ae" by simp
  finally  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) \<sqsubseteq> ae" by this simp_all
  }
  ultimately
  have "consistent (ae, ce, pred\<cdot>a) (\<Gamma>, e[y::=x], S)" using app\<^sub>2
    by (auto elim: below_trans edom_mono  simp add: join_below_iff)
  moreover
  have "conf_transform (ae, ce, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
  ultimately
  show ?case by (blast  del: consistentI consistentE)
next
case (thunk \<Gamma> x e S)
  hence "x \<in> thunks \<Gamma>" by auto
  hence [simp]: "x \<in> domA \<Gamma>" by (rule set_mp[OF thunks_domA])
  hence "x \<notin> upds S" using thunk by (auto elim!: heap_upds_okE)

  from thunk have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by (auto simp add: join_below_iff)
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".    
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
  hence [simp]: "x \<in> edom ae" by (simp add: edom_def)

  have "Astack (restr_stack (edom ae) S) \<sqsubseteq> u" using thunk `a \<sqsubseteq> u` by (auto elim: below_trans)

  from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
  also have "\<dots> \<sqsubseteq> ae" using thunk by (auto simp add: join_below_iff)
  finally have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae".

  show ?case
  proof(cases "ce x" rule:two_cases)
    case none
    hence "ae x = \<bottom>" using thunk by (auto simp add: edom_def)
    with `x \<in> edom ae` have False by (auto simp add: edom_def)
    thus ?thesis..
  next
    case once

    note `ae x = up\<cdot>u` 
    moreover

    have "prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce" using thunk by auto
    hence "prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once"
      using once by (metis (mono_tags) fun_belowD)
    hence "x \<notin> ap S" using prognosis_ap[of ae a \<Gamma> "(Var x)" S] by auto
    

    {
    have "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)" by (rule prognosis_delete)
    also
    from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u`
    have "\<dots> \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
      by (rule prognosis_Var)
    finally have "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))" by this simp
    }
    note * = this

    from `prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once`
    have "(record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))) x = none"
      by (simp add: two_pred_none)
    hence **: "prognosis ae u (delete x \<Gamma>, e, Upd x # S) x = none" using fun_belowD[OF *, where x = x] by auto

    have eq: "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) = prognosis ae u (delete x \<Gamma>, e, Upd x # S)"
      by (rule prognosis_env_cong) simp

    have [simp]: "restr_stack (edom ae - {x}) S = restr_stack (edom ae) S" 
      using `x \<notin> upds S` by (auto intro: restr_stack_cong)
  
    have "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> env_delete x ce"
      unfolding eq
      using ** below_trans[OF below_trans[OF * Cfun.monofun_cfun_arg[OF `prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce`]] record_call_below_arg]
      by (rule below_env_deleteI)
    moreover

    {
    have "ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) = ABinds (delete x \<Gamma>)\<cdot>ae" by (rule Abinds_env_cong) simp
    with `ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae`
    have "ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae" by simp
    moreover
    from **[folded eq] set_mp[OF artiy_edom_prognosis, unfolded edomIff]
    have "(ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u) x = \<bottom>" by metis
    ultimately
    have "ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u \<sqsubseteq> env_delete x ae" by (metis below_env_deleteI)
    }
    moreover


    have "const_on ae (ap S) (up\<cdot>0)" using thunk by auto
    hence "const_on (env_delete x ae) (ap S) (up\<cdot>0)" using `x \<notin>  ap S`
      by (fastforce simp add:  env_delete_def)
    moreover

    have "const_on ae  (upds (restr_stack (edom ae) S)) (up\<cdot>0)" using thunk by auto
    hence "const_on (env_delete x ae) (upds (restr_stack (edom ae) S)) (up\<cdot>0)" using `x \<notin> upds _`
      by (fastforce simp add: env_delete_def)
    ultimately
    have "consistent (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)" using thunk `a \<sqsubseteq> u`
      by (auto simp add: join_below_iff insert_absorb elim:below_trans)
     
    moreover
    
    {
    from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` once
    have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)) x = Some (Aeta_expand u (transform u e))"
      by (simp add: map_of_map_transform)
    hence "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G
           (restrictA (edom ae) (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), Upd x # restr_stack (edom ae) S)"
        by (auto simp add:  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist simp del: restr_delete)
    also
    have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ae) (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), restr_stack (edom ae) S)"
      by (rule r_into_rtranclp, rule)
    also
    have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ae)  (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), ccTransform u e, restr_stack (edom ae) S)"
      by (intro normal_trans Aeta_expand_correct `Astack (restr_stack (edom ae) S) \<sqsubseteq> u`)
    also(rtranclp_trans)
    have "\<dots> = conf_transform (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)" 
      by (auto simp add:  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist)
    finally(back_subst)
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)".
    }
    ultimately
    show ?thesis by (blast del: consistentI consistentE)

  next
    case many

    have "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)" by (rule prognosis_delete)
    also
    from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u`
    have "\<dots> \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))" by (rule prognosis_Var)
    also note record_call_below_arg
    finally
    have *: "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by this simp_all

    have "ae x = up\<cdot>0" using thunk many `x \<in> thunks \<Gamma>` by (auto)
    hence "u = 0" using `ae x = up\<cdot>u` by simp

    
    have "prognosis ae 0 (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> ce" using *[unfolded `u=0`] thunk by (auto elim: below_trans)
    moreover
    note `ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae`
    ultimately
    have "consistent (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)" using thunk `ae x = up\<cdot>u` `u = 0`  by auto
    moreover

    from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>0` many
    have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)) x = Some (transform 0 e)"
      by (simp add: map_of_map_transform)
    with `\<not> isLam e`
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)"
      by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
    ultimately
    show ?thesis by (blast del: consistentI consistentE)
  qed
next
case (lamvar \<Gamma> x e S)
  from lamvar have [simp]: "x \<in> domA \<Gamma>" by auto (metis domI dom_map_of_conv_domA)
  from lamvar have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by (auto simp add: join_below_iff)
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto

  from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
  also have "\<dots> \<sqsubseteq> ae" using lamvar by (auto simp add: join_below_iff)
  finally have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae".

  from `ae x = up\<cdot>u` have "ce x \<noteq> \<bottom>" using lamvar by (auto simp add: edom_def)
  then obtain c where "ce x = up\<cdot>c" by (cases "ce x") auto

  have "prognosis ae u ((x, e) # delete x \<Gamma>, e, S) = prognosis ae u (\<Gamma>, e, S)"
    using `map_of \<Gamma> x = Some e` by (auto intro!: prognosis_reorder)
  also have "\<dots> \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)" by (rule prognosis_upd)
  also have "\<dots> \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
     using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u`  by (rule prognosis_Var)
  also have "\<dots> \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by (rule record_call_below_arg)
  finally have *: "prognosis ae u ((x, e) # delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by this simp_all

  have "consistent (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)"
    using lamvar `ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae`  `ae x = up\<cdot>u` edom_mono[OF *]
    by (auto simp add: join_below_iff split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`] below_trans[OF *])
  moreover

  have "Astack (restr_stack (edom ae) S) \<sqsubseteq> u" using lamvar  below_trans[OF _ `a \<sqsubseteq> u`] by auto

  {
  from `isLam e`
  have "isLam (transform u e)" by simp
  hence "isLam (Aeta_expand u (transform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isLam (transform u e)`
  have "map_of (restrictA (edom ae) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))) x = Some (Aeta_expand u (transform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
        ((x, Aeta_expand u (transform u e)) # delete x (restrictA (edom ae) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))), Aeta_expand u  (transform u e), restr_stack (edom ae) S)"
     by (auto intro: lambda_var simp add: map_transform_delete simp del: restr_delete)
  also have "\<dots> = (restrictA (edom ae) ((map_transform Aeta_expand ae (map_transform transform ae ((x,e) # delete x \<Gamma>)))), Aeta_expand u  (transform u e), restr_stack (edom ae) S)"
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
  proof(cases "x \<in> edom ae")
    case True[simp]
    hence "ae x = up\<cdot>a" using var\<^sub>2 by auto

    hence "ce x \<noteq> \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)
    then obtain c where "ce x = up\<cdot>c" by (cases "ce x") auto

    have "Astack (Upd x # S) \<sqsubseteq> a" using var\<^sub>2 by auto
    hence "a = 0" by auto

    from `isLam e` `x \<notin> domA \<Gamma>`
    have *: "prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)" by (rule prognosis_Var2)

    have "consistent (ae, ce, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
      by (auto simp add: join_below_iff split:if_splits elim:below_trans[OF *])
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) ((x, e) # \<Gamma>, e, S)"
      using `ae x = up\<cdot>a` `a = 0` var\<^sub>2 `ce x = up\<cdot>c`
      by (auto intro!: step.intros simp add: map_transform_Cons)
    ultimately show ?thesis by (blast del: consistentI consistentE)
  next
    case False[simp]
    hence "ae x = \<bottom>" "ce x = \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)
    
    have "prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae a ((x, e) # \<Gamma>, e, Upd x # S)" by (rule prognosis_upd)
    also
    (*
    from `ce x = \<bottom>` and var\<^sub>2
    have "prognosis ae a (\<Gamma>, e, Upd x # S) x = \<bottom>" by auto (metis below_bottom_iff fun_belowD)
    hence "prognosis ae a (delete x ((x, e) # \<Gamma>), e, Upd x # S) x = \<bottom>"  using `x \<notin> domA \<Gamma>` by simp
    from this `ae x = \<bottom>`
    *)
    from `ae x = \<bottom>`
    have "prognosis ae a ((x, e) # \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (delete x ((x,e) # \<Gamma>), e, Upd x # S)" 
      by (rule prognosis_not_called) 
    also have  "delete x ((x,e)#\<Gamma>) = \<Gamma>" using `x \<notin> domA \<Gamma>` by simp
    finally
    have *: "prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, e, Upd x # S)" by this simp

    have "consistent (ae, ce, a) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
      by (auto simp add: join_below_iff `ae x = \<bottom>` split:if_splits elim:below_trans[OF *])
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, e, Upd x # S) = conf_transform (ae, ce, a) ((x, e) # \<Gamma>, e, S)"
      by(simp add: map_transform_restrA[symmetric])
    ultimately show ?thesis by (auto del: consistentI consistentE)
  qed
next
  case (let\<^sub>1 \<Delta> \<Gamma> e S)

  let ?ae = "Aheap \<Delta> e\<cdot>a"
  let ?new = "(domA (\<Delta> @ \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S))"
  have new: "?new = domA \<Delta>"
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (auto dest: set_mp[OF ups_fv_subset])

  let ?ce = "cHeap \<Delta> e\<cdot>a"

  have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: set_mp[OF ups_fv_subset])
  hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom ?ae" by (auto dest!: set_mp[OF edom_Aheap])

  have restr_stack_simp: "restr_stack (edom (?ae \<squnion> ae)) S = restr_stack (edom ae) S"
    by (auto intro: restr_stack_cong dest!: *)

  have "edom ae \<subseteq> domA \<Gamma> \<union> upds S" using let\<^sub>1 by auto
  from set_mp[OF this] fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
  have [simp]: "ae f|` domA \<Delta> = \<bottom>"
    using  fresh_distinct[OF let\<^sub>1(1)] by (auto dest: set_mp[OF ups_fv_subset])

  from  fresh_distinct[OF let\<^sub>1(1)]
   have [simp]: "?ae f|` domA \<Gamma> = \<bottom>" by (auto dest!: set_mp[OF edom_Aheap])

  {
  have "edom (?ae \<squnion> ae) \<subseteq> domA (\<Delta> @ \<Gamma>) \<union> upds S"
    using let\<^sub>1(3) by (auto dest: set_mp[OF edom_Aheap])
  moreover
  { fix x e'
    assume "x \<in> thunks \<Gamma>"
    hence "x \<notin> edom ?ce" using fresh_distinct[OF let\<^sub>1(1)]
      by (auto simp add: edom_cHeap dest: set_mp[OF edom_Aheap]  set_mp[OF thunks_domA])
    hence [simp]: "?ce x = \<bottom>" unfolding edomIff by auto
  
    assume "many \<sqsubseteq> (?ce \<squnion> ce) x"
    with let\<^sub>1 `x \<in> thunks \<Gamma>`
    have "(?ae \<squnion> ae) x = up \<cdot>0" by auto
  }
  moreover
  { fix x e'
    assume "x \<in> thunks \<Delta>" 
    hence "x \<notin> domA \<Gamma>" and "x \<notin> upds S"
      using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
      by (auto dest!: set_mp[OF thunks_domA] set_mp[OF ups_fv_subset])
    hence "x \<notin> edom ce" using let\<^sub>1 by auto
    hence [simp]: "ce x = \<bottom>"  by (auto simp add: edomIff)

    assume "many \<sqsubseteq> (?ce \<squnion> ce) x" with `x \<in> thunks \<Delta>`
    have "(?ae \<squnion> ae) x = up\<cdot>0" by (auto simp add: Aheap_heap3)
  }
  moreover
  have "const_on ae (ap S) (up\<cdot>0)" using let\<^sub>1 by auto  
  hence "const_on (?ae \<squnion> ae) (ap S) (up\<cdot>0)" by fastforce
  moreover
  have "const_on ae (upds (restr_stack (edom ae) S)) (up\<cdot>0)" using let\<^sub>1 by auto
  hence "const_on (?ae \<squnion> ae) (upds (restr_stack (edom ae) S)) (up\<cdot>0)"  by fastforce
  hence "const_on (?ae \<squnion> ae) (upds (restr_stack (edom (?ae \<squnion> ae)) S)) (up\<cdot>0)" unfolding restr_stack_simp.
  moreover
  have "Astack (restr_stack (edom (?ae \<squnion> ae)) S) \<sqsubseteq> a" unfolding restr_stack_simp using let\<^sub>1 by auto
  moreover
  have "edom (?ce \<squnion> ce) = edom (?ae \<squnion> ae)" using let\<^sub>1 by (auto simp add: edom_cHeap)
  moreover
  {
  from let\<^sub>1(1,2) `edom ae \<subseteq> domA \<Gamma> \<union> upds S`
  have "prognosis (?ae \<squnion> ae) a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> ?ce \<squnion> prognosis ae a (\<Gamma>, Let \<Delta> e, S)" by (rule prognosis_Let)
  also have "prognosis ae a (\<Gamma>, Let \<Delta> e, S) \<sqsubseteq> ce" using let\<^sub>1 by auto
  finally have "prognosis (?ae \<squnion> ae) a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> ?ce \<squnion> ce" by this simp
  }
  moreover
  have "heap_upds_ok (\<Gamma>, S)" using let\<^sub>1 by auto
  with fresh_distinct[OF let\<^sub>1(1)]  `domA \<Delta> \<inter> upds S = {}`
  have "heap_upds_ok (\<Delta> @ \<Gamma>, S)" by (rule heap_upds_ok_append)
  moreover
  {
  have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)"
    by (rule Abinds_env_restr_cong) (simp add: env_restr_join)
  moreover
  have "ABinds \<Gamma>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Gamma>\<cdot>ae"
    by (rule Abinds_env_restr_cong) (simp add: env_restr_join)
  ultimately
  have "ABinds (\<Delta> @ \<Gamma>) \<cdot> (Aheap \<Delta> e\<cdot>a \<squnion> ae) \<squnion> Aexp e\<cdot>a = (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a) \<squnion> ABinds \<Gamma>\<cdot>ae"
    apply (simp add: Abinds_append_disjoint[OF fresh_distinct[OF let\<^sub>1(1)]])
    by (metis join_comm)
  moreover have "(ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a) \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a" by (rule Aexp_Let)
  moreover have " ABinds \<Gamma>\<cdot>ae \<squnion> Aexp (Let \<Delta> e)\<cdot>a \<sqsubseteq> ae" using let\<^sub>1 by auto
  ultimately
  have "ABinds (\<Delta> @ \<Gamma>) \<cdot> (Aheap \<Delta> e\<cdot>a \<squnion> ae) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> ae"
    apply (simp only: join_assoc[symmetric])
    apply (erule below_trans[OF join_mono[OF _ below_refl]])
    apply (simp only: join_assoc)
    apply (subst join_comm) back
    apply (erule join_mono[OF  below_refl])
    done
  }
  ultimately
  have "consistent (?ae \<squnion> ae, ?ce \<squnion> ce, a) (\<Delta> @ \<Gamma>, e, S) " by auto
  }
  moreover
  {
    have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ae"
      using fresh_distinct[OF let\<^sub>1(1)]
      by (auto dest!: set_mp[OF edom_Aheap])
    hence "restrictA (edom (?ae \<squnion> ae)) (map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Gamma>))
       = restrictA (edom ae) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))"
       by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
    moreover

    from let\<^sub>1 have *: "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
    have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
       using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
       by (auto dest!: set_mp[OF *] set_mp[OF ups_fv_subset])
    hence "restrictA (edom (?ae \<squnion> ae)) (map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Delta>))
       = restrictA (edom ?ae) (map_transform Aeta_expand ?ae (map_transform transform ?ae \<Delta>))"
       by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
    ultimately

    have "conf_transform (ae, ce, a) (\<Gamma>, Let \<Delta> e, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (?ae \<squnion> ae, ?ce \<squnion> ce, a) (\<Delta> @ \<Gamma>, e, S)"
      using restr_stack_simp let\<^sub>1(1,2)
      by (fastforce intro!: let_and_restrict simp  add: map_transform_append restrictA_append restr_stack_simp   dest: set_mp[OF edom_Aheap])
  }
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
  case refl thus ?case by auto
next
  case (trans c c' c'')
    from trans(3)[OF trans(5)]
    obtain ae' ce' a' where "consistent (ae', ce', a') c'" and *: "conf_transform (ae, ce, a) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae', ce', a') c'" by blast
    from trans(4)[OF this(1)]
    obtain ae'' ce'' a'' where "consistent (ae'', ce'', a'') c''" and **: "conf_transform (ae', ce', a') c' \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae'', ce'', a'') c''" by blast
    from this(1) rtranclp_trans[OF * **]
    show ?case by blast
qed


end


end
