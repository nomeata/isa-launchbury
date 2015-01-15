theory CardinalityEtaExpandCorrect
imports ArityEtaExpand CardinalityAnalysisSpec AbstractTransform Sestoft SestoftGC ArityEtaExpansionSestoft
begin

context CardinalityPrognosisCorrect
begin
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
    (restrictA (edom ce) (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)), 
     ccTransform a e,
     restr_stack (edom ce) S)"

  definition anal_env :: "(exp \<Rightarrow> 'a::cpo \<rightarrow> 'b::pcpo) \<Rightarrow> heap \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<rightarrow> (var \<Rightarrow> 'b)"
    where "anal_env f \<Gamma> = (\<Lambda> e. (\<lambda> x . fup\<cdot>(f (the (map_of \<Gamma> x)))\<cdot>(e x)))"


  inductive consistent :: "tstate \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ce \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> heap_upds_ok (\<Gamma>, S)
    \<Longrightarrow> edom ae = edom ce
    \<Longrightarrow> Astack (restr_stack (edom ce) S) \<sqsubseteq> a
    \<Longrightarrow> prognosis ae a (\<Gamma>, e, S) \<sqsubseteq> ce
    \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a) f|` edom ce \<sqsubseteq> ae
    \<Longrightarrow> (\<And> x. x \<in> thunks \<Gamma> \<Longrightarrow> many \<sqsubseteq> ce x \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> const_on ae (ap S \<inter> edom ce) (up\<cdot>0)
    \<Longrightarrow> const_on ae (upds S \<inter> edom ce) (up\<cdot>0)
    \<Longrightarrow> consistent (ae, ce, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, ce, a) (\<Gamma>, e, S)"

  lemma closed_consistent:
    assumes "fv e = ({}::var set)"
    shows "consistent (\<bottom>, \<bottom>, 0) ([], e, [])"
  proof-
    from assms
    have "edom (Aexp e\<cdot>0) = {}"
      by (auto dest!: set_mp[OF Aexp_edom])
    moreover
    from assms
    have "edom (prognosis \<bottom> 0 ([], e, [])) = {}"
     by (auto dest!: set_mp[OF edom_prognosis])
    ultimately
    show ?thesis
      by (auto simp add: edom_empty_iff_bot)
  qed

  lemma foo:
    fixes c c' R 
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,ce,a) c"
    shows "\<exists>ae' ce' a'. consistent (ae',ce',a') c' \<and> conf_transform (ae,ce,a) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae',ce',a') c'"
  using assms
  proof(induction c c' arbitrary: ae ce a rule:step_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    have "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)" by (rule prognosis_App)
    with app\<^sub>1 have "consistent (ae, ce, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by (cases "x \<in> edom ce")  (auto simp add: join_below_iff env_restr_join dest!: below_trans[OF env_restr_mono[OF Aexp_App]] elim: below_trans)
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
    have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) f|` edom ce  \<sqsubseteq> (env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<squnion> esing x\<cdot>(up\<cdot>0)) f|` edom ce" by (rule env_restr_mono[OF Aexp_subst])
    also have "\<dots> =  env_delete y ((Aexp e)\<cdot>(pred\<cdot>a))  f|` edom ce \<squnion> esing x\<cdot>(up\<cdot>0)  f|` edom ce" by (simp add: env_restr_join)
    also have "env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<sqsubseteq> Aexp (Lam [y]. e)\<cdot>a" by (rule Aexp_Lam)
    also have "\<dots> f|` edom ce \<sqsubseteq> ae" using app\<^sub>2 by (auto simp add: join_below_iff env_restr_join)
    also have "esing x\<cdot>(up\<cdot>0) f|` edom ce  \<sqsubseteq> ae" using app\<^sub>2 by (cases "x\<in>edom ce") (auto simp add: env_restr_join)
    also have "ae \<squnion> ae = ae" by simp
    finally  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) f|` edom ce \<sqsubseteq> ae" by this simp_all
    }
    ultimately
    have "consistent (ae, ce, pred\<cdot>a) (\<Gamma>, e[y::=x], S)" using app\<^sub>2
      by (auto elim: below_trans edom_mono  simp add: join_below_iff env_restr_join)
    moreover
    have "conf_transform (ae, ce, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
    ultimately
    show ?case by (blast  del: consistentI consistentE)
  next
  case (thunk \<Gamma> x e S)
    hence "x \<in> thunks \<Gamma>" by auto
    hence [simp]: "x \<in> domA \<Gamma>" by (rule set_mp[OF thunks_domA])
    hence "x \<notin> upds S" using thunk by (auto elim!: heap_upds_okE)

    from thunk have "prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce" by auto
    from below_trans[OF prognosis_called fun_belowD[OF this] ]
    have [simp]: "x \<in> edom ce" by (auto simp add: edom_def)
  
    from thunk
    have "Aexp (Var x)\<cdot>a  f|` edom ce \<sqsubseteq> ae" by (auto simp add: join_below_iff env_restr_join)
    from fun_belowD[where x = x, OF this] 
    have "(Aexp (Var x)\<cdot>a) x \<sqsubseteq> ae x" by simp
    from below_trans[OF  Aexp_Var this]
    have "up\<cdot>a \<sqsubseteq> ae x".    
    then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
    hence [simp]: "x \<in> edom ae" by (simp add: edom_def)

    have "Astack (restr_stack (edom ce) S) \<sqsubseteq> u" using thunk `a \<sqsubseteq> u` by (auto elim: below_trans)
  
    from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
    have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
    moreover have "\<dots> f|` edom ce \<sqsubseteq> ae" using thunk by (auto simp add: join_below_iff env_restr_join)
    ultimately have "(ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u) f|` edom ce \<sqsubseteq> ae" by simp

    show ?case
    proof(cases "ce x" rule:two_cases)
      case none
      with `x \<in> edom ce` have False by (auto simp add: edom_def)
      thus ?thesis..
    next
      case once

      note `ae x = up\<cdot>u` 
      moreover
  
      from `prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce`
      have "prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once"
        using once by (metis (mono_tags) fun_belowD)
      hence "x \<notin> ap S" using prognosis_ap[of ae a \<Gamma> "(Var x)" S] by auto
      
  
      from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `\<not> isVal e`
      have *: "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
        by (rule prognosis_Var_thunk)
  
      from `prognosis ae a (\<Gamma>, Var x, S) x \<sqsubseteq> once`
      have "(record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))) x = none"
        by (simp add: two_pred_none)
      hence **: "prognosis ae u (delete x \<Gamma>, e, Upd x # S) x = none" using fun_belowD[OF *, where x = x] by auto

      have eq: "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) = prognosis ae u (delete x \<Gamma>, e, Upd x # S)"
        by (rule prognosis_env_cong) simp

      have [simp]: "restr_stack (edom ce - {x}) S = restr_stack (edom ce) S" 
        using `x \<notin> upds S` by (auto intro: restr_stack_cong)
    
      have "prognosis (env_delete x ae) u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> env_delete x ce"
        unfolding eq
        using ** below_trans[OF below_trans[OF * Cfun.monofun_cfun_arg[OF `prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce`]] record_call_below_arg]
        by (rule below_env_deleteI)
      moreover

      have "ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) = ABinds (delete x \<Gamma>)\<cdot>ae" by (rule Abinds_env_cong) simp
      with `(ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u) f|\` edom ce \<sqsubseteq> ae`
      have "(ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u) f|` edom ce \<sqsubseteq> ae" by simp
      from env_restr_mono[where S = "-{x}", OF this]
      have "(ABinds (delete x \<Gamma>)\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u) f|` edom (env_delete x ce) \<sqsubseteq> env_delete x ae"
        by (auto simp add: Diff_eq Int_commute env_delete_restr)

      moreover
  
      have "const_on ae (ap S \<inter> edom ce) (up\<cdot>0)" using thunk by auto
      hence "const_on (env_delete x ae) (ap S \<inter> edom ce) (up\<cdot>0)" using `x \<notin>  ap S`
        by (fastforce simp add: env_delete_def)
      moreover
  
      have "const_on ae (upds S \<inter> edom ce) (up\<cdot>0)" using thunk by auto
      hence "const_on (env_delete x ae) (upds S \<inter> (edom (env_delete x ce))) (up\<cdot>0)" by fastforce
      ultimately

      have "consistent (env_delete x ae, env_delete x ce, u) (delete x \<Gamma>, e, Upd x # S)" using thunk `a \<sqsubseteq> u`
        by (auto simp add: join_below_iff env_restr_join insert_absorb restr_delete_twist elim:below_trans below_trans[OF env_restr_mono2, rotated])
      moreover
      
      {
      from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` once
      have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)) x = Some (Aeta_expand u (transform u e))"
        by (simp add: map_of_map_transform)
      hence "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G
             (restrictA (edom ce) (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), Upd x # restr_stack (edom ce) S)"
          by (auto simp add:  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist simp del: restr_delete)
      also
      have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ce) (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), Aeta_expand u (ccTransform u e), restr_stack (edom ce) S)"
        by (rule r_into_rtranclp, rule)
      also
      have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (restrictA (edom ce)  (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>))), ccTransform u e, restr_stack (edom ce) S)"
        by (intro normal_trans Aeta_expand_correct `Astack (restr_stack (edom ce) S) \<sqsubseteq> u`)
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
  
      from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `\<not> isVal e`
      have "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
        by (rule prognosis_Var_thunk)
      also note record_call_below_arg
      finally
      have *: "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by this simp_all
  
      have "ae x = up\<cdot>0" using thunk many `x \<in> thunks \<Gamma>` by (auto)
      hence "u = 0" using `ae x = up\<cdot>u` by simp
  
      
      have "prognosis ae 0 (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> ce" using *[unfolded `u=0`] thunk by (auto elim: below_trans)
      moreover
      note `(ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u) f|\` edom ce \<sqsubseteq> ae`
      ultimately
      have "consistent (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)" using thunk `ae x = up\<cdot>u` `u = 0`  by auto
      moreover
  
      from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>0` many
      have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)) x = Some (transform 0 e)"
        by (simp add: map_of_map_transform)
      with `\<not> isVal e`
      have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) (delete x \<Gamma>, e, Upd x # S)"
        by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
      ultimately
      show ?thesis by (blast del: consistentI consistentE)
    qed
  next
  case (lamvar \<Gamma> x e S)
    from lamvar have "prognosis ae a (\<Gamma>, Var x, S) \<sqsubseteq> ce" by auto
    from below_trans[OF prognosis_called fun_belowD[OF this] ]
    have [simp]: "x \<in> edom ce" by (auto simp add: edom_def)
    then obtain c where "ce x = up\<cdot>c" by (cases "ce x") (auto simp add: edom_def)

    from lamvar have [simp]: "x \<in> domA \<Gamma>" by auto (metis domI dom_map_of_conv_domA)
    from lamvar have "Aexp (Var x)\<cdot>a f|` edom ce \<sqsubseteq> ae" by (auto simp add: join_below_iff env_restr_join)
    from fun_belowD[where x = x, OF this] 
    have "(Aexp (Var x)\<cdot>a) x \<sqsubseteq> ae x" by simp
    from below_trans[OF Aexp_Var this]
    have "up\<cdot>a \<sqsubseteq> ae x".
    then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
    hence "x \<in> edom ae" by (auto simp add: edom_def)

    from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
    have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
    moreover have "\<dots> f|` edom ce \<sqsubseteq> ae" using lamvar by (auto simp add: join_below_iff env_restr_join)
    ultimately have "(ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u) f|` edom ce \<sqsubseteq> ae" by simp

    have "prognosis ae u ((x, e) # delete x \<Gamma>, e, S) = prognosis ae u (\<Gamma>, e, S)"
      using `map_of \<Gamma> x = Some e` by (auto intro!: prognosis_reorder)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
       using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `isVal e`  by (rule prognosis_Var_lam)
    also have "\<dots> \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by (rule record_call_below_arg)
    finally have *: "prognosis ae u ((x, e) # delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S)" by this simp_all
  
    have "consistent (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)"
      using lamvar `(ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u) f|\` edom ce \<sqsubseteq> ae`   `ae x = up\<cdot>u` edom_mono[OF *]
      by (auto simp add: join_below_iff env_restr_join thunks_Cons restr_delete_twist split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`] below_trans[OF *])
    moreover
  
    have "Astack (restr_stack (edom ce) S) \<sqsubseteq> u" using lamvar below_trans[OF _ `a \<sqsubseteq> u`] by auto
  
    {
    from `isVal e`
    have "isVal (transform u e)" by simp
    hence "isVal (Aeta_expand u (transform u e))" by (rule isVal_Aeta_expand)
    moreover
    from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isVal (transform u e)`
    have "map_of (restrictA (edom ce) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))) x = Some (Aeta_expand u (transform u e))"
      by (simp add: map_of_map_transform)
    ultimately
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
          ((x, Aeta_expand u (transform u e)) # delete x (restrictA (edom ce) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))), Aeta_expand u  (transform u e), restr_stack (edom ce) S)"
       by (auto intro: lambda_var simp add: map_transform_delete simp del: restr_delete)
    also have "\<dots> = (restrictA (edom ce) ((map_transform Aeta_expand ae (map_transform transform ae ((x,e) # delete x \<Gamma>)))), Aeta_expand u  (transform u e), restr_stack (edom ce) S)"
      using `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isVal (transform u e)`
      by (simp add: map_transform_Cons map_transform_delete restr_delete_twist del: restr_delete)
    also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* conf_transform (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)"
      by simp (rule Aeta_expand_correct[OF `Astack (restr_stack (edom ce) S) \<sqsubseteq> u`])
    finally(rtranclp_trans)
    have "conf_transform (ae, ce, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* conf_transform (ae, ce, u) ((x, e) # delete x \<Gamma>, e, S)".
    }
    ultimately show ?case by (blast intro: normal_trans del: consistentI consistentE)
  next
  case (var\<^sub>2 \<Gamma> x e S)
    show ?case
    proof(cases "x \<in> edom ce")
      case True[simp]
      hence "ce x \<noteq> \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)
      hence "ae x = up\<cdot>a" using var\<^sub>2 by auto
  
      obtain c where "ce x = up\<cdot>c" using `ce x \<noteq> \<bottom>` by (cases "ce x") auto
  
      have "Astack (Upd x # S) \<sqsubseteq> a" using var\<^sub>2 by auto
      hence "a = 0" by auto
  
      from `isVal e` `x \<notin> domA \<Gamma>`
      have *: "prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)" by (rule prognosis_Var2)

      have "consistent (ae, ce, 0) ((x, e) # \<Gamma>, e, S)"
        using var\<^sub>2
        by (auto simp add: join_below_iff env_restr_join thunks_Cons split:if_splits elim:below_trans[OF *])
      moreover
      have "conf_transform (ae, ce, a) (\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0) ((x, e) # \<Gamma>, e, S)"
        using `ae x = up\<cdot>a` `a = 0` var\<^sub>2 `ce x = up\<cdot>c`
        by (auto intro!: step.intros simp add: map_transform_Cons)
      ultimately show ?thesis by (blast del: consistentI consistentE)
    next
      case False[simp]
      hence "ce x = \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)

      from False have "x \<notin> edom ae" using var\<^sub>2 by auto
      hence [simp]: "ae x = \<bottom>" by (auto simp add: edom_def)

      
      have "prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae a ((x, e) # \<Gamma>, e, Upd x # S)" by (rule prognosis_upd)
      also
       
      from `ae x = \<bottom>`
      have "prognosis ae a ((x, e) # \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae a (delete x ((x,e) # \<Gamma>), e, Upd x # S)"
        by (rule prognosis_not_called)
      also have  "delete x ((x,e)#\<Gamma>) = \<Gamma>" using `x \<notin> domA \<Gamma>` by simp
      finally
      have *: "prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, e, Upd x # S)" by this simp

      have "consistent (ae, ce, a) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
        by (auto simp add: join_below_iff env_restr_join `ce x = \<bottom>` thunks_Cons split:if_splits elim:below_trans[OF *])
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
    hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom ?ce" by (auto simp add: edom_cHeap dest!: set_mp[OF edom_Aheap])
  
    have restr_stack_simp2: "restr_stack (edom (?ce \<squnion> ce)) S = restr_stack (edom ce) S"
      by (auto intro: restr_stack_cong dest!: *)
  
    have "edom ae \<subseteq> domA \<Gamma> \<union> upds S" using let\<^sub>1 by auto
    from set_mp[OF this] fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    have "edom ae \<inter> domA \<Delta> = {}" by (auto dest: set_mp[OF ups_fv_subset])
    hence [simp]: "\<And> S. S \<subseteq> domA \<Delta> \<Longrightarrow> ae f|` S = \<bottom>" by auto

    have "edom ce \<subseteq> domA \<Gamma> \<union> upds S" using let\<^sub>1 by auto
    from set_mp[OF this] fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    have "edom ce \<inter> domA \<Delta> = {}"
       by (auto dest: set_mp[OF ups_fv_subset])

    from fresh_distinct[OF let\<^sub>1(1)]
    have "edom ?ae \<inter> domA \<Gamma> = {}" by (auto dest: set_mp[OF edom_Aheap])
    hence "edom ?ce \<inter> domA \<Gamma> = {}" by (simp add: edom_cHeap)

  
    from  fresh_distinct[OF let\<^sub>1(1)]
    have [simp]: "\<And> S. S \<subseteq> domA \<Gamma> \<Longrightarrow> ?ae f|` S = \<bottom>" by (auto dest!: set_mp[OF edom_Aheap])
  
    {
    have "edom (?ce \<squnion> ce) \<subseteq> domA (\<Delta> @ \<Gamma>) \<union> upds S"
      using let\<^sub>1(3) by (auto simp add: edom_cHeap dest: set_mp[OF edom_Aheap])
    moreover
    have "edom (?ae \<squnion> ae) = edom (?ce \<squnion> ce)"
      using let\<^sub>1(3) by (auto simp add: edom_cHeap)
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
    have [simp]: "ap S \<inter> edom (cHeap \<Delta> e\<cdot>a) = {}"
      using fresh_distinct_fv[OF let\<^sub>1(2)] 
      by (auto simp add: edom_cHeap dest!: set_mp[OF edom_Aheap] set_mp[OF ap_fv_subset])

    have "const_on ae (ap S \<inter> edom ce) (up\<cdot>0)" using let\<^sub>1 by auto  
    hence "const_on (?ae \<squnion> ae) (ap S \<inter> edom ce) (up\<cdot>0)" by fastforce
    hence "const_on (?ae \<squnion> ae) (ap S \<inter> edom (?ce \<squnion> ce)) (up\<cdot>0)" by (simp add: Int_Un_distrib)
    moreover
    have "const_on ae (upds (restr_stack (edom ce) S)) (up\<cdot>0)" using let\<^sub>1 by auto
    hence "const_on (?ae \<squnion> ae) (upds (restr_stack (edom ce) S)) (up\<cdot>0)"  by fastforce
    hence "const_on (?ae \<squnion> ae) (upds (restr_stack (edom (?ce \<squnion> ce)) S)) (up\<cdot>0)" unfolding restr_stack_simp2.
    moreover
    have "Astack (restr_stack (edom (?ce \<squnion> ce)) S) \<sqsubseteq> a" unfolding restr_stack_simp2 using let\<^sub>1 by auto
    moreover
    have "edom (?ce \<squnion> ce) \<subseteq> edom (?ae \<squnion> ae)" using let\<^sub>1 by (auto simp add: edom_cHeap)
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
    moreover
    have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a" by (rule Aexp_Let)
    moreover
    have "(ABinds \<Gamma>\<cdot>ae \<squnion> Aexp (Let \<Delta> e)\<cdot>a) f|` edom ce \<sqsubseteq> ae" using let\<^sub>1 by auto
    moreover
    have "Aexp (Terms.Let \<Delta> e)\<cdot>a f|` (edom ce \<union> edom (cHeap \<Delta> e\<cdot>a)) = Aexp (Terms.Let \<Delta> e)\<cdot>a f|` edom ce"
      by (rule env_restr_cong) (auto simp add: edom_cHeap dest!: set_mp[OF Aexp_edom]  set_mp[OF edom_Aheap])
    moreover
    have "ABinds \<Gamma>\<cdot>ae f|` (edom ce \<union> edom (cHeap \<Delta> e\<cdot>a)) = ABinds \<Gamma>\<cdot>ae f|` edom ce" 
      using fresh_distinct_fv[OF let\<^sub>1(1)]
      by (auto intro: env_restr_cong  simp add: edom_cHeap dest!: set_mp[OF Aexp_edom]  set_mp[OF edom_Aheap] set_mp[OF edom_AnalBinds])
    ultimately
    have "(ABinds (\<Delta> @ \<Gamma>) \<cdot> (Aheap \<Delta> e\<cdot>a \<squnion> ae) \<squnion> Aexp e\<cdot>a) f|` edom (?ce \<squnion> ce) \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> ae"
      by (simp only: join_assoc[symmetric] restrictA_append Abinds_append_disjoint[OF fresh_distinct[OF let\<^sub>1(1)]] join_below_iff env_restr_join)
         (auto 4 4 simp add: join_below_iff env_restr_join intro: below_trans[OF env_restr_below_self] elim!: below_trans[OF env_restr_mono] below_trans)
    }
    ultimately
    have "consistent (?ae \<squnion> ae, ?ce \<squnion> ce, a) (\<Delta> @ \<Gamma>, e, S) "
      by auto
    }
    moreover
    {
      have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ae" "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ce"
        using fresh_distinct[OF let\<^sub>1(1)]
        by (auto simp add: edom_cHeap dest!: set_mp[OF edom_Aheap])
      hence "restrictA (edom (?ce \<squnion> ce)) (map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Gamma>))
         = restrictA (edom ce) (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>))"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      moreover
  
      from let\<^sub>1 have *: "edom ce \<subseteq> domA \<Gamma> \<union> upds S"  "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
      have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ce" and  "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
         using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
         by (auto dest!: set_mp[OF *(1)] set_mp[OF *(2)] set_mp[OF ups_fv_subset])
      hence "restrictA (edom (?ce \<squnion> ce)) (map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Delta>))
         = restrictA (edom ?ce) (map_transform Aeta_expand ?ae (map_transform transform ?ae \<Delta>))"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      ultimately
  
      have "conf_transform (ae, ce, a) (\<Gamma>, Let \<Delta> e, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (?ae \<squnion> ae, ?ce \<squnion> ce, a) (\<Delta> @ \<Gamma>, e, S)"
        using restr_stack_simp2 let\<^sub>1(1,2)
        by (fastforce intro!: let_and_restrict simp  add: map_transform_append restrictA_append  edom_cHeap  dest: set_mp[OF edom_Aheap])
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
