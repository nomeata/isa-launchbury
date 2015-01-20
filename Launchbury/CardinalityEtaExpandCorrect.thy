theory CardinalityEtaExpandCorrect
imports ArityEtaExpand CardinalityAnalysisSpec AbstractTransform Sestoft SestoftGC ArityEtaExpansionSestoft ArityAnalysisStack  ArityConsistent
begin

context CardinalityPrognosisCorrect
begin
  sublocale AbstractTransformBoundSubst
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
    "fst"
    "snd"
    "\<lambda> _. 0"
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

  type_synonym tstate = "(AEnv \<times> (var \<Rightarrow> two) \<times> Arity \<times> Arity list)"

  fun transform_alts :: "Arity list \<Rightarrow> stack \<Rightarrow> stack"
    where 
      "transform_alts _ [] = []"
    | "transform_alts (a#as) (Alts e1 e2 # S) = (Alts (ccTransform a e1) (ccTransform a e2)) # transform_alts as S"
    | "transform_alts as (x # S) = x # transform_alts as S"

  lemma transform_alts_Nil[simp]: "transform_alts [] S = S"
    by (induction  S) auto

  lemma Astack_transform_alts[simp]:
    "Astack (transform_alts as S) = Astack S"
   by (induction rule: transform_alts.induct) auto

  lemma fresh_star_transform_alts[intro]: "a \<sharp>* S \<Longrightarrow> a \<sharp>* transform_alts as S"
   by (induction as S  rule: transform_alts.induct) (auto simp add: fresh_star_Cons)

  fun a_transform :: "astate \<Rightarrow> conf \<Rightarrow> conf"
  where "a_transform (ae, a, as) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>), 
     ccTransform a e,
     transform_alts as  S)"

  fun restr_conf :: "var set \<Rightarrow> conf \<Rightarrow> conf"
    where "restr_conf V (\<Gamma>, e, S) = (restrictA V \<Gamma>, e, restr_stack V S)"

  fun conf_transform :: "tstate \<Rightarrow> conf \<Rightarrow> conf"
  where "conf_transform (ae, ce, a, as) c = a_transform (ae, a, as) (restr_conf (edom ce) c)"


  inductive consistent :: "tstate \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "a_consistent (ae, a, as) (restr_conf (edom ce) (\<Gamma>, e, S))
    \<Longrightarrow> heap_upds_ok (\<Gamma>, S)
    \<Longrightarrow> edom ae = edom ce
    \<Longrightarrow> prognosis ae as a (\<Gamma>, e, S) \<sqsubseteq> ce
    \<Longrightarrow> (\<And> x. x \<in> thunks \<Gamma> \<Longrightarrow> many \<sqsubseteq> ce x \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> consistent (ae, ce, a, as) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, ce, a, as) (\<Gamma>, e, S)"

  lemma closed_consistent:
    assumes "fv e = ({}::var set)"
    shows "consistent (\<bottom>, \<bottom>, 0, []) ([], e, [])"
  proof-
    from assms
    have "edom (prognosis \<bottom> [] 0 ([], e, [])) = {}"
     by (auto dest!: set_mp[OF edom_prognosis])
    thus ?thesis
      by (auto simp add: edom_empty_iff_bot closed_a_consistent[OF assms])
  qed

  lemma foo:
    fixes c c' R 
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,ce,a,as) c"
    shows "\<exists>ae' ce' a' as'. consistent (ae',ce',a',as') c' \<and> conf_transform (ae,ce,a,as) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae',ce',a',as') c'"
  using assms
  proof(induction c c' arbitrary: ae ce a as rule:step_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    have "prognosis ae as (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, App e x, S)" by (rule prognosis_App)
    with app\<^sub>1 have "consistent (ae, ce, inc\<cdot>a, as) (\<Gamma>, e, Arg x # S)"
      by (auto intro: a_consistent_app\<^sub>1 elim: below_trans)
    moreover
    have "conf_transform (ae, ce, a, as) (\<Gamma>, App e x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, inc\<cdot>a, as) (\<Gamma>, e, Arg x # S)"
      by simp rule
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
  case (app\<^sub>2 \<Gamma> y e x S)
    have "prognosis ae as (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae as a (\<Gamma>, (Lam [y]. e), Arg x # S)"
       by (rule prognosis_subst_Lam)
    then
    have "consistent (ae, ce, pred\<cdot>a, as) (\<Gamma>, e[y::=x], S)" using app\<^sub>2
      by (auto 4 3 intro: a_consistent_app\<^sub>2 elim: below_trans)
    moreover
    have "conf_transform (ae, ce, a, as) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, pred \<cdot> a, as) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
    ultimately
    show ?case by (blast  del: consistentI consistentE)
  next
  case (thunk \<Gamma> x e S)
    hence "x \<in> thunks \<Gamma>" by auto
    hence [simp]: "x \<in> domA \<Gamma>" by (rule set_mp[OF thunks_domA])
    hence "x \<notin> upds S" using thunk by (auto elim!: heap_upds_okE)

    from thunk have "prognosis ae as a (\<Gamma>, Var x, S) \<sqsubseteq> ce" by auto
    from below_trans[OF prognosis_called fun_belowD[OF this] ]
    have [simp]: "x \<in> edom ce" by (auto simp add: edom_def)

    have "x \<in> edom ae" using thunk by auto
    then obtain u where "ae x = up\<cdot>u" by (cases "ae x") (auto simp add: edom_def)
  

    show ?case
    proof(cases "ce x" rule:two_cases)
      case none
      with `x \<in> edom ce` have False by (auto simp add: edom_def)
      thus ?thesis..
    next
      case once

      from `prognosis ae as a (\<Gamma>, Var x, S) \<sqsubseteq> ce`
      have "prognosis ae as a (\<Gamma>, Var x, S) x \<sqsubseteq> once"
        using once by (metis (mono_tags) fun_belowD)
      hence "x \<notin> ap S" using prognosis_ap[of ae as a \<Gamma> "(Var x)" S] by auto
      
  
      from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `\<not> isVal e`
      have *: "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))"
        by (rule prognosis_Var_thunk)
  
      from `prognosis ae as a (\<Gamma>, Var x, S) x \<sqsubseteq> once`
      have "(record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))) x = none"
        by (simp add: two_pred_none)
      hence **: "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) x = none" using fun_belowD[OF *, where x = x] by auto

      have eq: "prognosis (env_delete x ae) as u (delete x \<Gamma>, e, Upd x # S) = prognosis ae as u (delete x \<Gamma>, e, Upd x # S)"
        by (rule prognosis_env_cong) simp

      have [simp]: "restr_stack (edom ce - {x}) S = restr_stack (edom ce) S" 
        using `x \<notin> upds S` by (auto intro: restr_stack_cong)
    
      have "prognosis (env_delete x ae) as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> env_delete x ce"
        unfolding eq
        using ** below_trans[OF below_trans[OF * Cfun.monofun_cfun_arg[OF `prognosis ae as a (\<Gamma>, Var x, S) \<sqsubseteq> ce`]] record_call_below_arg]
        by (rule below_env_deleteI)
      moreover

      have *: "a_consistent (env_delete x ae, u, as) (delete x (restrictA (edom ce) \<Gamma>), e, restr_stack (edom ce) S)" using thunk `ae x = up\<cdot>u`
          by (auto intro!: a_consistent_thunk_once simp del: restr_delete)
      ultimately

      have "consistent (env_delete x ae, env_delete x ce, u, as) (delete x \<Gamma>, e, Upd x # S)" using thunk
        by (auto  simp add:   restr_delete_twist elim:below_trans )
      moreover

      from *
      have "Astack (transform_alts as (restr_stack (edom ce) S)) \<sqsubseteq> u" by (auto elim: a_consistent_stackD)
      
      {
      from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` once
      have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae (restrictA (edom ce) \<Gamma>))) x = Some (Aeta_expand u (transform u e))"
        by (simp add: map_of_map_transform)
      hence "conf_transform (ae, ce, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G
             (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae (restrictA (edom ce) \<Gamma>))), Aeta_expand u (ccTransform u e), Upd x # transform_alts as (restr_stack (edom ce) S))"
          by (auto simp add:  map_transform_delete delete_map_transform_env_delete insert_absorb restr_delete_twist simp del: restr_delete)
      also
      have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae (restrictA (edom ce) \<Gamma>))), Aeta_expand u (ccTransform u e), transform_alts as (restr_stack (edom ce) S))"
        by (rule r_into_rtranclp, rule)
      also
      have "\<dots> \<Rightarrow>\<^sub>G\<^sup>* (delete x (map_transform Aeta_expand ae (map_transform ccTransform ae  (restrictA (edom ce) \<Gamma>))), ccTransform u e, transform_alts as (restr_stack (edom ce) S))"
        by (intro normal_trans Aeta_expand_correct `Astack (transform_alts as (restr_stack (edom ce) S)) \<sqsubseteq> u`)
      also(rtranclp_trans)
      have "\<dots> = conf_transform (env_delete x ae, env_delete x ce, u, as) (delete x \<Gamma>, e, Upd x # S)" 
        by (auto intro!: map_transform_cong simp add:  map_transform_delete[symmetric]  restr_delete_twist)
      finally(back_subst)
      have "conf_transform (ae, ce, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (env_delete x ae, env_delete x ce, u, as) (delete x \<Gamma>, e, Upd x # S)".
      }
      ultimately
      show ?thesis by (blast del: consistentI consistentE)
  
    next
      case many
  
      from `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `\<not> isVal e`
      have "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))"
        by (rule prognosis_Var_thunk)
      also note record_call_below_arg
      finally
      have *: "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, Var x, S)" by this simp_all
  
      have "ae x = up\<cdot>0" using thunk many `x \<in> thunks \<Gamma>` by (auto)
      hence "u = 0" using `ae x = up\<cdot>u` by simp
  
      
      have "prognosis ae as 0 (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> ce" using *[unfolded `u=0`] thunk by (auto elim: below_trans)
      moreover
      have "a_consistent (ae, 0, as) (delete x (restrictA (edom ce) \<Gamma>), e, Upd x # restr_stack (edom ce) S)" using thunk `ae x = up\<cdot>0`
        by (auto intro!: a_consistent_thunk_0 simp del: restr_delete)
      ultimately
      have "consistent (ae, ce, 0, as) (delete x \<Gamma>, e, Upd x # S)" using thunk `ae x = up\<cdot>u` `u = 0`
        by (auto simp add:  restr_delete_twist)
      moreover
  
      from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>0` many
      have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae (restrictA (edom ce) \<Gamma>))) x = Some (transform 0 e)"
        by (simp add: map_of_map_transform)
      with `\<not> isVal e`
      have "conf_transform (ae, ce, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0, as) (delete x \<Gamma>, e, Upd x # S)"
        by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
      ultimately
      show ?thesis by (blast del: consistentI consistentE)
    qed
  next
  case (lamvar \<Gamma> x e S)
    from lamvar(1) have [simp]: "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)

    from lamvar have "prognosis ae as a (\<Gamma>, Var x, S) \<sqsubseteq> ce" by auto
    from below_trans[OF prognosis_called fun_belowD[OF this] ]
    have [simp]: "x \<in> edom ce" by (auto simp add: edom_def)
    then obtain c where "ce x = up\<cdot>c" by (cases "ce x") (auto simp add: edom_def)

    then have "x \<in> edom ae" using lamvar by auto
    then obtain  u where "ae x = up\<cdot>u"  by (cases "ae x") (auto simp add: edom_def)


    have "prognosis ae as u ((x, e) # delete x \<Gamma>, e, S) = prognosis ae as u (\<Gamma>, e, S)"
      using `map_of \<Gamma> x = Some e` by (auto intro!: prognosis_reorder)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))"
       using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` `isVal e`  by (rule prognosis_Var_lam)
    also have "\<dots> \<sqsubseteq> prognosis ae as a (\<Gamma>, Var x, S)" by (rule record_call_below_arg)
    finally have *: "prognosis ae as u ((x, e) # delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae as a (\<Gamma>, Var x, S)" by this simp_all
    moreover
    have "a_consistent (ae, u, as) ((x,e) # delete x (restrictA (edom ce) \<Gamma>), e, restr_stack (edom ce) S)" using lamvar `ae x = up\<cdot>u`
      by (auto intro!: a_consistent_lamvar simp del: restr_delete)
    ultimately
    have "consistent (ae, ce, u, as) ((x, e) # delete x \<Gamma>, e, S)"
      using lamvar edom_mono[OF *] by (auto simp add:  thunks_Cons restr_delete_twist elim: below_trans)
    moreover

    from `a_consistent _ _`
    have "Astack (transform_alts as (restr_stack (edom ce) S)) \<sqsubseteq> u" by (auto elim: a_consistent_stackD)
  
    {
    from `isVal e`
    have "isVal (transform u e)" by simp
    hence "isVal (Aeta_expand u (transform u e))" by (rule isVal_Aeta_expand)
    moreover
    from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isVal (transform u e)`
    have "map_of (map_transform Aeta_expand ae (map_transform transform ae (restrictA (edom ce) \<Gamma>))) x = Some (Aeta_expand u (transform u e))"
      by (simp add: map_of_map_transform)
    ultimately
    have "conf_transform (ae, ce, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
          ((x, Aeta_expand u (transform u e)) # delete x (map_transform Aeta_expand ae (map_transform transform ae (restrictA (edom ce) \<Gamma>))), Aeta_expand u (transform u e), transform_alts as (restr_stack (edom ce) S))"
       by (auto intro: lambda_var simp add: map_transform_delete simp del: restr_delete)
    also have "\<dots> = ((map_transform Aeta_expand ae (map_transform transform ae ((x,e) # delete x (restrictA (edom ce) \<Gamma>)))), Aeta_expand u  (transform u e), transform_alts as (restr_stack (edom ce) S))"
      using `ae x = up \<cdot> u` `ce x = up\<cdot>c` `isVal (transform u e)`
      by (simp add: map_transform_Cons map_transform_delete restr_delete_twist del: restr_delete)
    also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* conf_transform (ae, ce, u, as) ((x, e) # delete x \<Gamma>, e, S)"
      by (simp add: restr_delete_twist) (rule Aeta_expand_correct[OF `Astack _ \<sqsubseteq> u`])
    finally(rtranclp_trans)
    have "conf_transform (ae, ce, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* conf_transform (ae, ce, u, as) ((x, e) # delete x \<Gamma>, e, S)".
    }
    ultimately show ?case by (blast intro: normal_trans del: consistentI consistentE)
  next
  case (var\<^sub>2 \<Gamma> x e S)
    show ?case
    proof(cases "x \<in> edom ce")
      case True[simp]
      hence "ce x \<noteq> \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)
      from True have "x \<in> edom ae" using var\<^sub>2 by auto
 
      obtain c where "ce x = up\<cdot>c" using `ce x \<noteq> \<bottom>` by (cases "ce x") auto
  
      from var\<^sub>2
      have "a_consistent (ae, a, as) (restrictA (edom ce) \<Gamma>, e, Upd x # restr_stack (edom ce) S)" by auto
      from a_consistent_UpdD[OF this  `x \<in> edom ae`]
      have "ae x = up\<cdot>0" and "a = 0".
  
      from `isVal e` `x \<notin> domA \<Gamma>`
      have *: "prognosis ae as 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae as 0 (\<Gamma>, e, Upd x # S)" by (rule prognosis_Var2)
      moreover
      have "a_consistent (ae, a, as) ((x, e) # restrictA (edom ce) \<Gamma>, e, restr_stack (edom ce) S)"
        using var\<^sub>2 by (auto intro!: a_consistent_var\<^sub>2)
      ultimately
      have "consistent (ae, ce, 0, as) ((x, e) # \<Gamma>, e, S)"
        using var\<^sub>2 `a = 0`
        by (auto simp add: thunks_Cons elim: below_trans)
      moreover
      have "conf_transform (ae, ce, a, as) (\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0, as) ((x, e) # \<Gamma>, e, S)"
        using `ae x = up\<cdot>0` `a = 0` var\<^sub>2 `ce x = up\<cdot>c`
        by (auto intro!: step.intros simp add: map_transform_Cons)
      ultimately show ?thesis by (blast del: consistentI consistentE)
    next
      case False[simp]
      hence "ce x = \<bottom>" using var\<^sub>2 by (auto simp add: edom_def)

      from False have "x \<notin> edom ae" using var\<^sub>2 by auto
      hence [simp]: "ae x = \<bottom>" by (auto simp add: edom_def)

      
      have "prognosis ae as a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae as a ((x, e) # \<Gamma>, e, Upd x # S)" by (rule prognosis_upd)
      also
       
      from `ae x = \<bottom>`
      have "prognosis ae as a ((x, e) # \<Gamma>, e, Upd x # S) \<sqsubseteq> prognosis ae as a (delete x ((x,e) # \<Gamma>), e, Upd x # S)"
        by (rule prognosis_not_called)
      also have  "delete x ((x,e)#\<Gamma>) = \<Gamma>" using `x \<notin> domA \<Gamma>` by simp
      finally
      have *: "prognosis ae as a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae as a (\<Gamma>, e, Upd x # S)" by this simp
      then
      have "consistent (ae, ce, a, as) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
        by (auto simp add: thunks_Cons  elim:below_trans)
      moreover
      have "conf_transform (ae, ce, a, as) (\<Gamma>, e, Upd x # S) = conf_transform (ae, ce, a, as) ((x, e) # \<Gamma>, e, S)"
        by(simp add: map_transform_restrA[symmetric])
      ultimately show ?thesis by (auto del: consistentI consistentE simp del:conf_transform.simps)
    qed
  next
    case (let\<^sub>1 \<Delta> \<Gamma> e S)
    let ?ae = "Aheap \<Delta> e\<cdot>a"
    let ?ce = "cHeap \<Delta> e\<cdot>a"
  
    have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: set_mp[OF ups_fv_subset])
    hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom ?ae" by (auto simp add: edom_cHeap dest!: set_mp[OF edom_Aheap])
    have restr_stack_simp2: "restr_stack (edom (?ae \<squnion> ae)) S = restr_stack (edom ae) S"
      by (auto intro: restr_stack_cong dest!: *)

    have "edom ce = edom ae" using let\<^sub>1 by auto
  
    have "edom ae \<subseteq> domA \<Gamma> \<union> upds S" using let\<^sub>1 by (auto dest!: a_consistent_edom_subsetD)
    from set_mp[OF this] fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    have "edom ae \<inter> domA \<Delta> = {}" by (auto dest: set_mp[OF ups_fv_subset])

    from `edom ae \<inter> domA \<Delta> = {}`
    have [simp]: "edom (Aheap \<Delta> e\<cdot>a) \<inter> edom ae = {}" by (auto dest!: set_mp[OF edom_Aheap]) 

    from fresh_distinct[OF let\<^sub>1(1)]
    have [simp]: "restrictA (edom ae \<union> edom (Aheap \<Delta> e\<cdot>a)) \<Gamma> = restrictA (edom ae) \<Gamma>"
      by (auto intro: restrictA_cong dest!: set_mp[OF edom_Aheap]) 

    {
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
      hence "x \<notin> edom ce" using `edom ae \<subseteq> domA \<Gamma> \<union> upds S` `edom ce = edom ae` by auto
      hence [simp]: "ce x = \<bottom>"  by (auto simp add: edomIff)
  
      assume "many \<sqsubseteq> (?ce \<squnion> ce) x" with `x \<in> thunks \<Delta>`
      have "(?ae \<squnion> ae) x = up\<cdot>0" by (auto simp add: Aheap_heap3)
    }
    moreover
    {
    from let\<^sub>1(1,2) `edom ae \<subseteq> domA \<Gamma> \<union> upds S`
    have "prognosis (?ae \<squnion> ae) as a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> ?ce \<squnion> prognosis ae as a (\<Gamma>, Let \<Delta> e, S)" by (rule prognosis_Let)
    also have "prognosis ae as a (\<Gamma>, Let \<Delta> e, S) \<sqsubseteq> ce" using let\<^sub>1 by auto
    finally have "prognosis (?ae \<squnion> ae) as a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> ?ce \<squnion> ce" by this simp
    }
    moreover
    have "heap_upds_ok (\<Gamma>, S)" using let\<^sub>1 by auto
    with fresh_distinct[OF let\<^sub>1(1)]  `domA \<Delta> \<inter> upds S = {}`
    have "heap_upds_ok (\<Delta> @ \<Gamma>, S)" by (rule heap_upds_ok_append)
    moreover
    
    have "a_consistent (ae, a, as) (restrictA (edom ce) \<Gamma>, Let \<Delta> e, restr_stack (edom ce) S)"
      using let\<^sub>1 by auto
    hence "a_consistent (?ae \<squnion> ae, a, as) (\<Delta> @ restrictA (edom ce) \<Gamma>, e, restr_stack (edom ce) S)"
      using let\<^sub>1(1,2) `edom ae \<inter> domA \<Delta> = {}` 
      by (auto intro!:  a_consistent_let simp del: join_comm)
    hence "a_consistent (?ae \<squnion> ae, a, as) (restrictA (edom (?ae \<squnion> ae)) (\<Delta> @ restrictA (edom ce) \<Gamma>), e, restr_stack (edom ce) S)"
      by (rule a_consistent_restrictA[OF _ order_refl])
    hence "a_consistent (?ae \<squnion> ae, a, as) (restrictA (edom (?ce \<squnion> ce)) (\<Delta> @ \<Gamma>), e, restr_stack (edom (?ce \<squnion> ce)) S)"
      by (simp add: restrictA_append restr_stack_simp2[simplified] edom_cHeap `edom ce = edom ae` Int_Un_distrib2)
    ultimately
    have "consistent (?ae \<squnion> ae, ?ce \<squnion> ce, a, as) (\<Delta> @ \<Gamma>, e, S)"
      by auto
    }
    moreover
    {
      have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ae" "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ce"
        using fresh_distinct[OF let\<^sub>1(1)]
        by (auto simp add: edom_cHeap dest!: set_mp[OF edom_Aheap])
      hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) (restrictA (edom (?ce \<squnion> ce)) \<Gamma>))
         = map_transform Aeta_expand ae (map_transform transform ae (restrictA (edom ce) \<Gamma>))"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      moreover
  
      from `edom ae \<subseteq> domA \<Gamma> \<union> upds S` `edom ce = edom ae`
      have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ce" and  "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
         using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
         by (auto dest!:  set_mp[OF ups_fv_subset])
      hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) (restrictA (edom (?ce \<squnion> ce)) \<Delta>))
         = map_transform Aeta_expand ?ae (map_transform transform ?ae (restrictA (edom ?ce) \<Delta>))"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      ultimately
      
      
      have "conf_transform (ae, ce, a, as) (\<Gamma>, Let \<Delta> e, S) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (?ae \<squnion> ae, ?ce \<squnion> ce, a, as) (\<Delta> @ \<Gamma>, e, S)"
        using restr_stack_simp2 let\<^sub>1(1,2) `edom ce = edom ae`
        apply (auto simp add: map_transform_append restrictA_append edom_cHeap restr_stack_simp2[simplified] map_transform_restrA)
        apply (rule let_and_restrict)
        apply (auto dest: set_mp[OF edom_Aheap])
        done
    }
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case (if\<^sub>1 \<Gamma> scrut e1 e2 S)
    have "prognosis ae as a (\<Gamma>, scrut ? e1 : e2, S) \<sqsubseteq> ce" using if\<^sub>1 by auto
    hence "prognosis ae (a#as) 0 (\<Gamma>, scrut, Alts e1 e2 # S) \<sqsubseteq> ce"
      by (rule below_trans[OF prognosis_IfThenElse])
    hence "consistent (ae, ce, 0, a#as) (\<Gamma>, scrut, Alts e1 e2 # S)"
      using if\<^sub>1  by (auto dest: a_consistent_if\<^sub>1)
    moreover
    have "conf_transform (ae, ce, a, as) (\<Gamma>, scrut ? e1 : e2, S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, 0, a#as) (\<Gamma>, scrut, Alts e1 e2 # S)"
      by (auto intro: normal step.intros)
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case (if\<^sub>2 \<Gamma> b e1 e2 S)
    hence "a_consistent (ae, a, as) (restrictA (edom ce) \<Gamma>, Bool b, Alts e1 e2 # restr_stack (edom ce) S)" by auto
    then  obtain a' as' where [simp]: "as = a' # as'" "a = 0"
      by (rule a_consistent_alts_on_stack)

    {
    have "prognosis ae (a'#as') 0 (\<Gamma>, Bool b, Alts e1 e2 # S) \<sqsubseteq> ce" using if\<^sub>2 by auto
    hence "prognosis ae as' a' (\<Gamma>, if b then e1 else e2, S) \<sqsubseteq> ce" by (rule below_trans[OF prognosis_Alts])
    then
    have "consistent (ae, ce, a', as') (\<Gamma>, if b then e1 else e2, S)" 
      using if\<^sub>2 by (auto dest!: a_consistent_if\<^sub>2)
    }
    moreover
    have "conf_transform (ae, ce, a, as) (\<Gamma>, Bool b, Alts e1 e2 # S) \<Rightarrow>\<^sub>G conf_transform (ae, ce, a', as') (\<Gamma>, if b then e1 else e2, S)"
      by (auto intro:normal  step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case refl thus ?case by auto
  next
    case (trans c c' c'')
      from trans(3)[OF trans(5)]
      obtain ae' ce' a' as' where "consistent (ae', ce', a', as') c'" and *: "conf_transform (ae, ce, a, as) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae', ce', a', as') c'" by blast
      from trans(4)[OF this(1)]
      obtain ae'' ce'' a'' as'' where "consistent (ae'', ce'', a'', as'') c''" and **: "conf_transform (ae', ce', a', as') c' \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae'', ce'', a'', as'') c''" by blast
      from this(1) rtranclp_trans[OF * **]
      show ?case by blast
  qed
end

end
