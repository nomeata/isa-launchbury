theory ArityEtaExpand
imports ArityCorrect ArityEtaExpansionSestoft AbstractTransform ConstOn
begin

locale CardinalityArityTransformation = CorrectArityAnalysisLetNoCard 
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

  abbreviation aTransform where "aTransform \<equiv> transform"

  lemma supp_transform: "supp (transform a e) \<subseteq> supp e"
    by (induction rule: transform.induct)
       (auto simp add: exp_assn.supp Let_supp dest!: set_mp[OF supp_map_transform] set_mp[OF supp_map_transform_step] )
  interpretation supp_bounded_transform transform
    by default (auto simp add: fresh_def supp_transform) 

  fun conf_transform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "conf_transform (ae,  a) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>), 
     transform a e,
     S)"

  inductive consistent :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ae \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> heap_upds_ok (\<Gamma>, S)
    \<Longrightarrow> Astack S \<sqsubseteq> a
    \<Longrightarrow> ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a \<sqsubseteq> ae
    \<Longrightarrow> const_on ae (thunks \<Gamma>) (up\<cdot>0)
    \<Longrightarrow> const_on ae (ap S) (up\<cdot>0)
    \<Longrightarrow> const_on ae (upds S) (up\<cdot>0)
    \<Longrightarrow> consistent (ae, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, a) (\<Gamma>, e, S)"
  
  lemma foo:
    fixes c c' R 
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "consistent (ae,a) c"
    shows "\<exists>ae' ce' a'. consistent (ae',a') c' \<and> conf_transform (ae,a) c \<Rightarrow>\<^sup>* conf_transform (ae',a') c'"
  using assms
  proof(induction c c' arbitrary: ae a rule:step_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    from app\<^sub>1 have "consistent (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by (auto simp add: join_below_iff  dest!: below_trans[OF Aexp_App] elim: below_trans)
    moreover
    have "conf_transform (ae, a) (\<Gamma>, App e x, S) \<Rightarrow> conf_transform (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"
      by simp rule
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
case (app\<^sub>2 \<Gamma> y e x S)
  {
  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) \<sqsubseteq> env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<squnion> esing x\<cdot>(up\<cdot>0)" by (rule Aexp_subst)
  also have "env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<sqsubseteq> Aexp (Lam [y]. e)\<cdot>a" by (rule Aexp_Lam)
  also have "\<dots> \<sqsubseteq> ae" using app\<^sub>2 by (auto simp add: join_below_iff)
  also have "esing x\<cdot>(up\<cdot>0) \<sqsubseteq> ae" using app\<^sub>2 by auto
  also have "ae \<squnion> ae = ae" by simp
  finally  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) \<sqsubseteq> ae" by this simp_all
  }
  then
  have "consistent (ae, pred\<cdot>a) (\<Gamma>, e[y::=x], S)" using app\<^sub>2
    by (auto elim: below_trans edom_mono  simp add: join_below_iff)
  moreover
  have "conf_transform (ae, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> conf_transform (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
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

  have "ae x = up\<cdot>0" using thunk `x \<in> thunks \<Gamma>` by (auto)
  hence "u = 0" using `ae x = up\<cdot>u` by simp

  
  from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by auto
  also have "\<dots> \<sqsubseteq> ae" using thunk by (auto simp add: join_below_iff)
  finally have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae".
  hence "consistent (ae, 0) (delete x \<Gamma>, e, Upd x # S)" using thunk `ae x = up\<cdot>u` `u = 0`
    by (auto intro!: const_onI)
  moreover

  from  `map_of \<Gamma> x = Some e` `ae x = up\<cdot>0`
  have "map_of (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)) x = Some (transform 0 e)"
    by (simp add: map_of_map_transform)
  with `\<not> isLam e`
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow> conf_transform (ae, 0) (delete x \<Gamma>, e, Upd x # S)"
    by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (lamvar \<Gamma> x e S)
  from lamvar have [simp]: "x \<in> domA \<Gamma>" by auto (metis domI dom_map_of_conv_domA)
  from lamvar have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by (auto simp add: join_below_iff)
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto

  from Abinds_reorder1[OF `map_of \<Gamma> x = Some e`] `ae x = up\<cdot>u`
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by auto
  also have "\<dots> \<sqsubseteq> ae" using lamvar by (auto simp add: join_below_iff)
  finally have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae".

  have "consistent (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    using lamvar `ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u \<sqsubseteq> ae`  `ae x = up\<cdot>u` 
    by (auto simp add: join_below_iff thunks_Cons split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`] intro!: const_onI)
  moreover

  have "Astack S \<sqsubseteq> u" using lamvar  below_trans[OF _ `a \<sqsubseteq> u`] by auto

  {
  from `isLam e`
  have "isLam (transform u e)" by simp
  hence "isLam (Aeta_expand u (transform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u`  `isLam (transform u e)`
  have "map_of (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)) x = Some (Aeta_expand u (transform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
        ((x, Aeta_expand u (transform u e)) # delete x (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)), Aeta_expand u  (transform u e), S)"
     by (auto intro: lambda_var simp add: map_transform_delete simp del: restr_delete)
  also have "\<dots> = ((map_transform Aeta_expand ae (map_transform transform ae ((x,e) # delete x \<Gamma>))), Aeta_expand u (transform u e), S)"
    using `ae x = up \<cdot> u` `isLam (transform u e)`
    by (simp add: map_transform_Cons map_transform_delete restr_delete_twist del: restr_delete)
  also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* conf_transform (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    by simp (rule Aeta_expand_correct[OF `Astack S \<sqsubseteq> u`])
  finally(rtranclp_trans)
  have "conf_transform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* conf_transform (ae, u) ((x, e) # delete x \<Gamma>, e, S)".
  }
  ultimately show ?case by (blast del: consistentI consistentE)
next
case (var\<^sub>2 \<Gamma> x e S)

  have "ae x = up\<cdot>a" using var\<^sub>2 by auto

  have "Astack (Upd x # S) \<sqsubseteq> a" using var\<^sub>2 by auto
  hence "a = 0" by auto

  have "consistent (ae, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>2
    by (auto simp add: join_below_iff thunks_Cons split:if_splits)
  moreover
  have "conf_transform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> conf_transform (ae, 0) ((x, e) # \<Gamma>, e, S)"
    using `ae x = up\<cdot>a` `a = 0` var\<^sub>2
    by (auto intro!: step.intros simp add: map_transform_Cons)
  ultimately show ?case by (blast del: consistentI consistentE)
next
  case (let\<^sub>1 \<Delta> \<Gamma> e S)

  let ?ae = "Aheap \<Delta> e\<cdot>a"
  let ?new = "(domA (\<Delta> @ \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S))"
  have new: "?new = domA \<Delta>"
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (auto dest: set_mp[OF ups_fv_subset])

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
  have "const_on (?ae \<squnion> ae) (thunks \<Gamma>) (up\<cdot>0)" using let\<^sub>1 by fastforce
  moreover
  { fix x e'
    assume "x \<in> thunks \<Delta>" 
    hence "x \<notin> domA \<Gamma>" and "x \<notin> upds S"
      using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
      by (auto dest!: set_mp[OF thunks_domA] set_mp[OF ups_fv_subset])
    hence "(?ae \<squnion> ae) x = up \<cdot> 0" using `x \<in> thunks \<Delta>` by (auto simp add: Aheap_heap3)
  }
  hence "const_on (?ae \<squnion> ae) (thunks \<Delta>) (up\<cdot>0)" by auto
  moreover
  have "const_on ae (ap S) (up\<cdot>0)" using let\<^sub>1 by auto  
  hence "const_on (?ae \<squnion> ae) (ap S) (up\<cdot>0)" by fastforce
  moreover
  have "const_on ae (upds S) (up\<cdot>0)" using let\<^sub>1 by auto
  hence "const_on (?ae \<squnion> ae) (upds S) (up\<cdot>0)"  by fastforce
  moreover
  have "Astack S \<sqsubseteq> a" unfolding restr_stack_simp using let\<^sub>1 by auto
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
    by (simp add: Abinds_append_disjoint[OF fresh_distinct[OF let\<^sub>1(1)]])
  also have "\<dots> \<sqsubseteq> (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a) \<squnion> ABinds \<Gamma>\<cdot>ae" by (rule join_mono[OF Aexp_Let below_refl])
  also have "\<dots> = Aheap \<Delta> e\<cdot>a \<squnion> (Aexp (Let \<Delta> e)\<cdot>a \<squnion> ABinds \<Gamma>\<cdot>ae)" by simp
  also have "Aexp (Let \<Delta> e)\<cdot>a \<squnion> ABinds \<Gamma>\<cdot>ae \<sqsubseteq> ae" using let\<^sub>1 by auto
  finally
  have "ABinds (\<Delta> @ \<Gamma>) \<cdot> (Aheap \<Delta> e\<cdot>a \<squnion> ae) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> ae"  by this simp
  }
  ultimately
  have "consistent (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S) " by auto
  }
  moreover
  {
    have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ae"
      using fresh_distinct[OF let\<^sub>1(1)]
      by (auto dest!: set_mp[OF edom_Aheap])
    hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Gamma>)
       = map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)"
       by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
    moreover

    from let\<^sub>1 have *: "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
    have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
       using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
       by (auto dest!: set_mp[OF *] set_mp[OF ups_fv_subset])
    hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Delta>)
       = map_transform Aeta_expand ?ae (map_transform transform ?ae \<Delta>)"
       by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
    ultimately

    have "conf_transform (ae, a) (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> conf_transform (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S)"
      using  let\<^sub>1(1,2)
      by (fastforce intro!: step.intros simp add: map_transform_append  dest: set_mp[OF edom_Aheap])
  }
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
  case refl thus ?case by auto
next
  case (trans c c' c'')
    from trans(3)[OF trans(5)]
    obtain ae' a' where "consistent (ae', a') c'" and *: "conf_transform (ae, a) c \<Rightarrow>\<^sup>* conf_transform (ae', a') c'" by blast
    from trans(4)[OF this(1)]
    obtain ae'' a'' where "consistent (ae'', a'') c''" and **: "conf_transform (ae', a') c' \<Rightarrow>\<^sup>* conf_transform (ae'', a'') c''" by blast
    from this(1) rtranclp_trans[OF * **]
    show ?case by blast
qed

end

end
