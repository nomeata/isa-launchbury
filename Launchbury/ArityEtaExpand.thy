theory ArityEtaExpand
imports ArityCorrectSestoft EtaExpansion
begin

locale ArityEtaExpand = CorrectArityAnalysisAheap +
  fixes Aeta_expand_transform :: "Arity \<Rightarrow> exp \<Rightarrow> exp"
begin
  lift_definition Aeta_expand :: "Arity \<Rightarrow> exp \<Rightarrow> exp"  is "\<lambda> a e. eta_expand a e".

  lemma Aeta_expand_0[simp]: "Aeta_expand 0 e = e"
    by transfer simp

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

  fun Aeta_expand' :: "Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp" 
  where "Aeta_expand' (Iup a) e = Aeta_expand a e"
   |    "Aeta_expand' Ibottom e = e"

  lemma [simp]: "Aeta_expand' (up\<cdot>a) e = Aeta_expand a e" unfolding up_def by (simp add: cont_Iup)
  lemma Aeta_expand'_fresh[simp]: "a \<sharp> Aeta_expand' n e = a \<sharp> e" by (cases "(n, e)" rule: Aeta_expand'.cases) auto
  lemma Aeta_expand'_fresh_star[simp]: "a \<sharp>* Aeta_expand' n e = a \<sharp>* e" by (auto simp add: fresh_star_def)

  fun Aeta_expand_transform' :: "Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp" 
  where "Aeta_expand_transform' (Iup a) e = Aeta_expand_transform a e"
   |    "Aeta_expand_transform' Ibottom e = e"

  lemma [simp]: "Aeta_expand_transform' (up\<cdot>a) e = Aeta_expand_transform a e" unfolding up_def by (simp add: cont_Iup)

  fun Atransform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "Atransform (ae, a) (\<Gamma>, e, S) =
    (map_ran (\<lambda> x e. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) e)) \<Gamma>, 
     Aeta_expand_transform a e,
     S)"

  (*
  inductive consistent  where
    [intro!]: "AE_consistent ae (\<Gamma>, e, S) \<Longrightarrow> Astack ae S \<sqsubseteq> a \<Longrightarrow> Aexp e \<cdot> a \<sqsubseteq> ae \<Longrightarrow> consistent (ae, a) (\<Gamma>, e, S)"
  declare consistent.cases[elim!]
  *)
  
  inductive consistent :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "edom ae \<subseteq> domA \<Gamma> \<union> upds S
    \<Longrightarrow> upds S \<subseteq> edom ae
    \<Longrightarrow> Astack ae S \<sqsubseteq> a
    \<Longrightarrow> AEstack ae S \<sqsubseteq> ae 
    \<Longrightarrow> Aexp e \<cdot> a \<sqsubseteq> ae
    \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> Aexp' e \<cdot> (ae x) \<sqsubseteq> ae)
    \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ae x = up\<cdot>0)
    \<Longrightarrow> ae ` upds S \<subseteq> {up\<cdot>0}
    \<Longrightarrow> consistent (ae, a) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, a) (\<Gamma>, e, S)"


  lemma [simp]:
    "Aeta_expand_transform a (App e x) = App (Aeta_expand_transform (inc\<cdot>a) e) x"
    "Aeta_expand_transform a (Lam [x]. e) = Lam [x].(Aeta_expand_transform (pred\<cdot>a) e)"
    "Aeta_expand_transform a (Var x) = Var x"
    "Aeta_expand_transform a (Terms.Let \<Delta> e) = Terms.Let (map_ran (\<lambda>x ea. Aeta_expand' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x) (Aeta_expand_transform' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x) ea)) \<Delta>) (Aeta_expand_transform a e)"
    "isLam (Aeta_expand_transform a e) \<longleftrightarrow> isLam e"
    "Aeta_expand_transform a (e[x ::= z]) = (Aeta_expand_transform a e)[x ::= z]"
    "at \<sharp> Aeta_expand_transform a e \<longleftrightarrow> at \<sharp> e"
    sorry

  lemma Aeta_expand_transform'_fresh[simp]: "a \<sharp> Aeta_expand_transform' n e = a \<sharp> e" by (cases "(n, e)" rule: Aeta_expand_transform'.cases) auto
  lemma Aeta_expand_transform'_fresh_star[simp]: "a \<sharp>* Aeta_expand_transform' n e = a \<sharp>* e" by (auto simp add: fresh_star_def)

  sublocale AbstractConforms step consistent.

lemma foo:
  fixes c c' R 
  assumes "c \<Rightarrow> c'" and "consistent (ae,a) c"
  shows "\<exists>ae' a'. consistent (ae',a') c' \<and> Atransform (ae,a) c \<Rightarrow>\<^sup>* Atransform (ae',a') c'"
using assms
proof(induction)
case (app\<^sub>1 \<Gamma> e x S)
  from app\<^sub>1 have "consistent (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)"  by (fastforce simp add: Aexp_App join_below_iff)
  moreover
  have "Atransform (ae, a) (\<Gamma>, App e x, S) \<Rightarrow> Atransform (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)" by simp rule
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (app\<^sub>2 \<Gamma> y e x S)
  have "Aexp (e[y ::= x])\<cdot>(pred\<cdot>a) \<sqsubseteq> ae" using app\<^sub>2
    apply (auto simp add: Aexp_Lam join_below_iff)
    apply (rule below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]])
    apply (auto simp add: Aexp_App join_below_iff)
    apply (cases a rule: Arity_exhaust)
    apply (auto simp add: Aexp_Lam join_below_iff)
    done
  hence "consistent (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)"  using app\<^sub>2
    apply  (auto intro!:  below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]] simp add: Aexp_App join_below_iff monofun_cfun_arg)
    by (metis image_eqI singletonD subsetCE)
  moreover
  have "Atransform (ae, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> Atransform (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by simp rule
  ultimately
  show ?case by (blast del: consistentI consistentE)
next
case (var\<^sub>1 \<Gamma> x e S)
  (*
  from var\<^sub>1 have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto
  moreover
  hence "x \<in> edom ae" unfolding edom_def by auto
  *)
  have "consistent (ae, 0) (delete x \<Gamma>, e, Upd x # S)" using var\<^sub>1 by (fastforce  simp add: join_below_iff)
  moreover
  {
  from var\<^sub>1 have "ae x = up\<cdot>0" by auto
  with  `map_of \<Gamma> x = Some e`
  have "map_of (map_ran (\<lambda>x e. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) e)) \<Gamma>) x = Some (Aeta_expand_transform 0 e)"
    by (simp add: map_ran_conv)
  with `\<not> isLam e`
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow> Atransform (ae, 0) (delete x \<Gamma>, e, Upd x # S)"
    by (auto simp add: map_ran_delete intro!: step.intros)
  }
  ultimately
  show ?case by (blast del: consistentI consistentE)
next 
case (var\<^sub>2 \<Gamma> x e S)
  from var\<^sub>2 have "ae ` upds S \<subseteq> {up \<cdot> 0}" by fastforce

  from var\<^sub>2 have "Aexp (Var x)\<cdot>a \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>a \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "a \<sqsubseteq> u" by (cases "ae x") auto

  from this(2)
  have "Aexp e\<cdot>a \<sqsubseteq> Aexp e\<cdot>u" by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> u` var\<^sub>2 by fastforce
  finally have "Aexp e\<cdot>a \<sqsubseteq> ae" by this simp
  moreover
  have "Aexp' e\<cdot>(ae x) \<sqsubseteq> ae" using var\<^sub>2 by auto
  hence "Aexp e\<cdot>u \<sqsubseteq> ae" using `ae x = up\<cdot>u` by simp
  ultimately
  have "consistent (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    using var\<^sub>2 by (auto  simp add: join_below_iff split:if_splits intro: below_trans[OF _ `a \<sqsubseteq> u`])
  moreover
  {
  from `isLam e`
  have "isLam (Aeta_expand_transform u e)" by simp
  hence "isLam (Aeta_expand u (Aeta_expand_transform u e))" by (rule isLam_Aeta_expand)
  moreover
  from  `map_of \<Gamma> x = Some e`  `ae x = up \<cdot> u`
  have "map_of (map_ran (\<lambda>x e. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) e)) \<Gamma>) x 
    = Some (Aeta_expand u (Aeta_expand_transform u e))"
    by (simp add: map_ran_conv)
  ultimately
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>
        ((x, Aeta_expand u (Aeta_expand_transform u e)) # map_ran (\<lambda>x e. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) e)) (delete x \<Gamma>), Aeta_expand u  (Aeta_expand_transform u e), S)"
    using `ae x = up \<cdot> u` by (auto intro: step.intros simp add: map_ran_delete)
  also
  have "\<dots> \<Rightarrow>\<^sup>* Atransform (ae, u) ((x, e) # delete x \<Gamma>, e, S)"
    using `ae x = up \<cdot> u`
    apply simp
    apply (rule Aeta_expand_correct[OF `ae \` upds S \<subseteq> {up \<cdot> 0}` below_trans[OF _ `a \<sqsubseteq> u`]])
    using var\<^sub>2 by auto
  finally
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* Atransform (ae, u) ((x, e) # delete x \<Gamma>, e, S)".
  }
  ultimately show ?case by (blast del: consistentI consistentE)
next
case (var\<^sub>3 x \<Gamma> e S)
  hence "ae x = up\<cdot>0" by auto

  have "Astack ae (Upd x # S) \<sqsubseteq> a" using var\<^sub>3 by auto
  with `ae x = up \<cdot> 0`
  have "a = 0" by auto

  have "consistent (ae, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>3 
    by (fastforce  simp add: join_below_iff split:if_splits)
  moreover
  have "Atransform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> Atransform (ae, 0) ((x, e) # \<Gamma>, e, S)"
    using `ae x = up\<cdot>0` `a = 0` var\<^sub>3 by (fastforce intro!: step.intros)
  ultimately show ?case by (blast del: consistentI consistentE)
next
  case (let\<^sub>1 \<Delta> \<Gamma> S e)

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
  moreover
  have "AEstack ae S \<sqsubseteq> ae" using let\<^sub>1(3) by auto
  hence "AEstack ae S \<sqsubseteq> ?ae \<squnion> ae" by (metis join_above1 below_refl box_below join_comm)
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
    have "\<And> x. x \<in> set \<Gamma> \<Longrightarrow> fst x \<notin> edom (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a))"
      using fresh_distinct[OF let\<^sub>1(1)]
      by (auto dest!: set_mp[OF edom_Aheap] domA_from_set)
    hence "map_ran (\<lambda>x ea. Aeta_expand' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x \<squnion> ae x) (Aeta_expand_transform' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x \<squnion> ae x) ea)) \<Gamma>
       = map_ran (\<lambda>x ea. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) ea)) \<Gamma>"
      by (auto intro: map_ran_cong[OF _ refl] simp add: edomIff)
    moreover
    from let\<^sub>1 have *: "edom ae \<subseteq> domA \<Gamma> \<union> upds S" by auto
    have "\<And> x. x \<in> set \<Delta> \<Longrightarrow> fst x \<notin> edom ae"
       using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
       by (auto dest!: set_mp[OF *] set_mp[OF ups_fv_subset] domA_from_set)
    hence "map_ran (\<lambda>x ea. Aeta_expand' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x \<squnion> ae x) (Aeta_expand_transform' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x \<squnion> ae x) ea)) \<Delta>
       = map_ran (\<lambda>x ea. Aeta_expand' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x) (Aeta_expand_transform' ((Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) x) ea)) \<Delta>"
      by (auto intro: map_ran_cong[OF _ refl]  simp add: edomIff)
    ultimately
    have "Atransform (ae, a) (\<Gamma>, Terms.Let \<Delta> e, S) \<Rightarrow> Atransform (?ae \<squnion> ae, a) (\<Delta> @ \<Gamma>, e, S)"
      apply (simp add: map_ran_append)
      apply rule
      using let\<^sub>1(1,2)
      apply auto
      apply (induction \<Gamma>)
      apply simp
      apply (auto simp add: fresh_star_Pair fresh_star_Cons)
      done
  }
  ultimately
  show ?case  by (blast del: consistentI consistentE)
qed


  sublocale AbstractTransform step consistent Atransform
    apply default
    using foo
    apply (auto del: consistentI consistentE)
    done

end
end

