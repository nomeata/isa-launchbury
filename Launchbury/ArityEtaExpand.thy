theory ArityEtaExpand
imports ArityCorrectSestoft EtaExpansion
begin

fun lift_transform :: "(Arity \<Rightarrow> exp \<Rightarrow> exp) \<Rightarrow> (Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp)"
  where "lift_transform t Ibottom  e = e"
  |     "lift_transform t (Iup a) e = t a e"

lemma lift_transform_up[simp]: "lift_transform t (up\<cdot>a) e = t a e"
  unfolding up_def by (simp add: cont_Iup)

definition map_transform :: "(Arity \<Rightarrow> exp \<Rightarrow> exp) \<Rightarrow> AEnv \<Rightarrow> heap \<Rightarrow> heap"
  where "map_transform t ae = map_ran (\<lambda> x e . lift_transform t (ae x) e)"

lemma domA_map_transform[simp]: "domA (map_transform t ae \<Gamma>) = domA \<Gamma>"
  unfolding map_transform_def by simp

lemma map_transform_delete:
  "map_transform t ae (delete x \<Gamma>) = delete x (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by (simp add: map_ran_delete)

lemma map_transform_Cons:
  "map_transform t ae ((x,e)# \<Gamma>) = (x, lift_transform t (ae x) e) #  (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by simp

lemma map_transform_append:
  "map_transform t ae (\<Delta>@\<Gamma>) = map_transform t ae \<Delta> @ map_transform t ae \<Gamma>"
  unfolding map_transform_def by (simp add: map_ran_append)

lemma map_transform_cong:
  "(\<And>x. x \<in> domA m1 \<Longrightarrow> ae x = ae' x) \<Longrightarrow> m1 = m2 \<Longrightarrow> map_transform t ae m1 = map_transform t ae' m2"
  unfolding map_transform_def by (auto intro!: map_ran_cong dest: domA_from_set)

lemma map_of_map_transform: "map_of (map_transform t ae \<Gamma>) x = map_option (lift_transform t (ae x)) (map_of \<Gamma> x)"
  unfolding map_transform_def by (simp add: map_ran_conv)

locale supp_bounded_transform = 
  fixes trans :: "Arity \<Rightarrow> exp \<Rightarrow> exp"
  assumes supp_trans: "supp (trans a e) \<subseteq> supp e"
begin
  lemma supp_lift_transform: "supp (lift_transform trans a e) \<subseteq> supp e"
    by (cases "(trans, a, e)" rule:lift_transform.cases) (auto dest!: set_mp[OF supp_trans])

  lemma supp_map_transform: "supp (map_transform trans ae \<Gamma>) \<subseteq> supp \<Gamma>"
  unfolding map_transform_def
     by (induction \<Gamma>) (auto simp add: supp_Pair supp_Cons dest!: set_mp[OF supp_lift_transform])

  lemma fresh_map_transform[intro]: "a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> map_transform trans ae \<Gamma>"
    unfolding fresh_def using supp_map_transform by auto

  lemma fresh_star_map_transform[intro]: "a \<sharp>* \<Gamma> \<Longrightarrow> a \<sharp>* map_transform trans ae \<Gamma>"
    by (auto simp add: fresh_star_def)
end

locale Has_Aeta_expand_transform = 
  fixes Aeta_expand_transform :: "Arity \<Rightarrow> exp \<Rightarrow> exp"
begin

(*
  fun Aeta_expand_transform' :: "Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp" 
  where "Aeta_expand_transform' (Iup a) e = Aeta_expand_transform a e"
   |    "Aeta_expand_transform' Ibottom e = e"

  lemma [simp]: "Aeta_expand_transform' (up\<cdot>a) e = Aeta_expand_transform a e" unfolding up_def by (simp add: cont_Iup)
*)

end


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

interpretation supp_bounded_transform Aeta_expand
  apply default
  using Aeta_expand_fresh
  apply (auto simp add: fresh_def)
  done

locale ArityEtaExpand = CorrectArityAnalysisAheap + Has_Aeta_expand_transform
begin

  fun Atransform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "Atransform (ae, a) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>), 
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


  lemma foobar[simp]:
    "Aeta_expand_transform a (App e x) = App (Aeta_expand_transform (inc\<cdot>a) e) x"
    "Aeta_expand_transform a (Lam [x]. e) = Lam [x].(Aeta_expand_transform (pred\<cdot>a) e)"
    "Aeta_expand_transform a (Var x) = Var x"
    "Aeta_expand_transform a (Terms.Let \<Delta> e) = Terms.Let (map_transform Aeta_expand (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) (map_transform Aeta_expand_transform (Aheap \<Delta>\<cdot>(Aexp e\<cdot>a)) \<Gamma>)) (Aeta_expand_transform a e)"
    "Aeta_expand_transform a (e[x ::= z]) = (Aeta_expand_transform a e)[x ::= z]"
    "at \<sharp> Aeta_expand_transform a e \<longleftrightarrow> at \<sharp> e"
    sorry

  interpretation supp_bounded_transform Aeta_expand_transform
    apply default
    using foobar(6)
    apply (auto simp add: fresh_def)
    done
  
  lemma isLam_Aeta_expand_transform[simp]:
    "isLam (Aeta_expand_transform a e) \<longleftrightarrow> isLam e"
    apply (induction e rule:isLam.induct)
    apply (auto simp add: foobar(4)[where a = a])
    apply (subst (asm) foobar) (* WTF *)
    apply simp
    done

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
    apply (auto simp add:  join_below_iff)
    apply (rule below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]])
    apply (auto simp add: Aexp_App Aexp_Lam join_below_iff)
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
  have "map_of (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>)) x = Some (Aeta_expand_transform 0 e)"
    by (simp add: map_of_map_transform)
  with `\<not> isLam e`
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow> Atransform (ae, 0) (delete x \<Gamma>, e, Upd x # S)"
    by (auto simp add: map_transform_delete intro!: step.intros)
  }
  ultimately
  show ?case by (blast del: consistentI consistentE)
next 
case (var\<^sub>2 \<Gamma> x e S)
  from var\<^sub>2 have "ae ` upds S \<subseteq> {up \<cdot> 0}" by fastforce
  from var\<^sub>2 have "Astack ae S \<sqsubseteq> a" by auto

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
  have "map_of (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae \<Gamma>)) x = Some (Aeta_expand u (Aeta_expand_transform u e))"
    by (simp add: map_of_map_transform)
  ultimately
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>
        ((x, Aeta_expand u (Aeta_expand_transform u e)) # (map_transform Aeta_expand ae (map_transform Aeta_expand_transform ae (delete x \<Gamma>))), Aeta_expand u  (Aeta_expand_transform u e), S)"
     by (auto intro: step.intros simp add: map_transform_delete)
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
case (var\<^sub>3 x \<Gamma> e S)
  hence "ae x = up\<cdot>0" by auto

  have "Astack ae (Upd x # S) \<sqsubseteq> a" using var\<^sub>3 by auto
  with `ae x = up \<cdot> 0`
  have "a = 0" by auto

  have "consistent (ae, 0) ((x, e) # \<Gamma>, e, S)" using var\<^sub>3 
    by (fastforce  simp add: join_below_iff split:if_splits)
  moreover
  have "Atransform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> Atransform (ae, 0) ((x, e) # \<Gamma>, e, S)"
    using `ae x = up\<cdot>0` `a = 0` var\<^sub>3 by (auto intro!: step.intros simp add: map_transform_Cons)
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
      apply (subst foobar(4))
      apply rule
      using let\<^sub>1(1,2)
      by auto
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

