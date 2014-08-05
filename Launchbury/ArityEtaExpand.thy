theory ArityEtaExpand
imports ArityCorrectSestoft EtaExpansion
begin

locale ArityEtaExpand = CorrectArityAnalysisAheap +
  fixes Aeta_expand_transform :: "Arity \<Rightarrow> exp \<Rightarrow> exp"
begin

  definition Aeta_expand :: "Arity \<Rightarrow> exp \<Rightarrow> exp" 
    where "Aeta_expand a e = eta_expand (Rep_Arity a) e"
  lemma Aeta_expand_0[simp]: "Aeta_expand 0 e = e"
    unfolding Aeta_expand_def by (metis eta_expand.simps(1) zero_Arity.rep_eq)

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
    show ?thesis unfolding Aeta_expand_def by (rule eta_expansion_correct')
  qed

  lemma isLam_Aeta_expand: "isLam e \<Longrightarrow> isLam (Aeta_expand a e)"
    unfolding Aeta_expand_def by (rule isLam_eta_expand)

  fun Aeta_expand' :: "Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp" 
  where "Aeta_expand' (Iup a) e = Aeta_expand a e"
   |    "Aeta_expand' Ibottom e = e"

  lemma [simp]: "Aeta_expand' (up\<cdot>a) e = Aeta_expand a e" unfolding up_def by (simp add: cont_Iup)

  fun Aeta_expand_transform' :: "Arity\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp" 
  where "Aeta_expand_transform' (Iup a) e = Aeta_expand_transform a e"
   |    "Aeta_expand_transform' Ibottom e = e"

  lemma [simp]: "Aeta_expand_transform' (up\<cdot>a) e = Aeta_expand_transform a e" unfolding up_def by (simp add: cont_Iup)

  fun Atransform :: "(AEnv \<times> Arity) \<Rightarrow> conf \<Rightarrow> conf"
  where "Atransform (ae, a) (\<Gamma>, e, S) =
    (map_ran (\<lambda> x e. Aeta_expand' (ae x) (Aeta_expand_transform' (ae x) e)) \<Gamma>, 
     Aeta_expand_transform a e,
     S)"

  inductive consistent  where
    [intro!]: "AE_consistent ae (\<Gamma>, e, S) \<Longrightarrow> Astack ae S \<sqsubseteq> a \<Longrightarrow> consistent (ae, a) (\<Gamma>, e, S)"
  declare consistent.cases[elim!]

  lemma [simp]:
    "Aeta_expand_transform a (App e x) = App (Aeta_expand_transform (inc\<cdot>a) e) x"
    "Aeta_expand_transform a (Lam [x]. e) = Lam [x].(Aeta_expand_transform (pred\<cdot>a) e)"
    "Aeta_expand_transform a (e[x ::= z]) = (Aeta_expand_transform a e)[x ::= z]"
    "Aeta_expand_transform a (Var x) = Var x"
    "isLam (Aeta_expand_transform a e) \<longleftrightarrow> isLam e"
    sorry

  sublocale AbstractConforms step consistent.

lemma foo:
  fixes c c' R 
  assumes "c \<Rightarrow> c'" and "consistent (ae,a) c"
  shows "\<exists>ae' a'. consistent (ae',a') c' \<and> Atransform (ae,a) c \<Rightarrow>\<^sup>* Atransform (ae',a') c'"
using assms
proof(induction)
case (app\<^sub>1 \<Gamma> e x S)
  from app\<^sub>1 have "AE_consistent ae (\<Gamma>, e, Arg x # S)"  by (fastforce intro!: AE_consistentI simp add: Aexp_App join_below_iff)
  moreover
  have "Astack ae (Arg x # S) \<sqsubseteq> inc\<cdot>a" using app\<^sub>1 by (auto intro: monofun_cfun_arg)
  ultimately
  have "consistent (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)" ..
  moreover
  have "Atransform (ae, a) (\<Gamma>, App e x, S) \<Rightarrow> Atransform (ae, inc\<cdot>a) (\<Gamma>, e, Arg x # S)" by simp rule
  ultimately
  show ?case by blast
next
case (app\<^sub>2 \<Gamma> y e x S)
  hence "AE_consistent ae (\<Gamma>, e[y::=x], S)" 
    by (fastforce intro!: AE_consistentI  below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]] simp add: Aexp_App join_below_iff)
  moreover
  have "Astack ae S \<sqsubseteq> pred\<cdot>a" using app\<^sub>2 by (auto, metis monofun_cfun_arg pred_inc)
  ultimately
  have "consistent (ae, pred\<cdot>a) (\<Gamma>, e[y ::= x], S)" ..
  moreover
  have "Atransform (ae, a) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> Atransform (ae, pred \<cdot> a) (\<Gamma>, e[y::=x], S)" by simp rule
  ultimately
  show ?case by blast
next
case (var\<^sub>1 \<Gamma> x e S)
  from var\<^sub>1 have "Aexp (Var x)\<cdot>(Astack ae S) \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto
  moreover
  hence "x \<in> edom ae" unfolding edom_def by auto
  ultimately
  have "AE_consistent ae (delete x \<Gamma>, e, Upd x # S)" using var\<^sub>1 by (fastforce intro!: AE_consistentI  simp add: join_below_iff)
  moreover
  have "Astack ae (Upd x # S) \<sqsubseteq> 0" by simp
  ultimately
  have "consistent (ae, 0) (delete x \<Gamma>, e, Upd x # S)" by blast
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
  show ?case by blast
next 
case (var\<^sub>2 \<Gamma> x e S)
  from var\<^sub>2 have "ae ` upds S \<subseteq> {up \<cdot> 0}" by fastforce

  from var\<^sub>2 have "Aexp (Var x)\<cdot>(Astack ae S) \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto

  from this(2)
  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> Aexp e\<cdot>u" by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> u` var\<^sub>2 by fastforce
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ae" by this simp
  hence "AE_consistent ae ((x, e) # delete x \<Gamma>, e, S)"
    using var\<^sub>2 by(fastforce intro!: AE_consistentI  simp add: join_below_iff split:if_splits)
  moreover
  have "Astack ae S \<sqsubseteq> u" by fact
  ultimately
  have "consistent (ae, u) ((x, e) # delete x \<Gamma>, e, S)" by auto
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
    using `ae x = up \<cdot> u` by simp (rule Aeta_expand_correct[OF `ae \` upds S \<subseteq> {up \<cdot> 0}` `Astack ae S \<sqsubseteq> u`])
  finally
  have "Atransform (ae, a) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* Atransform (ae, u) ((x, e) # delete x \<Gamma>, e, S)".
  }
  ultimately show ?case by blast
next
case (var\<^sub>3 x \<Gamma> e S)
  hence "ae x = up\<cdot>0" by auto

  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x" using var\<^sub>3 by (auto simp add: join_below_iff)
  then obtain u where "ae x = up \<cdot> u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto

  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> Aexp e\<cdot>0" by (rule monofun_cfun_arg) simp
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> 0` var\<^sub>3 by auto
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ae" by this simp
  hence "AE_consistent ae ((x, e) # \<Gamma>, e, S)" using var\<^sub>3 `ae x = up \<cdot> 0`
    by (fastforce intro!: AE_consistentI  simp add: join_below_iff split:if_splits)+
  moreover
  have "Astack ae (Upd x # S) \<sqsubseteq> a" using var\<^sub>3 by auto
  with `ae x = up \<cdot> 0`
  have "a = 0" by auto
  
  have "Astack ae S \<sqsubseteq> 0" by simp
  ultimately
  have "consistent (ae, 0) ((x, e) # \<Gamma>, e, S)" by auto
  moreover
  have "Atransform (ae, a) (\<Gamma>, e, Upd x # S) \<Rightarrow> Atransform (ae, 0) ((x, e) # \<Gamma>, e, S)"
    using `ae x = up\<cdot>0` `a = 0` var\<^sub>3 by (fastforce intro!: step.intros)
  ultimately show ?case by blast
next
  case (let\<^sub>1 \<Delta> \<Gamma> S e)

  show ?case sorry
qed


  sublocale AbstractTransform step consistent Atransform
    apply default
    using foo
    apply blast
    done

end
end

