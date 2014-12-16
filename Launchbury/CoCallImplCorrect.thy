theory CoCallImplCorrect
imports CoCallAnalysisImpl  CoCallCardinality 
begin

interpretation ArityAnalysis Aexp.

lemma Aexp_edom': "edom (Aexp e\<cdot>a) \<subseteq> fv e"
  by (nominal_induct arbitrary: a rule: exp_strong_induct) auto

interpretation EdomArityAnalysis Aexp by default (rule Aexp_edom')

lemma edom_Afix: "edom (Afix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp  e\<cdot>a)) \<subseteq> fv \<Gamma> \<union> fv e"
proof-
  {
  fix x  :: var
  assume "x \<notin> fv \<Gamma>" 
  hence [simp]: "\<And> a. (ABinds  \<Gamma>\<cdot>a) x = \<bottom>"
    apply (induction \<Gamma> rule: ABinds.induct)
    apply auto
    apply (auto simp add: Aexp'_def )
    apply (case_tac "a v")
    apply simp
    apply auto
    apply (metis (mono_tags) Aexp_edom' contra_subsetD edom_def mem_Collect_eq)
    apply (metis contra_subsetD fv_delete_subset)
    done
  
  from `x \<notin> fv \<Gamma>`
  have "x \<notin> domA \<Gamma>" by (metis domA_fv_subset set_mp)
  hence [simp]: "x \<notin> thunks \<Gamma>" by (metis set_mp thunks_domA)
  
  assume "x \<notin> fv e"
  hence "x \<notin> edom (Aexp e\<cdot>a)"  by (auto dest!: set_mp[OF Aexp_edom'])
  hence [simp]: "(Aexp e\<cdot>a) x = \<bottom>" by (simp add: edom_def)

  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp  e\<cdot>a)) x = \<bottom>"
    unfolding Afix_def cccFix_eq
    apply simp
    apply (rule fix_ind)  
    apply auto
    done
  }
  thus ?thesis by (auto simp add: edom_def)    
qed

lemma ccNeighbors_ccField:
  "ccNeighbors S G \<subseteq> ccField G" by transfer (auto simp add: Field_def)
    
lemma ccField_CCfix: "ccField (CCfix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp  e\<cdot>a)) \<subseteq> fv \<Gamma> \<union> fv e"
  unfolding CCfix_def cccFix_eq
  apply simp
  apply (rule fix_ind)
  apply (auto simp add: ccBindsExtra_simp ccBinds_eq ccField_cc_restr
             dest: set_mp[OF ccField_CCexp]
             dest!:set_mp[OF ccNeighbors_ccField]
             dest: set_mp[OF map_of_Some_fv_subset]
             dest!: set_mp[OF ccField_cc_restr]
              simp add: ccField_ccProd split: if_splits)
  done

lemma Aexp_lam_simp[simp]: "Aexp (Lam [x]. e) \<cdot> n = env_delete x (Aexp e \<cdot> (pred \<cdot> n))"
proof-
  have "Aexp (Lam [x]. e) \<cdot> n = Aexp e\<cdot>(pred\<cdot>n) f|` (fv e - {x})" by simp
  also have "... = env_delete x (Aexp e\<cdot>(pred\<cdot>n)) f|` (fv e - {x})" by simp
  also have "\<dots> = env_delete x (Aexp e\<cdot>(pred\<cdot>n))"
     by (rule env_restr_useless) (auto dest: set_mp[OF Aexp_edom])
  finally show ?thesis.
qed
declare Aexp_simps(2)[simp del]

(*
lemma Aexp_let_simp[simp]: "Aexp (Terms.Let \<Gamma> e) \<cdot> n = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)"
proof-
  have "Aexp (Let \<Gamma> e) \<cdot> n  = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by simp
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by auto (metis Diff_eq Diff_idemp)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)"
     by (rule env_restr_useless)
        (auto dest!: set_mp[OF Aexp_edom] set_mp[OF Afix_edom] set_mp[OF edom_thunks_AE])
  finally show ?thesis.
qed
declare Aexp.simps(4)[simp del]
*)

lemma Aexp_subst_upd: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
proof (nominal_induct e avoiding: x y  arbitrary: n rule: exp_strong_induct)
  case (Var v) 
  thus ?case by auto
next
  case (App e v x y n)
  have "Aexp (App e v)[y::=x]\<cdot>n \<sqsubseteq> (Aexp e[y::=x]\<cdot>(inc\<cdot>n)) \<squnion> (AE_singleton (v[y::v=x])\<cdot>(up\<cdot>0))" by simp
  also have "Aexp e[y::=x]\<cdot>(inc\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0)" by (rule App.hyps)
  also have "(AE_singleton (v[y::v=x])\<cdot>(up\<cdot>0)) \<sqsubseteq> (AE_singleton v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "(Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0) \<squnion> (AE_singleton v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0) 
    = (Aexp (App e v)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by auto
  finally show ?case by this simp_all
next
  case (Lam v e)
  note Lam(1,2)[simp]
  have "Aexp (Lam [v]. e)[y::=x]\<cdot>n = env_delete v (Aexp e[y::=x]\<cdot>(pred\<cdot>n))" by simp
  also have "\<dots> \<sqsubseteq> env_delete v ((Aexp e\<cdot>(pred\<cdot>n))(y := \<bottom>, x := up\<cdot>0))"
    by (rule cont2monofunE[OF env_delete_cont Lam(3)])
  also have "\<dots> = (env_delete v (Aexp e\<cdot>(pred\<cdot>n)))(y := \<bottom>, x := up\<cdot>0)"
    using Lam(1,2) by (auto simp add: fresh_at_base)
  also have "\<dots> = (Aexp (Lam [v]. e)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by simp
  finally show ?case.
next
  case (Let \<Gamma> e)
   hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  
  note this[simp] Let(1,2)[simp]

  have "Aexp (Let \<Gamma> e)[y::=x]\<cdot>n \<sqsubseteq> Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>n, CCexp e[y::=x]\<cdot>n) f|` fv (Let (\<Gamma>[y::h=x]) (e[y::=x]))"
    by (simp add: fresh_star_Pair)
  also have "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by fact
  (*
  also have "thunks_AE \<Gamma>[y::h=x] \<sqsubseteq> (thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by (rule thunks_AE_subst_approx[OF `y \<notin> domA \<Gamma>`])
  also have "(Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0) \<squnion> (thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0) = (Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "Afix \<Gamma>[y::h=x]\<cdot>((Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>))(y := \<bottom>, x := up\<cdot>0)"
    by (rule Afix_subst_approx[OF Let(3) `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`])
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>))(y := \<bottom>, x := up\<cdot>0) f|` (- domA \<Gamma>) = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)) (y := \<bottom>, x := up\<cdot>0)" by auto
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)) = Aexp (Terms.Let \<Gamma> e)\<cdot>n" by simp
  finally
  show ?case by this simp_all
  *)
  show ?case sorry
qed

lemma Aexp_restr_subst:
  assumes "x \<notin> S" and "y \<notin> S"
  shows "(Aexp e[x::=y]\<cdot>a) f|` S = (Aexp e\<cdot>a) f|` S"
using assms
proof (nominal_induct e avoiding: x y  arbitrary: a  S rule: exp_strong_induct_set)
  case (Var v) 
  thus ?case by auto
next
  case (App e v)
  thus ?case by (auto simp add: env_restr_join simp del: fun_meet_simp)
next
  case (Lam v e)
  thus ?case
  by (auto simp add: env_restr_join env_delete_env_restr_swap[symmetric]  simp del: fun_meet_simp)
next
  case (Let \<Gamma> e)
  (*
  hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  
  note this[simp] Let(1,2)[simp]

  from Let
  have "Afix \<Gamma>[x::h=y]\<cdot>(Aexp e[x::=y]\<cdot>a \<squnion> thunks_AE \<Gamma>) f|` (S \<union> domA \<Gamma>) = Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>) f|` (S \<union> domA \<Gamma>)"
    apply (auto simp add: fresh_star_Pair)
    apply (subst Afix_restr_subst')
    apply auto[1]
    apply auto[3]
    apply (simp add: env_restr_join)
    apply (subst Afix_restr) back
    apply auto[1]
    apply (simp add: env_restr_join)
    done
  thus ?case using Let(1,2) by (auto simp add: fresh_star_Pair elim:env_restr_eq_subset[rotated])
  *)
  show ?case sorry
qed

interpretation CorrectArityAnalysis' Aexp
proof default
(*
  fix \<pi>
  show "\<pi> \<bullet> Aexp = Aexp" by perm_simp rule
next
*)
  fix x y :: var and e :: exp  and a 
  show "Aexp e[y::=x]\<cdot>a \<sqsubseteq> env_delete y (Aexp e\<cdot>a) \<squnion> AE_singleton x\<cdot>(up\<cdot>0)"
    apply (rule below_trans[OF Aexp_subst_upd])
    apply (rule fun_belowI)
    apply auto
    done
qed (simp_all add:Aexp_restr_subst)

definition Aheap where
  "Aheap \<Gamma> e = (\<Lambda> a. (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a, CCexp e\<cdot>a) f|` domA \<Gamma>))"

lemma Aheap_simp:
  "Aheap \<Gamma> e \<cdot> a= (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a, CCexp e\<cdot>a) f|` domA \<Gamma>)"
  unfolding Aheap_def by simp

lemma Aheap_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap \<Gamma> e) = Aheap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding Aheap_def
  apply perm_simp
  apply (subst Abs_cfun_eqvt)
  apply simp
  apply rule
  done

interpretation CorrectArityAnalysisLet' Aexp Aheap
proof default
  fix \<pi> show "\<pi> \<bullet> Aheap = Aheap"
    by perm_simp rule
next
  fix \<Gamma> e a
  show "edom (Aheap \<Gamma> e\<cdot>a) \<subseteq> domA \<Gamma>"
   unfolding Aheap_def by simp
next
  fix x y :: var and \<Gamma> :: heap and e :: exp
  assume assms: "x \<notin> domA \<Gamma>"  "y \<notin> domA \<Gamma>"
  show "Aheap \<Gamma>[x::h=y] e[x::=y] = Aheap \<Gamma> e"
    apply (rule cfun_eqI)
    unfolding Aheap_simp
    apply simp
    sorry
    (*
    apply (subst Afix_restr_subst[OF assms subset_refl])
    apply (subst Afix_restr[OF  subset_refl]) back
    apply (simp add: env_restr_join)
    apply (subst Aexp_restr_subst[OF assms])
    apply rule
    done
    *)
next
  fix \<Gamma> e a
  have "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)"
    apply (subst Afix_unroll)
    unfolding Aheap_simp
    by (simp add: below_trans[OF _ join_above1] below_trans[OF _ join_above2])
  also have "\<dots> = \<dots> f|` (fv \<Gamma> \<union> fv e)"
    by (rule env_restr_useless[symmetric, OF edom_Afix])
 also have "\<dots> = Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
    using domA_fv_subset
    by (auto simp add: Aheap_simp env_restr_join2 Un_absorb1[OF le_supI1[OF domA_fv_subset]])
  finally
  show "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a".
qed

definition calledOnce :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<Rightarrow> var set"
  where "calledOnce \<Gamma> e a = {v. v \<notin> ccManyCalls (CCexp e\<cdot>a) \<and> (\<forall> x e'. map_of \<Gamma> x = Some e' \<longrightarrow> v \<notin>  edom (fup\<cdot>(Aexp e')\<cdot>((Aheap \<Gamma> e\<cdot>a) x)))}"


definition ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  where "ccHeap \<Gamma> e  = (\<Lambda> a. CCfix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a))"

lemma ccHeap_eq:
  "ccHeap \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)"
unfolding ccHeap_def by simp

(*
definition isLinear :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<Rightarrow> bool"
  where "isLinear \<Gamma> e a = ccLinear (domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a)"
*)

interpretation CoCallCardinality CCexp calledOnce (* isLinear *) ccHeap Aexp Aheap
proof
  fix e a x
  show "CCexp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> CCexp (App e x)\<cdot>a"
    by simp
next
  fix y e n
  show "cc_restr (fv (Lam [y]. e)) (CCexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> CCexp (Lam [y]. e)\<cdot>n"
    by (auto simp add: predCC_eq dest!: set_mp[OF ccField_cc_restr])
next
  fix x y :: var and S e a
  assume "x \<notin> S" 
  assume "y \<notin> S"
  show "cc_restr S (CCexp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (CCexp e\<cdot>a)"
    sorry
next
  fix e
  assume "isLam e"
  thus "CCexp  e\<cdot>0 = ccSquare (fv e)"
    by (induction e rule: isLam.induct) (auto simp add: predCC_eq)
next
  fix \<Gamma> e a
  have "ccHeap \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)" by (rule ccHeap_eq)

  have "ccField  (ccHeap \<Gamma> e\<cdot>a) \<subseteq> fv \<Gamma> \<union> fv e"
    unfolding ccHeap_eq
    by (rule ccField_CCfix)
  hence "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) = cc_restr ((fv \<Gamma> \<union> fv e) - domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a)"
    by (auto intro: cc_restr_intersect)
  thus "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> CCexp (Let \<Gamma> e)\<cdot>a"
    by (simp add: ccHeap_eq[symmetric])
next
  fix \<Delta> :: heap and e a

  show "CCexp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
    by (auto simp add: ccHeap_def arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x ])

  fix x e' a'
  assume "map_of \<Delta> x = Some e'"
  hence [simp]: "x \<in> domA \<Delta>" by (metis domI dom_map_of_conv_domA) 
  assume "(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'"
  hence "(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) x = up\<cdot>a'" 
    by (simp add: Aheap_def)
  hence "CCexp e'\<cdot>a' \<sqsubseteq> ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a))"
    by (auto simp add: ccExp'_def dest: set_mp[OF ccField_CCexp])
  also
  have "ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) \<sqsubseteq>  ccHeap \<Delta> e\<cdot>a"
    using `map_of \<Delta> x = Some e'`
    by (force simp add: ccHeap_def ccBindsExtra_simp  ccBinds_eq  arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x ]
                intro: below_trans[OF _ join_above2] 
                simp del: ccBind_eq)
  finally
  show "CCexp e'\<cdot>a' \<sqsubseteq>  ccHeap \<Delta> e\<cdot>a" by this simp_all

  show "ccProd (fv e') (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" 
    using `map_of \<Delta> x = Some e'`
    by (force simp add: ccHeap_def ccBindsExtra_simp  ccBinds_eq  arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x ]
                intro: below_trans[OF _ join_above2]  below_trans[OF _ join_above1] 
                simp del: ccBind_eq)
(*
next
  fix \<Delta> e a
  assume "isLinear \<Delta> e a"

  from `isLinear _ _ _`
  have linear: "ccLinear (domA \<Delta>) (CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a))" unfolding isLinear_def ccHeap_eq.
  hence "ccLinear (domA \<Delta>) (ccBindsExtra \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) \<squnion> CCexp e\<cdot>a)"
    by (subst (asm) CCfix_unroll) simp
  hence  *: "ccLinear (domA \<Delta>) (CCexp e\<cdot>a)" and **: "\<And> x e'. map_of \<Delta> x = Some e' \<Longrightarrow> ccLinear (domA \<Delta>) (ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)))"
    by (auto simp add: ccBindsExtra_simp ccBinds_eq simp del: ccBind_eq)

  show "ccLinear (domA \<Delta>) (CCexp e\<cdot>a)" by (rule * )

  fix x e' a'
  assume "map_of \<Delta> x = Some e'"
  hence [simp]: "x \<in> domA \<Delta>" by (metis domI dom_map_of_conv_domA)
  
  assume "(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'"
  hence "(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) x = up\<cdot>a'" 
    by (simp add: Aheap_def)
  with linear
  have "ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCfix \<Delta>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) = CCexp e'\<cdot>a'"
    unfolding ccLinear_def
    by (auto simp add: ccExp'_def)
  with **[OF `map_of \<Delta> x = Some e'`] 
  show "ccLinear (domA \<Delta>) (CCexp e'\<cdot>a')" by simp
*)

next
  fix x \<Gamma> e a
  assume "x \<in> thunks \<Gamma>"
  hence [simp]: "x \<in> domA \<Gamma>" by (rule set_mp[OF thunks_domA])
  assume "x \<in> edom (Aheap \<Gamma> e\<cdot>a)"

  (*
  assume "x \<notin> calledOnce \<Gamma> e a"
  hence "x--x\<in>CCexp e\<cdot>a \<or> (\<exists> x' e' . map_of \<Gamma> x' = Some e' \<longrightarrow> x \<in> edom (fup\<cdot>(Aexp e')\<cdot>((Aheap \<Gamma> e\<cdot>a) x')))"
    by (auto simp add: calledOnce_def split: if_splits)
  hence "x \<in> ccManyCalls (CCfix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a))"
    sorry (* TODO: non-trivial step here. The assumptions should show that eventually, we believe x is called twice *)
  *)

  from `x \<in> thunks \<Gamma>`
  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)) x = up\<cdot>0" 
    by (subst Afix_unroll) (simp add: ABindsExtra_simp)
 
  thus "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
    by (simp add:  Aheap_simp)
next
  fix \<Delta> e a
  show "calledOnce \<Delta> e a \<inter> ccManyCalls (CCexp e\<cdot>a) = {}"
    by (auto simp add: calledOnce_def)
next
  fix \<Delta> :: heap and x e' e a u'
  assume a: "map_of \<Delta> x = Some e'"  "(Aheap \<Delta> e\<cdot>a) x = up\<cdot>u'"
  thus "edom (Aexp e'\<cdot>u') \<inter> calledOnce \<Delta> e a = {}"
    by (fastforce simp add: calledOnce_def)
qed

end
