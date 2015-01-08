theory CoCallImplCorrect
imports CoCallAnalysisImpl  CoCallCardinality 
begin

lemma ccField_CCexp':
  "ccField (ccExp' e\<cdot>n) \<subseteq> fv e"
by (cases n) (auto dest: set_mp[OF ccField_CCexp])

interpretation ArityAnalysis Aexp.

lemma Aexp_edom': "edom (Aexp e\<cdot>a) \<subseteq> fv e"
  by (induction e arbitrary: a rule: exp_induct_rec)(auto)


interpretation EdomArityAnalysis Aexp by default (rule Aexp_edom')

(*
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
*)
   
lemma ccField_CCfix: "ccField (CCfix \<Gamma>\<cdot>(ae, CCexp  e\<cdot>a)) \<subseteq> fv \<Gamma> \<union> fv e"
  unfolding CCfix_def
  apply simp
  apply (rule fix_ind)
  apply simp_all
  apply (auto simp add: ccBindsExtra_simp ccBinds_eq ccBind_eq ccField_cc_restr
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

lemma Aexp_Let_simp1[simp]:
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aexp (Let \<Gamma> e)\<cdot>n = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` (- domA \<Gamma>)"
  unfolding Aexp_simps
  by (rule env_restr_cong) (auto dest!: set_mp[OF Afix_edom] set_mp[OF Aexp_edom] set_mp[OF thunks_domA])

lemma Aexp_Let_simp2[simp]:
  "atom x \<sharp> e \<Longrightarrow> Aexp (let x be e in exp)\<cdot>n = env_delete x (fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> (Aexp exp\<cdot>n, CCexp exp\<cdot>n)) \<squnion> Aexp exp\<cdot>n)"
  unfolding Aexp_simps env_delete_restr
  by (rule env_restr_cong) (auto dest!: set_mp[OF fup_Aexp_edom]  set_mp[OF Aexp_edom])

declare Aexp_simps(4)[simp del]
declare Aexp_simps(5)[simp del]


lemma CCexp_Let_simp1[simp]:
  "\<not> nonrec \<Gamma> \<Longrightarrow> CCexp (Let \<Gamma> e)\<cdot>n = cc_restr (- domA \<Gamma>) (CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>n))"
  unfolding CCexp_simps
  by (rule cc_restr_intersect)  (auto dest!: set_mp[OF ccField_CCfix])

lemma CCexp_Let_simp2[simp]:
  "atom x \<sharp> e \<Longrightarrow> CCexp (let x be e in exp)\<cdot>n = cc_restr (- {x}) (ccBind x e \<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors {x} (CCexp exp\<cdot>n)) \<squnion> CCexp exp\<cdot>n)"
  unfolding CCexp_simps
  by (rule cc_restr_intersect)
     (auto simp add: ccField_ccProd ccBind_eq dest!: set_mp[OF ccField_CCexp] set_mp[OF ccField_cc_restr] set_mp[OF ccNeighbors_ccField])
declare CCexp_simps(4)[simp del]
declare CCexp_simps(5)[simp del]


lemma Aexp_subst_upd: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
proof (nominal_induct e avoiding: x y  arbitrary: n rule: exp_strong_induct_rec)
  case (Var v) 
  thus ?case by auto
next
  case (App e v x y n)
  have "Aexp (App e v)[y::=x]\<cdot>n \<sqsubseteq> (Aexp e[y::=x]\<cdot>(inc\<cdot>n)) \<squnion> (esing (v[y::v=x])\<cdot>(up\<cdot>0))" by simp
  also have "Aexp e[y::=x]\<cdot>(inc\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0)" by (rule App.hyps)
  also have "(esing (v[y::v=x])\<cdot>(up\<cdot>0)) \<sqsubseteq> (esing v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "(Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0) \<squnion> (esing v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0) 
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
  hence "x \<notin> domA \<Gamma>" and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  hence "x \<notin> thunks \<Gamma>" and  "y \<notin> thunks \<Gamma>"
    by (metis contra_subsetD thunks_domA)+

  note this[simp] Let(1,2)[simp]

  note Let(3)
  hence "\<not> nonrec (\<Gamma>[y::h=x])"
    apply (auto elim!: nonrecE)
    sorry

  have "Aexp (Let \<Gamma> e)[y::=x]\<cdot>n \<sqsubseteq> Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>[y::h=x])) f|` ( - domA \<Gamma>)"
    by (simp add: fresh_star_Pair `\<not> nonrec (\<Gamma>[y::h=x])`)
  also have "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
    by fact
  also have "(\<lambda>_.up\<cdot>0) f|` (thunks (\<Gamma>[y::h=x])) \<sqsubseteq> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))(y := \<bottom>, x := up\<cdot>0)"
    by (auto intro: fun_belowI `y \<notin> thunks \<Gamma>`)
  also have "(Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0) \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))(y := \<bottom>, x := up\<cdot>0) = (Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)))(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "Afix \<Gamma>[y::h=x]\<cdot>((Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)))(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))))(y := \<bottom>, x := up\<cdot>0)"
    by (rule Afix_subst_approx[OF Let(4) `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`])
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))))(y := \<bottom>, x := up\<cdot>0) f|` (- domA \<Gamma>) = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))) f|` (- domA \<Gamma>)) (y := \<bottom>, x := up\<cdot>0)"
    by (auto simp add: `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`)
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> ((\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>))) f|` (- domA \<Gamma>)) = Aexp (Let \<Gamma> e)\<cdot>n"
    by (simp add: `\<not> nonrec \<Gamma>`)
  finally show ?case by this simp_all
next
  case (Let_nonrec x' e exp x y n)
  show ?case sorry
qed

lemma Aexp_restr_subst:
  assumes "x \<notin> S" and "y \<notin> S"
  shows "(Aexp e[x::=y]\<cdot>a) f|` S = (Aexp e\<cdot>a) f|` S"
using assms
proof (nominal_induct e avoiding: x y  arbitrary: a S rule: exp_strong_induct_rec_set)
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
  hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  
  note this[simp] Let(1,2)[simp]

  note Let(3)
  hence "\<not> nonrec (\<Gamma>[x::h=y])"
    apply (auto elim!: nonrecE)
    sorry


  from Let
  have "Afix \<Gamma>[x::h=y]\<cdot>(Aexp e[x::=y]\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` (thunks \<Gamma>)) f|` (S \<union> domA \<Gamma>) = Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` (thunks \<Gamma>)) f|` (S \<union> domA \<Gamma>)"
    apply (auto simp add: fresh_star_Pair)
    apply (subst Afix_restr_subst')
    apply auto[1]
    apply auto[3]
    apply (simp add: env_restr_join)
    apply (subst Afix_restr) back
    apply auto[1]
    apply (simp add: env_restr_join)
    done
  thus ?case using Let(1,2)
    using `\<not> nonrec \<Gamma>` `\<not> nonrec (\<Gamma>[x::h=y])`
    by (auto simp add: fresh_star_Pair elim:env_restr_eq_subset[rotated])
next
  case (Let_nonrec x' e exp x y a S)
  show ?case
    sorry
qed

interpretation CorrectArityAnalysis' Aexp
proof default
(*
  fix \<pi>
  show "\<pi> \<bullet> Aexp = Aexp" by perm_simp rule
next
*)
  fix x y :: var and e :: exp  and a 
  show "Aexp e[y::=x]\<cdot>a \<sqsubseteq> env_delete y (Aexp e\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)"
    apply (rule below_trans[OF Aexp_subst_upd])
    apply (rule fun_belowI)
    apply auto
    done
qed (simp_all add:Aexp_restr_subst)

definition Aheap_nonrec where
  "Aheap_nonrec x e' e = (\<Lambda> a. esing x\<cdot>(ABind_nonrec x e'\<cdot>(CoCallArityAnalysis.Aexp cCCexp e\<cdot>a, CoCallArityAnalysis.CCexp cCCexp e\<cdot>a)))"

lemma Aheap_nonrec_simp:
  "Aheap_nonrec x e' e\<cdot>a = esing x\<cdot>(ABind_nonrec x e'\<cdot>(CoCallArityAnalysis.Aexp cCCexp e\<cdot>a, CoCallArityAnalysis.CCexp cCCexp e\<cdot>a))"
  unfolding Aheap_nonrec_def by simp

lemma Aheap_nonrec_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap_nonrec x e' e) = Aheap_nonrec (\<pi> \<bullet> x) (\<pi> \<bullet> e') (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding Aheap_nonrec_simp
  by (perm_simp, rule)

definition Aheap where
  "Aheap \<Gamma> e = (\<Lambda> a. if nonrec \<Gamma> then (split Aheap_nonrec (hd \<Gamma>) e) \<cdot> a else  (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` domA \<Gamma>)"

lemma Aheap_simp1[simp]:
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aheap \<Gamma> e \<cdot>a = (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` domA \<Gamma>"
  unfolding Aheap_def by simp

lemma Aheap_simp2[simp]:
  "atom x \<sharp> e' \<Longrightarrow> Aheap [(x,e')] e \<cdot>a = Aheap_nonrec x e' e\<cdot>a "
  unfolding Aheap_def by (simp add: nonrec_def)

lemma Aheap_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap \<Gamma> e) = Aheap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  apply (cases nonrec \<pi> rule: eqvt_cases[where x = \<Gamma>])
  apply simp
  apply (erule nonrecE)
  apply simp
  apply (perm_simp, rule)
  apply simp
  apply (perm_simp, rule)
  done

interpretation CorrectArityAnalysisLet' Aexp Aheap
proof default
  fix \<pi> show "\<pi> \<bullet> Aheap = Aheap"
    by perm_simp rule
next
  fix \<Gamma> e a
  show "edom (Aheap \<Gamma> e\<cdot>a) \<subseteq> domA \<Gamma>"
    by (cases "nonrec \<Gamma>")
       (auto simp add: Aheap_nonrec_simp dest: set_mp[OF edom_esing_subset] elim!: nonrecE)
next
  fix x y :: var and \<Gamma> :: heap and e :: exp
  assume assms: "x \<notin> domA \<Gamma>"  "y \<notin> domA \<Gamma>"
  show "Aheap \<Gamma>[x::h=y] e[x::=y] = Aheap \<Gamma> e"
  proof(cases "nonrec \<Gamma>")
    case False[simp]
    hence [simp]: "\<not> nonrec (\<Gamma>[x::h=y])"
      sorry
    show ?thesis
    apply (rule cfun_eqI)
    apply simp
    apply (subst Afix_restr_subst[OF assms subset_refl])
    apply (subst Afix_restr[OF  subset_refl]) back
    apply (simp add: env_restr_join)
    apply (subst Aexp_restr_subst[OF assms])
    apply simp
    done
  next
    case True
    then obtain x' e' where [simp]: "\<Gamma> = [(x',e')]" "atom x' \<sharp> e'" by (auto elim: nonrecE)
    
    have [simp]: "atom x' \<sharp> e'[x::=y]" sorry

    have [simp]: "\<And> a. (Aexp e[x::=y]\<cdot>a) x' = (Aexp e\<cdot>a) x'" sorry
    have [simp]: "\<And> a. x'--x'\<in>(CCexp e[x::=y]\<cdot>a) \<longleftrightarrow> x'--x'\<in>(CCexp e\<cdot>a)" sorry
    
    show ?thesis
      apply -
      apply (rule cfun_eqI)
      apply (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq)
      done
  qed
next
  fix \<Gamma> e a
  show "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
  proof(cases "nonrec \<Gamma>")
    case False
    thus ?thesis
      by (auto simp add: Aheap_def join_below_iff env_restr_join2 Compl_partition intro:  below_trans[OF _ Afix_above_arg])
  next
    case True
    then obtain x e' where [simp]: "\<Gamma> = [(x,e')]" "atom x \<sharp> e'" by (auto elim: nonrecE)

    from `atom x \<sharp> e'`
    have "x \<notin> fv e'" by (simp add: fv_def fresh_def)

    hence "\<And> a. x \<notin> edom (fup\<cdot>(Aexp e')\<cdot>a)"
      by (auto dest:set_mp[OF fup_Aexp_edom])
    hence [simp]: "\<And> a. (fup\<cdot>(Aexp e')\<cdot>a) x = \<bottom>" by (simp add: edomIff)

    show ?thesis
      apply (rule env_restr_below_split[where S = "{x}"])
      apply (rule env_restr_belowI2)
      apply (auto simp add:  Aheap_nonrec_simp Aexp'_def join_below_iff env_restr_join env_delete_restr)
      apply (rule ABind_nonrec_above_arg)
      apply (rule below_trans[OF _ join_above2])
      apply (rule below_trans[OF _ join_above2])
      apply (rule below_refl)
      done
  qed
qed

definition ccHeap_nonrec
  where "ccHeap_nonrec x e exp = (\<Lambda> n. ccBind x e \<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors {x} (CCexp exp\<cdot>n)) \<squnion> CCexp exp\<cdot>n)"

lemma ccHeap_nonrec_eq:
   "ccHeap_nonrec x e exp \<cdot> n = ccBind x e \<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors {x} (CCexp exp\<cdot>n)) \<squnion> CCexp exp\<cdot>n"
unfolding ccHeap_nonrec_def by simp

definition ccHeap_rec :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  where "ccHeap_rec \<Gamma> e  = (\<Lambda> a. CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a))"

lemma ccHeap_rec_eq:
  "ccHeap_rec \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a)"
unfolding ccHeap_rec_def by simp

definition ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  where "ccHeap \<Gamma>  = (if nonrec \<Gamma> then split ccHeap_nonrec (hd \<Gamma>) else ccHeap_rec \<Gamma>)"

lemma ccHeap_simp1:
  "\<not> nonrec \<Gamma> \<Longrightarrow> ccHeap \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a)"
  by (simp add: ccHeap_def ccHeap_rec_eq)

lemma ccHeap_simp2:
  "atom x \<sharp> e \<Longrightarrow> ccHeap [(x,e)] exp\<cdot>n = ccBind x e \<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors {x} (CCexp exp\<cdot>n)) \<squnion> CCexp exp\<cdot>n"
  by (simp add: ccHeap_def ccHeap_nonrec_eq nonrec_def)

lemma CCexp_subst:
  assumes "x \<notin> S" and "y \<notin> S"
  shows "cc_restr S (CCexp e[y::=x]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
using assms
proof (nominal_induct e avoiding: x y  arbitrary: a  S rule: exp_strong_induct_rec_set)
  case (Var v) 
  thus ?case by auto
next
  case (App e v)
  thus ?case
    by (auto simp add: Int_insert_left fv_subst_int simp del: join_comm intro: join_mono)
next
  case (Lam v e)
  thus ?case
  by (auto simp add: cc_restr_predCC  Diff_Int_distrib2 fv_subst_int env_restr_join env_delete_env_restr_swap[symmetric])
next
  case (Let \<Gamma> e)
  hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+

  note this[simp] Let(1,2)[simp]


  note Let(3)
  hence "\<not> nonrec (\<Gamma>[y::h=x])"
    apply (auto elim!: nonrecE)
    sorry
  
  have "cc_restr (S \<union> domA \<Gamma>) (CCfix \<Gamma>[y::h=x]\<cdot>(Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` thunks \<Gamma>), CCexp e[y::=x]\<cdot>a)) =
        cc_restr (S \<union> domA \<Gamma>) (CCfix \<Gamma>\<cdot>        (Afix \<Gamma>\<cdot>        (Aexp e\<cdot>       a \<squnion> (\<lambda>_. up\<cdot>0) f|` thunks \<Gamma>), CCexp e\<cdot>       a))"
    apply (subst CCfix_restr_subst')
      apply (erule Let(4))
      apply (auto simp add: Let(6,7))[5]
    apply (subst CCfix_restr) back
      apply simp
    apply (subst Afix_restr_subst)
      apply (auto simp add: Let(6,7))[3]
    apply (subst Afix_restr) back
      apply simp
    apply (simp only: env_restr_join)
    apply (subst Aexp_restr_subst)
      apply (auto simp add: Let(6,7))[2]
    apply (subst Let(5))
      apply (auto simp add: Let(6,7))[2]
    apply rule
    done
  thus ?case using Let(1,2) `\<not> nonrec \<Gamma>` `\<not> nonrec (\<Gamma>[y::h=x])`
    by (auto simp add: fresh_star_Pair ccHeap_simp1 elim: cc_restr_eq_subset[rotated] )
next
  case (Let_nonrec x' e exp x y S)
  show ?case sorry
qed

interpretation CoCallCardinality CCexp ccHeap Aexp Aheap
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
  assume "x \<notin> S"  and "y \<notin> S"
  thus "cc_restr S (CCexp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (CCexp e\<cdot>a)"
    by (rule eq_imp_below[OF CCexp_subst])
next
  fix e
  assume "isLam e"
  thus "CCexp  e\<cdot>0 = ccSquare (fv e)"
    by (induction e rule: isLam.induct) (auto simp add: predCC_eq)
next
  fix \<Gamma> e a
  show "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> CCexp (Let \<Gamma> e)\<cdot>a"
  proof(cases "nonrec \<Gamma>")
    case False[simp]
    have "ccField  (ccHeap \<Gamma> e\<cdot>a) \<subseteq> fv \<Gamma> \<union> fv e"
      unfolding ccHeap_simp1[OF False]
      by (rule ccField_CCfix)
    thus "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> CCexp (Let \<Gamma> e)\<cdot>a"
      by (simp add: ccHeap_simp1[OF False, symmetric])
  next
    case True
    thus ?thesis  by (auto simp add: ccHeap_simp2 elim!: nonrecE)
  qed
next
  fix \<Delta> :: heap and e a

  show "CCexp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
    by (cases "nonrec \<Delta>")
       (auto simp add: ccHeap_simp1 ccHeap_simp2 arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x ] elim!: nonrecE)

  fix x e' a'
  assume "map_of \<Delta> x = Some e'"
  hence [simp]: "x \<in> domA \<Delta>" by (metis domI dom_map_of_conv_domA) 
  assume "(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'"
  hence "(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>))) x = up\<cdot>a'" 
    by (simp add: Aheap_def)
  hence "CCexp e'\<cdot>a' \<sqsubseteq> ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCfix \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCexp e\<cdot>a))"
    by (auto simp add: ccExp'_def dest: set_mp[OF ccField_CCexp])
  also
  have "ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCfix \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCexp e\<cdot>a)) \<sqsubseteq>  ccHeap \<Delta> e\<cdot>a"
    using `map_of \<Delta> x = Some e'`
    by (force simp add: ccHeap_def ccBindsExtra_simp  ccBinds_eq  arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x ]
                intro: below_trans[OF _ join_above2]
                simp del: ccBind_eq)
  finally
  show "CCexp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by this simp_all

  show "ccProd (fv e') (ccNeighbors {x} (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" 
  proof (cases "nonrec \<Delta>")
    case False[simp]

    have "ccProd (fv e') (ccNeighbors {x} (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccProd (fv e') (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a))"
      sorry
    also have "\<dots> \<sqsubseteq> (\<Squnion>x\<mapsto>e'\<in>map_of \<Delta>. ccProd (fv e') (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)))" 
      using `map_of \<Delta> x = Some e'` by (rule below_lubmapI)
    also have "\<dots> \<sqsubseteq> ccBindsExtra \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), ccHeap \<Delta> e\<cdot>a)"
      by (simp add: ccBindsExtra_simp  below_trans[OF _ join_above2])
    also have "\<dots> \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      by (simp add: ccHeap_simp1  arg_cong[OF CCfix_unroll, where f = "op \<sqsubseteq> x" for x])
    finally
    show "ccProd (fv e') (ccNeighbors {x} (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by this simp_all
  next
    case True
    with `map_of \<Delta> x = Some e'`
    have [simp]: "\<Delta> = [(x,e')]" "atom x \<sharp> e'" by (auto elim!: nonrecE split: if_splits)
    hence [simp]: "x \<notin> fv e'" by (auto simp add: fresh_def fv_def)

    have [simp]: "(ccNeighbors {x} (CoCallAnalysis.ccBind (CoCallArityAnalysis.CCexp cCCexp) x e'\<cdot>(CoCallArityAnalysis.Aexp cCCexp e\<cdot>a, CoCallArityAnalysis.CCexp cCCexp e\<cdot>a))) = {}"
     by (rule ccNeighbors_disjoint_empty) (auto simp add: ccBind_eq dest!: set_mp[OF ccField_cc_restr] set_mp[OF ccField_CCexp'])

    thus ?thesis
      using `map_of \<Delta> x = Some e'` `(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'`
      apply (auto simp add: ccHeap_simp2 ccNeighbors_ccProd Aheap_nonrec_simp ABind_nonrec_eq join_below_iff  below_trans[OF _ join_above2] elim!: nonrecE split: if_splits)
      apply (simp add: ccBind_eq ccSquare_def below_trans[OF _ join_above2])
      
      apply (simp add: ccBind_eq)
      sorry
  qed
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
  assume [simp]: "\<not> nonrec \<Gamma>"
  assume "x \<in> thunks \<Gamma>"
  hence [simp]: "x \<in> domA \<Gamma>" by (rule set_mp[OF thunks_domA])
  assume "x \<in> edom (Aheap \<Gamma> e\<cdot>a)"

  from `x \<in> thunks \<Gamma>`
  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Gamma>))) x = up\<cdot>0" 
    by (subst Afix_unroll) simp

  thus "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0" by simp
next
  fix x \<Gamma> e a
  assume "nonrec \<Gamma>"
  then obtain x' e' where [simp]: "\<Gamma> = [(x',e')]" "atom x' \<sharp> e'" by (auto elim: nonrecE)
  assume "x \<in> thunks \<Gamma>"
  hence [simp]: "x = x'" "\<not> isLam e'" by (auto simp add: thunks_Cons split: if_splits)

  assume "x \<in> ccManyCalls (CCexp e\<cdot>a)"
  hence [simp]: "x'--x'\<in> CCexp  e\<cdot>a" by simp

  from `x \<in> thunks \<Gamma>`
  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Gamma>))) x = up\<cdot>0" 
    by (subst Afix_unroll) simp

  show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0" by (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq)
qed

end
