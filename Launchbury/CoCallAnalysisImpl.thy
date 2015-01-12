theory CoCallAnalysisImpl
imports CoCallFix "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin

fun combined_restrict :: "var set \<Rightarrow> (AEnv \<times> CoCalls) \<Rightarrow> (AEnv \<times> CoCalls)"
  where "combined_restrict S (env, G) = (env f|` S, cc_restr S G)"

lemma fst_combined_restrict[simp]:
  "fst (combined_restrict S p) = fst p f|` S"
  by (cases p, simp)

lemma snd_combined_restrict[simp]:
  "snd (combined_restrict S p) = cc_restr S (snd p)"
  by (cases p, simp)

lemma combined_restrict_eqvt[eqvt]:
  shows "\<pi> \<bullet> combined_restrict S p = combined_restrict (\<pi> \<bullet> S) (\<pi> \<bullet> p)"
  by (cases p) auto

lemma combined_restrict_cont:
  "cont (\<lambda>x. combined_restrict S x)"
proof-
  have "cont (\<lambda>(env, G). combined_restrict S (env, G))" by simp
  thus ?thesis by (metis split_eta)
qed
lemmas cont_compose[OF combined_restrict_cont, cont2cont, simp]

lemma combined_restrict_perm:
  assumes "supp \<pi> \<sharp>* S" and [simp]: "finite S"
  shows "combined_restrict S (\<pi> \<bullet> p) = combined_restrict S p"
proof(cases p)
  fix env :: AEnv and  G :: CoCalls
  assume "p = (env, G)"
  moreover 
  from assms
  have "env_restr S (\<pi> \<bullet> env) = env_restr S env" by (rule env_restr_perm)
  moreover
  from assms
  have "cc_restr S (\<pi> \<bullet> G) = cc_restr S G" by (rule cc_restr_perm)
  ultimately
  show ?thesis by simp
qed

definition predCC :: "var set \<Rightarrow> (Arity \<rightarrow> CoCalls) \<Rightarrow> (Arity \<rightarrow> CoCalls)"
  where "predCC S f = (\<Lambda> a. if a \<noteq> 0 then cc_restr S (f\<cdot>(pred\<cdot>a)) else ccSquare S)"

lemma predCC_eq:
  shows "predCC S f \<cdot> a = (if a \<noteq> 0 then cc_restr S (f\<cdot>(pred\<cdot>a)) else ccSquare S)"
  unfolding predCC_def
  apply (rule beta_cfun)
  apply (rule cont_if_else_above)
  apply (auto dest: set_mp[OF ccField_cc_restr])
  done

lemma predCC_eqvt[eqvt, simp]: "\<pi> \<bullet> (predCC S f) = predCC (\<pi> \<bullet> S) (\<pi> \<bullet> f)"
  unfolding predCC_def
  apply perm_simp
  apply (rule Abs_cfun_eqvt)
  apply (rule cont_if_else_above)
  apply (auto dest: set_mp[OF ccField_cc_restr])
  done

lemma cc_restr_predCC:
  "cc_restr S (predCC S' f\<cdot>n) = (predCC (S' \<inter> S) (\<Lambda> n. cc_restr S (f\<cdot>n)))\<cdot>n"
  unfolding predCC_eq
  by (auto simp add: inf_commute ccSquare_def)

lemma cc_restr_predCC'[simp]:
  "cc_restr S (predCC S f\<cdot>n) = predCC S f\<cdot>n"
  unfolding predCC_eq by simp

  
nominal_function
  cCCexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)" 
where
  "cCCexp (GVar b x) =   (\<Lambda> n . (esing x \<cdot> (up \<cdot> n),                                   \<bottom>))"
| "cCCexp (Lam [x]. e) = (\<Lambda> n . combined_restrict (fv (Lam [x]. e)) (fst (cCCexp e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp e\<cdot>a))\<cdot>n))"
| "cCCexp (App e x) =    (\<Lambda> n . (fst (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> (esing x \<cdot> (up\<cdot>0)),          snd (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> ccProd {x} (insert x (fv e))))"
| "cCCexp (Let \<Gamma> e) =    (\<Lambda> n . combined_restrict (fv (Let \<Gamma> e)) (CoCallArityAnalysis.cccFix_choose cCCexp \<Gamma> \<cdot> (cCCexp e\<cdot>n)))"
proof-
case goal1
    show ?case
    unfolding eqvt_def cCCexp_graph_aux_def
    apply rule
    apply (perm_simp)
    apply (simp add: Abs_cfun_eqvt)
    done
next
case goal3 thus ?case by (metis Terms.exp_strong_exhaust)
next
case (goal8 x e x' e')
  from goal8(9)
  show ?case
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set)" 
    {
    fix n
    have "combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n)
       = combined_restrict (fv (Lam [x]. e)) (- \<pi> \<bullet> (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n))"
      by (rule combined_restrict_perm[symmetric, OF *]) simp
    also have "\<dots> = combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC e\<cdot>(pred\<cdot>n)), predCC (- \<pi> \<bullet> fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC e\<cdot>a))\<cdot>n)"
      by (perm_simp, simp add: eqvt_at_apply[OF goal8(1)] pemute_minus_self Abs_cfun_eqvt)
    also have "- \<pi> \<bullet> fv (Lam [x]. e) = (fv (Lam [x]. e) :: var set)" by (rule perm_supp_eq[OF *])
    also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n))
        = (\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC e\<cdot>a))\<cdot>n))" by simp
  qed
next
case (goal13 \<Gamma> body \<Gamma>' body')
  from goal13(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let \<Gamma> body) :: var set)"
    
    { fix n
      have "combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))
      =  combined_restrict (fv (Terms.Let \<Gamma> body)) (- \<pi> \<bullet> (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)))"
        by (rule combined_restrict_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)) = 
                       CoCallArityAnalysis.cccFix_choose (- \<pi> \<bullet> cCCexp_sumC) \<Gamma>\<cdot>((- \<pi> \<bullet> cCCexp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "CoCallArityAnalysis.cccFix_choose (- \<pi> \<bullet> cCCexp_sumC) \<Gamma> = CoCallArityAnalysis.cccFix_choose cCCexp_sumC \<Gamma>"
        thm cccFix_cong
        by (rule cccFix_choose_cong[OF eqvt_at_apply[OF goal13(1)] refl])
      also have "(- \<pi> \<bullet> cCCexp_sumC) body = cCCexp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))) =
         (\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC \<Gamma>\<cdot>(cCCexp_sumC body\<cdot>n)))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order


interpretation CoCallArityAnalysis cCCexp.

lemma cCCexp_eq[simp]:
  "cCCexp (GVar b x)\<cdot>n =   (esing x \<cdot> (up \<cdot> n),                                   \<bottom>)"
  "cCCexp (Lam [x]. e)\<cdot>n = combined_restrict (fv (Lam [x]. e)) (fst (cCCexp e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp e\<cdot>a))\<cdot>n)"
  "cCCexp (App e x)\<cdot>n =    (fst (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> (esing x \<cdot> (up\<cdot>0)),          snd (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> ccProd {x} (insert x (fv e)))"
  "cCCexp (Let \<Gamma> e)\<cdot>n =    combined_restrict (fv (Let \<Gamma> e)) (CoCallArityAnalysis.cccFix_choose cCCexp \<Gamma> \<cdot> (cCCexp e\<cdot>n))"
by (simp_all)
declare cCCexp.simps[simp del]


lemma Aexp_simps[simp]:
  "Aexp (GVar b x)\<cdot>n = esing x\<cdot>(up\<cdot>n)"
  "Aexp (Lam [x]. e)\<cdot>n = Aexp e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)"
  "Aexp (App e x)\<cdot>n = Aexp e\<cdot>(inc\<cdot>n) \<squnion> esing x\<cdot>(up\<cdot>0)"
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aexp (Let \<Gamma> e)\<cdot>n = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` (fv (Let \<Gamma> e))"
  "atom x \<sharp> e \<Longrightarrow> Aexp (let x be e in exp)\<cdot>n = (fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> (Aexp exp\<cdot>n, CCexp exp\<cdot>n)) \<squnion> Aexp exp\<cdot>n) f|` (fv (let x be e in exp))"
 by (simp add: cccFix_eq Aexp_eq fup_Aexp_eq CCexp_eq fup_CCexp_eq)+


lemma CCexp_simps[simp]:
  "CCexp (GVar b x)\<cdot>n = \<bottom>"
  "CCexp (Lam [x]. e)\<cdot>n = predCC (fv (Lam [x]. e)) (CCexp e)\<cdot>n"
  "CCexp (App e x)\<cdot>n = CCexp e\<cdot>(inc\<cdot>n) \<squnion> ccProd {x} (insert x (fv e))"
  "\<not> nonrec \<Gamma> \<Longrightarrow> CCexp (Let \<Gamma> e)\<cdot>n = cc_restr (fv (Let \<Gamma> e)) (CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n  \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>n))"
  "atom x \<sharp> e \<Longrightarrow> CCexp (let x be e in exp)\<cdot>n =
    cc_restr (fv (let x be e in exp)) (ccBind x e \<cdot>(Aheap_nonrec x e\<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n), CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors x (CCexp exp\<cdot>n) - (if isLam e then {} else {x})) \<squnion> CCexp exp\<cdot>n)"
 by (simp add: cccFix_eq Aexp_eq fup_Aexp_eq CCexp_eq fup_CCexp_eq predCC_eq)+

lemma ccField_CCexp:
  "ccField (CCexp e\<cdot>n) \<subseteq> fv e"
by (induction e arbitrary: n rule: exp_induct_rec)
   (auto simp add: ccField_ccProd predCC_eq dest: set_mp[OF ccField_cc_restr])

lemma cc_restr_CCexp[simp]:
  "cc_restr (fv e) (CCexp e\<cdot>a) = CCexp e\<cdot>a"
by (rule cc_restr_noop[OF ccField_CCexp])



end

