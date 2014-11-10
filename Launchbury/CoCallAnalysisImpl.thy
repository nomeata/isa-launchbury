theory CoCallAnalysisImpl
imports CoCallFix  "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
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
  apply (auto dest: set_mp[OF ccFieldd_cc_restr])
  done

lemma predCC_eqvt[eqvt, simp]: "\<pi> \<bullet> (predCC S f) = predCC (\<pi> \<bullet> S) (\<pi> \<bullet> f)"
  unfolding predCC_def
  apply perm_simp
  apply (rule Abs_cfun_eqvt)
  apply (rule cont_if_else_above)
  apply (auto dest: set_mp[OF ccFieldd_cc_restr])
  done

lemma cc_restr_usless[simp]:
  "ccField G \<subseteq> S \<Longrightarrow> cc_restr S G = G"
  apply transfer
  apply (auto simp add: Field_def)
  apply (metis Domain.DomainI contra_subsetD)
  apply (metis Range.intros subsetCE)
  done

lemma cc_restr_cc_restr[simp]:
  "cc_restr S (cc_restr S G) = cc_restr S G"
  by transfer auto

lemma cc_restr_cc_square[simp]:
  "cc_restr S (ccSquare S) = ccSquare S"
  by simp

lemma cc_restr_predCC[simp]:
  "cc_restr S (predCC S f\<cdot>n) = predCC S f\<cdot>n"
  unfolding predCC_eq by simp

  
nominal_function
  cCCexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)" 
where
  "cCCexp (GVar b x) = (\<Lambda> n . (AE_singleton x \<cdot> (up \<cdot> n), \<bottom>))"
| "cCCexp (Lam [x]. e) = (\<Lambda> n . combined_restrict (fv (Lam [x]. e)) (fst (cCCexp e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp e\<cdot>a))\<cdot>n))"
| "cCCexp (App e x) = (\<Lambda> n . (fst (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)), snd (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> ccProd (fv e) {x}))"
| "cCCexp (Let \<Gamma> e) = (\<Lambda> n . combined_restrict (fv (Let \<Gamma> e)) (CoCallArityAnalysis.cccFix cCCexp \<Gamma> \<cdot> (cCCexp e \<cdot> n)))"
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
      have "combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))
      =  combined_restrict (fv (Terms.Let \<Gamma> body)) (- \<pi> \<bullet> (CoCallArityAnalysis.cccFix cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)))"
        by (rule combined_restrict_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> (CoCallArityAnalysis.cccFix cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)) = 
                       CoCallArityAnalysis.cccFix (- \<pi> \<bullet> cCCexp_sumC) \<Gamma>\<cdot>((- \<pi> \<bullet> cCCexp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "CoCallArityAnalysis.cccFix (- \<pi> \<bullet> cCCexp_sumC) \<Gamma> = CoCallArityAnalysis.cccFix cCCexp_sumC \<Gamma>"
        by (rule cccFix_cong[OF eqvt_at_apply[OF goal13(1)] refl])
      also have "(- \<pi> \<bullet> cCCexp_sumC) body = cCCexp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))) =
         (\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix cCCexp_sumC \<Gamma>\<cdot>(cCCexp_sumC body\<cdot>n)))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order

interpretation CoCallArityAnalysis cCCexp.

definition Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)" where "Aexp e = (\<Lambda> a. fst (cCCexp e \<cdot> a))"
definition CCexp :: "exp \<Rightarrow> (Arity \<rightarrow> CoCalls)" where "CCexp \<Gamma> = (\<Lambda> a. snd (cCCexp \<Gamma>\<cdot>a))"

definition Afix :: "heap \<Rightarrow> (AEnv \<times> CoCalls \<rightarrow> AEnv)" where "Afix e = (\<Lambda> ae. fst (cccFix e \<cdot> ae))"
definition CCfix :: "heap \<Rightarrow> (AEnv \<times> CoCalls \<rightarrow> CoCalls)" where "CCfix \<Gamma> = (\<Lambda> ae. snd (cccFix \<Gamma>\<cdot>ae))"

lemma Aexp_eqvt[eqvt]:  "\<pi> \<bullet> (Aexp e) = Aexp (\<pi> \<bullet> e)"
  unfolding Aexp_def by perm_simp (simp_all add: Abs_cfun_eqvt)
lemma CCexp_eqvt[eqvt]:  "\<pi> \<bullet> (CCexp e) = CCexp (\<pi> \<bullet> e)"
  unfolding CCexp_def by perm_simp (simp_all add: Abs_cfun_eqvt)
lemma Afix_eqvt[eqvt]:  "\<pi> \<bullet> (Afix \<Gamma>) = Afix (\<pi> \<bullet> \<Gamma>)"
  unfolding Afix_def by perm_simp (simp_all add: Abs_cfun_eqvt)
lemma CCfix_eqvt[eqvt]:  "\<pi> \<bullet> (CCfix \<Gamma>) = CCfix (\<pi> \<bullet> \<Gamma>)"
  unfolding CCfix_def by perm_simp (simp_all add: Abs_cfun_eqvt)

lemma Aexp_simps[simp]:
  "Aexp (GVar b x)\<cdot>n = AE_singleton x\<cdot>(up\<cdot>n)"
  "Aexp (Lam [x]. e)\<cdot>n = Aexp e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)"
  "Aexp (App e x)\<cdot>n = Aexp e\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0)"
  "Aexp (Let \<Gamma> e)\<cdot>n = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n, CCexp e\<cdot>n) f|` fv (Let \<Gamma> e)"
unfolding Aexp_def CCexp_def Afix_def by (simp add: beta_cfun)+


lemma CCexp_simps[simp]:
  "CCexp (GVar b x)\<cdot>n = \<bottom>"
  "CCexp (Lam [x]. e)\<cdot>n = predCC (fv (Lam [x]. e)) (CCexp e)\<cdot>n"
  "CCexp (App e x)\<cdot>n = CCexp e\<cdot>(inc\<cdot>n) \<squnion> ccProd (fv e) {x}"
  "CCexp (Let \<Gamma> e)\<cdot>n = cc_restr (fv (Let \<Gamma> e)) (CCfix \<Gamma>\<cdot>(Aexp e\<cdot>n, CCexp e\<cdot>n))"
unfolding Aexp_def CCexp_def CCfix_def by (simp add: beta_cfun)+



end

