theory CoCallAnalysisImpl
imports CoCallFix  "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin

fun combined_restrict :: "var set \<Rightarrow> (AEnv \<times> CoCalls) \<Rightarrow> (AEnv \<times> CoCalls)"
  where "combined_restrict S (env, G) = (env f|` S, cc_restr S G)"

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
  
nominal_function
  cccExp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)" 
where
  "cccExp (GVar b x) = (\<Lambda> n . (AE_singleton x \<cdot> (up \<cdot> n), \<bottom>))"
| "cccExp (Lam [x]. e) = (\<Lambda> n . combined_restrict (fv (Lam [x]. e)) (fst (cccExp e\<cdot>(pred\<cdot>n)), \<bottom>))"
| "cccExp (App e x) = (\<Lambda> n . (fst (cccExp e\<cdot>(inc\<cdot>n)) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)), \<bottom>))"
| "cccExp (Let as e) = (\<Lambda> n . combined_restrict (fv (Let as e)) (CoCallArityAnalysis.ccFix cccExp as \<cdot> (cccExp e \<cdot> n)))"
proof-
case goal1
    show ?case
    unfolding eqvt_def cccExp_graph_aux_def
    apply rule
    apply (perm_simp)
    apply (simp add: Abs_cfun_eqvt)
    done
next
case goal3 thus ?case by (metis Terms.exp_strong_exhaust)
next
case (goal8 x e x' e')
  from goal8(5)
  show ?case
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set)" 
    {
    fix n
    have "combined_restrict (fv (Lam [x]. e)) (fst (cccExp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), \<bottom>) = combined_restrict (fv (Lam [x]. e)) (- \<pi> \<bullet> (fst (cccExp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), \<bottom>))"
      by (rule combined_restrict_perm[symmetric, OF *]) simp
    also have "\<dots> = combined_restrict (fv (Lam [x]. e)) (fst (cccExp_sumC e\<cdot>(pred\<cdot>n)), \<bottom>)"
      by (simp add: eqvt_at_apply[OF goal8(1)] pemute_minus_self)
    also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cccExp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), \<bottom>)) = (\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cccExp_sumC e\<cdot>(pred\<cdot>n)), \<bottom>))" by simp
  qed
next
case (goal13 as body as' body')
  from goal13(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let as body) :: var set)"
    
    { fix n
      have "combined_restrict (fv (Terms.Let as body)) (CoCallArityAnalysis.ccFix cccExp_sumC (\<pi> \<bullet> as)\<cdot>(cccExp_sumC (\<pi> \<bullet> body)\<cdot>n))
      =  combined_restrict (fv (Terms.Let as body)) (- \<pi> \<bullet> (CoCallArityAnalysis.ccFix cccExp_sumC (\<pi> \<bullet> as)\<cdot>(cccExp_sumC (\<pi> \<bullet> body)\<cdot>n)))"
        by (rule combined_restrict_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> (CoCallArityAnalysis.ccFix cccExp_sumC (\<pi> \<bullet> as)\<cdot>(cccExp_sumC (\<pi> \<bullet> body)\<cdot>n)) = 
                       CoCallArityAnalysis.ccFix (- \<pi> \<bullet> cccExp_sumC) as\<cdot>((- \<pi> \<bullet> cccExp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "CoCallArityAnalysis.ccFix (- \<pi> \<bullet> cccExp_sumC) as = CoCallArityAnalysis.ccFix cccExp_sumC as"
        by (rule ccFix_cong[OF eqvt_at_apply[OF goal13(1)] refl])
      also have "(- \<pi> \<bullet> cccExp_sumC) body = cccExp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Terms.Let as body)) (CoCallArityAnalysis.ccFix cccExp_sumC (\<pi> \<bullet> as)\<cdot>(cccExp_sumC (\<pi> \<bullet> body)\<cdot>n))) =
         (\<Lambda> n. combined_restrict (fv (Terms.Let as body)) (CoCallArityAnalysis.ccFix cccExp_sumC as\<cdot>(cccExp_sumC body\<cdot>n)))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order

end

