theory ArityAnalysisPreImpl
imports ArityAnalysisSig "Env-Nominal"
begin

definition thunks_AE  :: "heap \<Rightarrow> AEnv" where
  "thunks_AE \<Gamma> = (\<lambda> x . (if x \<in> thunks \<Gamma> then up\<cdot>0 else \<bottom>))"

lemma edom_thunks_AE: "edom (thunks_AE \<Gamma>) \<subseteq> domA \<Gamma>"
  unfolding edom_def thunks_AE_def by (auto dest: set_mp[OF thunks_domA])

lemma thunks_AE_eqvt[eqvt]:
  "\<pi> \<bullet> thunks_AE \<Gamma> = thunks_AE (\<pi> \<bullet> \<Gamma>)"
  unfolding thunks_AE_def
  by perm_simp rule

lemma thunks_AE_subst[simp]:
  "thunks_AE \<Gamma>[y::h=x] = thunks_AE \<Gamma>"
  unfolding thunks_AE_def by simp

lemma thunks_AE_subst_approx:
  "y \<notin> domA \<Gamma> \<Longrightarrow> thunks_AE \<Gamma>[y::h=x] \<sqsubseteq> (thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)"
  by (auto intro!: fun_belowI dest!: contra_subsetD[OF edom_thunks_AE] simp add: edomIff)

locale ArityAnalysisPreImpl =
  fixes Afix ::  "(exp \<Rightarrow> (Arity \<rightarrow> AEnv)) \<Rightarrow> heap \<Rightarrow> AEnv \<rightarrow> AEnv"
  assumes Afix_eqvt: "p \<bullet> Afix = Afix"
  assumes Afix_cong[fundef_cong]:
    "\<lbrakk> (\<And> e. size e \<le> size_list (\<lambda>p. size (snd p)) heap1 \<Longrightarrow> aexp1 e = aexp2 e); heap1 = heap2 \<rbrakk>
        \<Longrightarrow> Afix aexp1 heap1 = Afix aexp2 heap2"
begin
  
nominal_function
  Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)"
where
  "Aexp (Var x) = (\<Lambda> n . esing x\<cdot>(up\<cdot>n))"
| "Aexp (Lam [x]. e) = (\<Lambda> n . (Aexp e \<cdot> (pred \<cdot> n)  f|` (fv (Lam [x]. e))))"
| "Aexp (App e x) = (\<Lambda> n . Aexp e  \<cdot> (inc \<cdot> n) \<squnion> (esing x \<cdot> (up \<cdot> 0)))"
| "Aexp (Terms.Let as e) = (\<Lambda> n . (Afix Aexp as \<cdot> (Aexp e \<cdot> n \<squnion> thunks_AE as)) f|` (fv (Terms.Let as e)))"
| "Aexp (Bool b) = \<bottom>"
| "Aexp (scrut ? e1 : e2) = (\<Lambda> n. Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>n \<squnion> Aexp e2\<cdot>n)"
proof-
case goal1
    note Afix_eqvt[eqvt]
    show ?case
    unfolding eqvt_def Aexp_graph_aux_def
    apply rule
    apply (perm_simp)
    apply (simp add: Abs_cfun_eqvt)
    done
next
case goal3 thus ?case by (metis Terms.exp_strong_exhaust)
next
case (goal10 x e x' e')
  from goal10(5)
  show ?case
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set)" 
    {
    fix n
    have "Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)  f|` fv  (Lam [x]. e) = (-\<pi> \<bullet> Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (rule env_restr_perm[symmetric, OF *]) simp
    also have "\<dots> = ((Aexp_sumC e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (simp add: eqvt_at_apply[OF goal10(1)] pemute_minus_self)
    also note calculation
    }
    thus "(\<Lambda> n. Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)) = (\<Lambda> n. Aexp_sumC e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e))" by simp
  qed
next
case (goal19 as body as' body')
  note Afix_eqvt[eqvt]

  from goal19(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let as body) :: var set)"
    
    { fix n
      have "Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks_AE (\<pi> \<bullet> as)) f|` fv (Terms.Let as body)
      =  (- \<pi> \<bullet> Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks_AE (\<pi> \<bullet> as))) f|` fv (Terms.Let as body)"
        by (rule env_restr_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks_AE (\<pi> \<bullet> as)) = 
                       Afix (- \<pi> \<bullet> Aexp_sumC) as\<cdot>((- \<pi> \<bullet> Aexp_sumC) body\<cdot>n \<squnion> thunks_AE as)"
        by (simp add: pemute_minus_self)
      also have "Afix (- \<pi> \<bullet> Aexp_sumC) as = Afix Aexp_sumC as"
        by (rule Afix_cong[OF eqvt_at_apply[OF goal19(1)] refl])
      also have "(- \<pi> \<bullet> Aexp_sumC) body = Aexp_sumC body"
        by (rule eqvt_at_apply[OF goal19(2)])
      also note calculation
    }
    thus "(\<Lambda> n. Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks_AE (\<pi> \<bullet> as)) f|` fv (Terms.Let as body)) =
         (\<Lambda> n. Afix Aexp_sumC as\<cdot>(Aexp_sumC body\<cdot>n \<squnion> thunks_AE as) f|` fv (Terms.Let as body))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order
end


end
