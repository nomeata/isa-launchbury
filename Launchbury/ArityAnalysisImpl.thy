theory ArityAnalysisImpl
imports ArityCorrect "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin

(*
locale CorrectArityAnalysis = ArityAnalysis +
  assumes Aexp_Var: "Aexp (Var x) \<cdot> n = AE_singleton x \<cdot> (up \<cdot> n)"
  assumes Aexp_subst_App_Lam: "Aexp (e'[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_Let: "Afix as\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Aexp (Terms.Let as e)\<cdot>n"
  assumes Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
begin
*)

nominal_function
  Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)"
where
  "Aexp (Var x) = (\<Lambda> n . AE_singleton x \<cdot> (up \<cdot> n))"
| "Aexp (Lam [x]. e) = (\<Lambda> n . (Aexp e \<cdot> (pred \<cdot> n)  f|` (fv (Lam [x]. e))))"
| "Aexp (App e x) = (\<Lambda> n . Aexp e  \<cdot> (inc \<cdot> n) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)))"
| "Aexp (Terms.Let as e) = (\<Lambda> n . (ArityAnalysis.Afix Aexp as \<cdot> (Aexp e \<cdot> n)) f|` (fv (Terms.Let as e)))"
proof-
case goal1 show ?case
    unfolding eqvt_def Aexp_graph_aux_def
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
    have "Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)  f|` fv  (Lam [x]. e) = (-\<pi> \<bullet> Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (rule env_restr_perm[symmetric, OF *]) simp
    also have "\<dots> = ((Aexp_sumC e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (simp add: eqvt_at_apply[OF goal8(1)] pemute_minus_self)
    also note calculation
    }
    thus "(\<Lambda> n. Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)) = (\<Lambda> n. Aexp_sumC e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e))" by simp
  qed
next
case (goal13 as body as' body')
  from goal13(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let as body) :: var set)"
    
    { fix n
      have "ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) f|` fv (Terms.Let as body)
      =  (- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n)) f|` fv (Terms.Let as body)"
        by (rule env_restr_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) = 
                       ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as\<cdot>((- \<pi> \<bullet> Aexp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as = ArityAnalysis.Afix Aexp_sumC as"
        by (rule Afix_cong[OF eqvt_at_apply[OF goal13(1)]])
      also have "(- \<pi> \<bullet> Aexp_sumC) body = Aexp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) f|` fv (Terms.Let as body)) =
         (\<Lambda> n. ArityAnalysis.Afix Aexp_sumC as\<cdot>(Aexp_sumC body\<cdot>n) f|` fv (Terms.Let as body))" by (simp only:)
  qed
qed auto

nominal_termination by lexicographic_order



lemma edom_join[simp]: "edom (f \<squnion> g) = edom f \<union> edom g" sorry

lemma edom_Afix: "(\<And>ea. ea \<in> snd ` set as \<Longrightarrow> \<forall>n. edom (Aexp_sum ea\<cdot>n) \<subseteq> fv ea) \<Longrightarrow>
   edom (ArityAnalysis.Afix Aexp_sum as\<cdot>x) \<subseteq> edom x \<union> \<Union>{ fv e | e.  e \<in> snd ` set as}"
   sorry




(*
lemma Aexp_fresh_bot[simp]: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
  apply (nominal_induct avoiding: v arbitrary: a  rule: exp_strong_induct)
  apply auto[1]
  apply auto[1]
  defer
  apply auto[1]
  apply auto[1]
  defer
  apply (metis (mono_tags, hide_lams) bn_subst domA_not_fresh fresh_at_base(2) obtain_fresh subst_is_fresh(2))
  sorry

lemma pred_inc[simp]: "pred\<cdot>(inc\<cdot>n) = n" sorry

lemma Aexp_subst_other: "z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> (Aexp e'[y::=x]\<cdot>n) z \<sqsubseteq> (Aexp e'\<cdot>n) z"
apply (nominal_induct avoiding: x y z  arbitrary: n rule: exp_strong_induct)
apply auto[1]
apply (simp add: join_mono)
defer
apply auto[1]
sorry

interpretation CorrectArityAnalysis Aexp
proof default
  fix e' y x
  show "Aexp e'[y::=x] \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  proof (rule cfun_belowI[OF fun_belowI])
    fix n z
    { assume "z = x"
      hence "(Aexp e'[y::=x]\<cdot>n) z \<sqsubseteq> (Aexp (App (Lam [y]. e') x)\<cdot>n) z" by simp
    } moreover {
      assume "z \<noteq> x" and "z = y"
      hence "(Aexp e'[y::=x]\<cdot>n) z \<sqsubseteq> (Aexp (App (Lam [y]. e') x)\<cdot>n) z" by simp
    } moreover {
      assume "z \<noteq> x" and "z \<noteq> y"
      hence "(Aexp e'[y::=x]\<cdot>n) z \<sqsubseteq> (Aexp (App (Lam [y]. e') x)\<cdot>n) z" by (simp add: Aexp_subst_other)
    }
    ultimately show "(Aexp e'[y::=x]\<cdot>n) z \<sqsubseteq> (Aexp (App (Lam [y]. e') x)\<cdot>n) z" by blast
  qed
qed simp_all
*)
end
