theory CoCallFix
imports CoCallAnalysis CoCallAnalysisBinds ArityCorrect "Env-Nominal"  ArityAnalysisFix
begin

locale CoCallArityAnalysis =
  fixes cccExp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)"
begin
definition Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)" where "Aexp e = (\<Lambda> a. fst (cccExp e \<cdot> a))"
definition CCexp :: "exp \<Rightarrow> (Arity \<rightarrow> CoCalls)" where "CCexp \<Gamma> = (\<Lambda> a. snd (cccExp \<Gamma>\<cdot>a))"

sublocale ArityAnalysis Aexp.
sublocale CoCallAnalysis CCexp.

definition ABindsExtra :: "heap \<Rightarrow> CoCalls \<rightarrow> AEnv"
  where "ABindsExtra \<Gamma> = (\<Lambda> G. (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma> \<inter> ccManyCalls G))"

lemma ABindsExtra_simp: "ABindsExtra \<Gamma>\<cdot>G = (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma> \<inter> ccManyCalls G)" sorry

lemma ABindsExtra_strict[simp]: "ABindsExtra \<Gamma>\<cdot>\<bottom> = \<bottom>"
  unfolding ABindsExtra_simp by simp

lemma ABindsExtra_eq_up0[intro!]: "x \<in> thunks \<Gamma> \<inter> ccManyCalls G \<Longrightarrow> (ABindsExtra \<Gamma>\<cdot>G) x = up\<cdot>0"
  unfolding ABindsExtra_simp by (auto simp add: lookup_env_restr_eq)

(* This might work just as nicely:

context
  fixes \<Gamma> :: heap
begin
fixrec Afix :: "(AEnv \<times> CoCalls \<rightarrow> AEnv)" and CCfix :: " (AEnv \<times> CoCalls \<rightarrow> CoCalls)"
  where "Afix\<cdot>ae = ABinds \<Gamma>\<cdot>(Afix\<cdot>ae) \<squnion>  ABindsExtra \<Gamma>\<cdot>(CCfix\<cdot>ae) \<squnion> fst ae"
   |    "CCfix\<cdot>ae = ccBindsExtra \<Gamma>\<cdot>(Afix\<cdot>ae, CCfix\<cdot>ae) \<squnion> snd ae" 
end
lemmas Afix_unroll = Afix.simps[simp del]
lemmas CCfix_unroll = CCfix.simps[simp del]
*)


(*
definition cccFix ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
  where "cccFix \<Gamma> = (\<Lambda> i. (\<mu>  i'. (ABinds \<Gamma> \<cdot> (fst i') \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>), ccBindsExtra \<Gamma> \<cdot> i') \<squnion> i))"

definition Afix :: "heap \<Rightarrow> (AEnv \<times> CoCalls \<rightarrow> AEnv)"
  where "Afix e = (\<Lambda> ae. fst (cccFix e \<cdot> ae))"
*)

definition CCfix :: "heap \<Rightarrow> (AEnv \<times> CoCalls) \<rightarrow> CoCalls"
  where "CCfix \<Gamma> = (\<Lambda> aeG. (\<mu> G'. ccBindsExtra \<Gamma>\<cdot>(fst aeG , G') \<squnion> snd aeG))"

lemma CCfix_unroll: "CCfix \<Gamma>\<cdot>(ae,G) = ccBindsExtra \<Gamma>\<cdot>(ae, CCfix \<Gamma>\<cdot>(ae,G)) \<squnion> G"
  unfolding  CCfix_def
  apply simp
  apply (subst fix_eq)
  apply simp
  done

(*
lemma cccFix_least_below: "Binds \<Gamma> \<cdot> (fst ae') \<sqsubseteq> fst ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> cccFix \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding cccFix_eq
  by (auto intro: fix_least_below)

lemma Abinds_below_Afix: "ABinds \<Delta> \<sqsubseteq> Afix \<Delta>"
  apply (rule cfun_belowI)
  apply (simp add: Afix_eq)
  apply (subst fix_eq, simp)
  apply (rule below_trans[OF _ join_above1])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> ae"
  by (metis (hide_lams, no_types) Abinds_below_Afix ArityAnalysis.ABinds_above_arg below_refl box_below monofun_cfun_fun)


lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma>\<cdot>ae"
  unfolding Afix_eq
  apply (subst fix_eq) back apply simp
  apply (rule below_trans[OF ABinds_above_arg monofun_cfun_arg])
  apply (subst fix_eq) apply simp
  done

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)
*)

end

lemma Aexp_eqvt[eqvt]:  "\<pi> \<bullet> (CoCallArityAnalysis.Aexp cccExp e) = CoCallArityAnalysis.Aexp (\<pi> \<bullet> cccExp) (\<pi> \<bullet> e)"
  unfolding CoCallArityAnalysis.Aexp_def by perm_simp (simp_all add: Abs_cfun_eqvt)

lemma CCexp_eqvt[eqvt]:  "\<pi> \<bullet> (CoCallArityAnalysis.CCexp cccExp e) = CoCallArityAnalysis.CCexp (\<pi> \<bullet> cccExp) (\<pi> \<bullet> e)"
  unfolding CoCallArityAnalysis.CCexp_def by perm_simp (simp_all add: Abs_cfun_eqvt)

(*
lemma ABindsExtra_eqvt[eqvt]: "\<pi> \<bullet> CoCallArityAnalysis.ABindsExtra = ABindsExtra" sorry
lemma cccFix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix cccExp \<Gamma>) = CoCallArityAnalysis.cccFix  (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.cccFix_def
  by perm_simp (simp add: Abs_cfun_eqvt)

lemma Afix_eqvt[eqvt]:  "\<pi> \<bullet> (CoCallArityAnalysis.Afix cccExp \<Gamma>) = CoCallArityAnalysis.Afix (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.Afix_def by perm_simp (simp_all add: Abs_cfun_eqvt)
*)

lemma CCfix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.CCfix cccExp \<Gamma>) = CoCallArityAnalysis.CCfix (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.CCfix_def by perm_simp (simp_all add: Abs_cfun_eqvt)

(*
lemma cccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.cccFix cccexp1 heap1 = CoCallArityAnalysis.cccFix cccexp2 heap2"
   unfolding CoCallArityAnalysis.cccFix_def
   apply (rule cong) back back
   apply (rule cong[OF _ Abinds_cong])
   apply metis
   apply (simp add: CoCallArityAnalysis.Aexp_def)
   apply assumption
   apply (metis CoCallArityAnalysis.CCexp_def ccBindsExtra_cong)
   done
*)

lemma ccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.CCfix cccexp1 heap1 = CoCallArityAnalysis.CCfix cccexp2 heap2"
   unfolding CoCallArityAnalysis.CCfix_def
   apply (rule arg_cong) back
   apply (rule ccBindsExtra_cong)
   apply (auto simp add: CoCallArityAnalysis.CCexp_def)
   done


context CoCallArityAnalysis
begin
definition cccFix ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
  where "cccFix \<Gamma> = (\<Lambda> i. (Afix \<Gamma>\<cdot>(fst i \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>), CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(fst i  \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), snd i)))"
end

lemma cccFix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix cccExp \<Gamma>) = CoCallArityAnalysis.cccFix  (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.cccFix_def 
  by perm_simp (simp add: Abs_cfun_eqvt)


lemma cccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.cccFix cccexp1 heap1 = CoCallArityAnalysis.cccFix cccexp2 heap2"
   unfolding CoCallArityAnalysis.cccFix_def
   apply (rule cfun_eqI)
   apply auto
   apply (rule arg_cong[OF Afix_cong], auto simp add: CoCallArityAnalysis.Aexp_def)[1]
   apply (rule arg_cong2[OF ccFix_cong Afix_cong ])
   apply (auto simp add: CoCallArityAnalysis.Aexp_def)
   done

end
