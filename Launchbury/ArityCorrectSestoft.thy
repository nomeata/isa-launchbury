theory ArityCorrectSestoft
imports ArityCorrect SestoftCorrect
begin

fun Astack :: "AEnv \<Rightarrow> stack \<Rightarrow> Arity"
  where "Astack ae [] = 0"
      | "Astack ae (Arg x # S) = inc\<cdot>(Astack ae S)"
      | "Astack ae (Upd x # S) = (case ae x of Iup a \<Rightarrow> a)"
      | "Astack ae (Dummy x # S) = 0"

lemma Astack_cong: "(\<And> x. x \<in> upds S \<Longrightarrow> ae x = ae' x) \<Longrightarrow>  Astack ae S = Astack ae' S"
  by (induction S  rule: Astack.induct) auto

lemma Astack_Upd_simps[simp]:
  "ae x = up\<cdot>u \<Longrightarrow> Astack ae (Upd x # S) = u"
  by (simp add: up_def cont_Iup)
declare Astack.simps(3)[simp del]


fun AEstack :: "AEnv \<Rightarrow> stack \<Rightarrow> AEnv"
  where "AEstack ae [] = \<bottom>"
      | "AEstack ae (Arg x # S) = AE_singleton x \<cdot> (up\<cdot>0) \<squnion> AEstack ae S"
      | "AEstack ae (Upd x # S) = AE_singleton x \<cdot> (up\<cdot>(Astack ae S)) \<squnion> AEstack ae S"
      | "AEstack ae (Dummy x # S) = AEstack ae S"

lemma AEstack_cong: "(\<And> x. x \<in> upds S \<Longrightarrow> ae x = ae' x) \<Longrightarrow> AEstack ae S = AEstack ae' S"
  by (induction S  rule: upds.induct) (auto cong: Astack_cong)

context CorrectArityAnalysisAheap
begin

inductive AE_consistent :: "AEnv \<Rightarrow> conf \<Rightarrow> bool" where
  AE_consistentI: 
  "edom ae \<subseteq> domA \<Gamma> \<union> upds S
  \<Longrightarrow> upds S \<subseteq> edom ae
  \<Longrightarrow> AEstack ae S \<sqsubseteq> ae 
  \<Longrightarrow> Aexp e \<cdot> (Astack ae S) \<sqsubseteq> ae
  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> Aexp' e \<cdot> (ae x) \<sqsubseteq> ae)
  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ae x = up\<cdot>0)
  \<Longrightarrow> ae ` upds S \<subseteq> {up\<cdot>0}
  \<Longrightarrow> AE_consistent ae (\<Gamma>, e, S)"

inductive_cases AE_consistentE[elim]: "AE_consistent ae (\<Gamma>, e, S)"

theorem
  assumes "(\<Gamma>, e, S) \<Rightarrow> (\<Delta>, v, S')"
  assumes "AE_consistent ae (\<Gamma>, e, S)"
  shows "\<exists> ae'. ae' f|` (-((domA \<Delta> \<union> upds S') - (domA \<Gamma> \<union> upds S))) = ae \<and> AE_consistent ae' (\<Delta>, v, S')"
using assms
proof(induction "(\<Gamma>, e, S)" "(\<Delta>, v, S')"  arbitrary: \<Gamma> e S \<Delta> v S' rule: step.inducts)
case (app\<^sub>1 \<Gamma> e x S)
  hence "AE_consistent ae (\<Gamma>, e, Arg x # S)"  by (fastforce elim!: AE_consistentE intro!: AE_consistentI simp add: Aexp_App join_below_iff)
  thus ?case by simp
next
case (app\<^sub>2 \<Gamma> y e x S)
  hence "AE_consistent ae (\<Gamma>, e[y::=x], S)" 
    by (fastforce elim!: AE_consistentE intro!: AE_consistentI  below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]] simp add: Aexp_App join_below_iff)
  thus ?case by simp
next
case (var\<^sub>1 \<Gamma> x e S)
  from `map_of \<Gamma> x = Some e`
  have "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
  hence *: "(domA (delete x \<Gamma>) \<union> upds (Upd x # S) - (domA \<Gamma> \<union> upds S)) = {}" using `x \<in> domA \<Gamma>` by auto
  
  from var\<^sub>1 have "Aexp (Var x)\<cdot>(Astack ae S) \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto
  moreover
  hence "x \<in> edom ae" unfolding edom_def by auto
  ultimately
  have "AE_consistent ae (delete x \<Gamma>, e, Upd x # S)" using var\<^sub>1 by (fastforce intro!: AE_consistentI  simp add: join_below_iff)
  thus ?case unfolding * by simp
next
case (var\<^sub>2 \<Gamma> x e S)
  from `map_of \<Gamma> x = Some e`
  have "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
  hence *: "(domA ((x,e) # delete x \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S)) = {}" using `x \<in> domA \<Gamma>` by auto
  
  
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
  thus ?case unfolding * by simp
next
case (var\<^sub>3 x \<Gamma> e S)
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x" using var\<^sub>3 by (auto simp add: join_below_iff)
  then obtain u where "ae x = up \<cdot> u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto

  from this(2)
  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> Aexp e\<cdot>u" by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> u` var\<^sub>3 by auto
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ae" by this simp
  hence "AE_consistent ae ((x, e) # \<Gamma>, e, S)" using var\<^sub>3 `ae x = up \<cdot> u`
    by (fastforce intro!: AE_consistentI  simp add: join_below_iff split:if_splits)+
  thus ?case by simp
next
case (let\<^sub>1 \<Delta> \<Gamma> S e)
  let ?ae = "Aheap \<Delta> \<cdot> (Aexp e\<cdot>(Astack ae S))"
  let ?new = "(domA (\<Delta> @ \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S))"
  have new: "?new = domA \<Delta>"
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (auto dest: set_mp[OF ups_fv_subset])

  have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: set_mp[OF ups_fv_subset])
  hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)))"
    using edom_Aheap[where \<Gamma> = \<Delta> and ae = "Aexp e\<cdot>(Astack ae S)"] by auto
  hence stack: "AEstack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)) \<squnion> ae) S = AEstack ae S"
               "Astack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)) \<squnion> ae) S = Astack ae S"
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
  have "AEstack ae S \<sqsubseteq> ?ae \<squnion> ae"
    by (rule AE_consistentE[OF let\<^sub>1(3)])
       (metis "join_above1" below_refl box_below join_comm)
  moreover
  {
  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> (Aexp e\<cdot>(Astack ae S) f|` domA \<Delta>) \<squnion> (Aexp e\<cdot>(Astack ae S) f|` (- domA \<Delta>))"
    by (rule eq_imp_below[OF join_env_restr_UNIV[symmetric]]) auto
  also have "Aexp e\<cdot>(Astack ae S) f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S)" by (rule Aexp_Let_above)
  also have "\<dots> \<sqsubseteq> ae" by (rule AE_consistentE[OF let\<^sub>1(3)])
  also have "Aexp e\<cdot>(Astack ae S) f|` domA \<Delta> \<sqsubseteq> ?ae" by (rule Aheap_above_arg)
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ?ae \<squnion> ae" by this auto
  }
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
    have "Aexp' e'\<cdot>(?ae x) f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S)" by (rule Aheap_heap2)
    also
    have "Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S) \<sqsubseteq> ae"  by (rule AE_consistentE[OF let\<^sub>1(3)])
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
  ultimately
  have "AE_consistent (?ae \<squnion> ae) (\<Delta> @ \<Gamma>, e, S) "
    by (auto intro!: AE_consistentI simp add: stack)
  }
  ultimately
  show ?case unfolding new by auto
qed
end

end
