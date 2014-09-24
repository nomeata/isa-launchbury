theory DeadCodeRemoval2CorrectSestoft
imports Sestoft DeadCodeRemoval2 SestoftCorrect LookAheadSim
begin

lemma isLam_remove_dead_code[simp]: "isLam e \<Longrightarrow> isLam (remove_dead_code e)"
  by (induction e rule:isLam.induct) auto

definition rdcH :: "var set \<Rightarrow> heap \<Rightarrow> heap"
  where "rdcH S \<Gamma> = restrictA (-S) (clearjunk (map_ran (\<lambda> _ e . remove_dead_code e) \<Gamma>))" 

lemma domA_rdcH[simp]: "domA (rdcH V \<Gamma>) = domA \<Gamma> - V"
  unfolding rdcH_def by auto

lemma delete_map_ran[simp]: "delete x (map_ran f \<Gamma>) = map_ran f (delete x \<Gamma>)"
  by (induction \<Gamma>) auto

lemma map_of_rdcH: "map_of (rdcH S \<Gamma>) x = (if x \<in> S then None else map_option remove_dead_code (map_of \<Gamma> x))"
  apply (induction \<Gamma> rule: clearjunk.induct)
  apply (auto simp add: rdcH_def map_of_clearjunk  split: if_splits)
  by (metis delete_map_ran map_of_delete)

lemma delete_rdcH[simp]: "delete x (rdcH S \<Gamma>) = rdcH S (delete x \<Gamma>)"
  by (induction \<Gamma> rule:clearjunk.induct) 
     (auto simp add: rdcH_def  delete_twist split: if_splits)

lemma map_ran_append[simp]: "map_ran f (\<Gamma>1 @ \<Gamma>2) = map_ran f \<Gamma>1 @ map_ran f \<Gamma>2"
  by (induction \<Gamma>1) auto

lemma restrictA_UNIV[simp]: "restrictA UNIV \<Gamma> = \<Gamma>"
  by (induction \<Gamma>) auto

lemma restrictA_delete[simp]: "restrictA S (delete x \<Gamma>) = restrictA (S - {x}) \<Gamma>"
  by (induction \<Gamma>) auto

lemma clearjunk_append: "clearjunk (\<Gamma>1 @ \<Gamma>2) = clearjunk \<Gamma>1 @ clearjunk (restrictA (-domA \<Gamma>1) \<Gamma>2)"
  by (induction \<Gamma>1 arbitrary: \<Gamma>2 rule:clearjunk.induct) (auto simp add: Compl_insert)

lemma restrictA_clearjunk: "restrictA S (clearjunk \<Gamma>) = clearjunk (restrictA S \<Gamma>)"
  by (induction \<Gamma>  rule:clearjunk.induct) (auto simp add: Compl_insert)

lemma restrictA_append[simp]: "restrictA S (\<Gamma>1 @ \<Gamma>2) = restrictA S \<Gamma>1 @ restrictA S \<Gamma>2"
  by (induction \<Gamma>1) auto

lemma rdcH_append[simp]: "domA as \<inter> domA \<Gamma> = {} \<Longrightarrow> rdcH S (as @ \<Gamma>) = rdcH S as @ rdcH S \<Gamma>"
  unfolding rdcH_def apply (simp add: clearjunk_append restrictA_clearjunk)
  apply (rule arg_cong) back
  apply (rule restrictA_cong)
  apply auto
  done

lemma restrict_is_nil[simp]: "restrictA S \<Gamma> = [] \<longleftrightarrow> S \<inter> domA \<Gamma> = {}"
  by (induction \<Gamma>) auto

lemma rdcH_nil[simp]: "rdcH S [] = []"
  by (auto simp add: rdcH_def)

lemma rdcH_is_nil: "domA \<Gamma> \<subseteq> S \<Longrightarrow> rdcH S \<Gamma> = []"
  by (auto simp add: rdcH_def)

lemma rdcH_cong_set: "S \<inter> domA \<Gamma> = S' \<inter> domA \<Gamma> \<Longrightarrow> rdcH S \<Gamma> = rdcH S' \<Gamma>"
  unfolding rdcH_def by (rule restrictA_cong) auto

lemma rdcH_eqvt[eqvt]: "\<pi> \<bullet> (rdcH V \<Gamma>) = rdcH (\<pi> \<bullet> V) (\<pi> \<bullet> \<Gamma>)"
  unfolding rdcH_def by perm_simp rule

lemma rdch_fresh[intro]: "a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> rdcH V \<Gamma>"
  by (induction \<Gamma> rule: clearjunk.induct)
     (auto simp add:  rdcH_def fresh_Nil fresh_Pair fresh_Cons  eqvt_fresh_cong1[OF remove_dead_code.eqvt] fresh_delete)

lemma rdch_fv_subset: "fv (rdcH V \<Gamma>) \<subseteq> fv \<Gamma>"
  using rdch_fresh unfolding fresh_def fv_def by auto

lemma rdch_Cons[simp]:
  "x \<notin> V \<Longrightarrow> rdcH V ((x, z) # \<Gamma>) = (x, remove_dead_code z) # rdcH V (delete x \<Gamma>)"
  unfolding rdcH_def
  by (auto simp add: clearjunk_restrict[symmetric] delete_map_ran[symmetric] simp del: delete_map_ran)

inductive dc_rel :: "(heap \<times> exp \<times> stack) \<Rightarrow> (heap \<times> exp \<times> stack) \<Rightarrow>  bool" ("_ \<triangleright> _" [50,50] 50 )
  where "V \<subseteq> domA \<Gamma> \<union> fv S \<Longrightarrow> V \<inter> fv (rdcH V \<Gamma>, remove_dead_code e, S) = {} \<Longrightarrow> (\<Gamma>, e, S) \<triangleright> (rdcH V \<Gamma>, remove_dead_code e, S)"

inductive_cases dc_rel_elim: "(\<Gamma>, e, S) \<triangleright> (\<Gamma>', e', S')"

lemma dc_relI: "V \<subseteq> domA \<Gamma> \<union> fv S \<Longrightarrow> V \<inter> fv (rdcH V \<Gamma>, remove_dead_code e, S) = {} \<Longrightarrow> \<Gamma>' = rdcH V \<Gamma> \<Longrightarrow> e' = remove_dead_code e \<Longrightarrow> S' = S \<Longrightarrow>  (\<Gamma>, e, S) \<triangleright> (\<Gamma>', e', S')"
  by (auto intro!: dc_rel.intros)


lemma disjoint_mono: "A \<inter> B = {} \<Longrightarrow>  A' \<subseteq> A \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> A' \<inter> B' = {}" by auto
lemma disjoint_Un1: "(A \<union> B) \<inter> C = {} \<longleftrightarrow> A \<inter> C = {} \<and> B \<inter> C = {} " by auto
lemma disjoint_Un2: "C \<inter> (A \<union> B) = {} \<longleftrightarrow> C \<inter> A = {} \<and> C \<inter> B = {} " by auto

lemma isLam_SmartLet[simp]: "isLam (SmartLet \<Gamma> e) \<longleftrightarrow> \<Gamma> = [] \<and> isLam e"
  unfolding SmartLet_def by auto

lemma SmartLet_Nil[simp]: "SmartLet [] e = e"
  unfolding SmartLet_def by auto
(*
lemma remove_dead_code_eventually:
  assumes "isLam (remove_dead_code z)"
  shows "eventually (\<lambda> (\<Gamma>', z', S) . remove_dead_code z = remove_dead_code z' \<and> restrict_reachable (map_ran (\<lambda>_. remove_dead_code) \<Gamma>') (remove_dead_code z') = restrict_reachable (map_ran (\<lambda>_. remove_dead_code) \<Gamma>) (remove_dead_code z') \<and>  isLam z') op \<Rightarrow> (\<Gamma>, z, S)"
    (is "?t \<Gamma> z S")
using assms
apply(nominal_induct z avoiding: \<Gamma> S rule:exp_strong_induct)
apply auto
apply (rule laterI)
apply rule
apply assumption
apply assumption
apply (erule step.cases)
apply auto[5]
apply (auto simp del: Let_eq_iff)
proof-
  case (goal1 \<Gamma> exp \<Delta> \<Gamma>'' S e)
  have "?t (\<Delta> @ \<Gamma>'') e S" sorry
  moreover
  from `_ = []`
  have "restrict_reachable (map_ran (\<lambda>_. remove_dead_code) \<Delta>) (remove_dead_code e) = []"
    sorry
  ultimately
  show ?case apply simp

lemma remove_dead_code_eventually:
  assumes "isLam (remove_dead_code z)"
  assumes "(\<Gamma>, z, S) \<triangleright> c'"
  shows "eventually (\<lambda>c . c \<triangleright> c') op \<Rightarrow> (\<Gamma>, z, S)"
using assms
apply(nominal_induct z avoiding: \<Gamma> S rule:exp_strong_induct)
apply auto
apply (rule laterI)
apply rule
apply assumption
apply assumption
apply (erule step.cases)
apply auto[5]
*)


theorem DeadCodeRemovalCorrectStep:
  assumes "(\<Gamma>, e, S) \<Rightarrow> (\<Delta>, z, T)"
  assumes "(\<Gamma>, e, S) \<triangleright> (\<Gamma>', e', S')"
  shows  "\<exists> \<Delta>' z' T'. (\<Delta>, z, T) \<triangleright> (\<Delta>', z', T') \<and> (\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Delta>', z', T')"
using assms(2)
proof(rule dc_rel_elim)
  fix V
  assume V\<^sub>1: "V \<subseteq> domA \<Gamma> \<union> fv S"
  assume V\<^sub>2: "V \<inter> (fv (rdcH V \<Gamma>) \<union> (fv (remove_dead_code e) \<union> fv S)) = {}"
  assume eqs: "\<Gamma>' = rdcH V \<Gamma>" "e' = remove_dead_code e" "S' = S"

  have "\<exists> \<Delta>' z' T'. (\<Delta>, z, T) \<triangleright> (\<Delta>', z', T') \<and> (rdcH V \<Gamma>, remove_dead_code e, S) \<Rightarrow>\<^sup>* (\<Delta>', z', T')"
  using assms(1)
  proof(cases rule: step.cases)
  case (app\<^sub>1 x)
    from V\<^sub>1 V\<^sub>2
    have "(\<Gamma>, z, Arg x # S) \<triangleright> (rdcH V \<Gamma>, remove_dead_code z, Arg x # S)"
      unfolding app\<^sub>1  by -(rule dc_relI[where V = V], auto)
    moreover
    have "(rdcH V \<Gamma>, remove_dead_code (App z x), S) \<Rightarrow> (rdcH V \<Gamma>, remove_dead_code z, Arg x # S)"
      by simp rule
    ultimately
    show ?thesis unfolding app\<^sub>1 by blast
  next
  case (app\<^sub>2 y e' x)
    from V\<^sub>1 V\<^sub>2
    have "(\<Gamma>, e'[y::=x], T) \<triangleright> (rdcH V \<Gamma>, remove_dead_code (e'[y::=x]), T)"
      unfolding app\<^sub>2 eqs by -(rule dc_relI[where V = V], auto simp add: fv_subst_eq subst_remove_dead_code[symmetric])
    moreover
    have "(rdcH V \<Gamma>, remove_dead_code (Lam [y]. e'), Arg x # T) \<Rightarrow> (rdcH V \<Gamma>, remove_dead_code (e'[y::=x]), T)"
      by (simp add: subst_remove_dead_code[symmetric]) rule
    ultimately
    show ?thesis unfolding app\<^sub>2 by blast
  next
  case (var\<^sub>1 x)
    from V\<^sub>2 var\<^sub>1 `map_of \<Gamma> x = Some z`  have "x \<notin> V" by auto

    from `map_of \<Gamma> x = Some z` and `x \<notin> V`
    have "map_of (rdcH V \<Gamma>) x = Some (remove_dead_code z)" by (auto simp add: map_of_rdcH)

    have *: "\<And> S . fv (rdcH S (delete x \<Gamma>)) \<subseteq> fv (rdcH S \<Gamma>)" by (metis delete_rdcH fv_delete_subset)

    from `map_of (rdcH V \<Gamma>) x = Some (remove_dead_code z)`
    have **: "fv (remove_dead_code z) \<subseteq> fv (rdcH V \<Gamma>)" by (metis domA_from_set map_of_fv_subset map_of_is_SomeD option.sel)

    from V\<^sub>1 V\<^sub>2
    have "(delete x \<Gamma>, z, Upd x # S) \<triangleright> (rdcH V (delete x \<Gamma>), remove_dead_code z, Upd x # S)"
      unfolding var\<^sub>1(1)
      by -(rule dc_relI[where V = V], auto dest: set_mp[OF *] set_mp[OF **])
    moreover
    from  `map_of (rdcH V \<Gamma>) x = Some (remove_dead_code z)`
    have "(rdcH V \<Gamma>, remove_dead_code (Var x), S) \<Rightarrow> (rdcH V (delete x \<Gamma>), remove_dead_code z, Upd x # S)"
      by (simp add: delete_rdcH[symmetric] del: delete_rdcH) rule
    ultimately
    show ?thesis unfolding var\<^sub>1 by blast
  next
  case (var\<^sub>2 x)
    with V\<^sub>2 have [simp]: "x \<notin> V" by auto
    with `x \<notin> domA \<Gamma>`
    have  "rdcH V ((x, z) # \<Gamma>) = (x,remove_dead_code z) # rdcH V \<Gamma>" by simp

    note `x \<notin> domA \<Gamma>` [simp] and `isLam e` [simp]


    from V\<^sub>1 V\<^sub>2
    have "((x, e) # \<Gamma>, e, T) \<triangleright> ((x,remove_dead_code e) # rdcH V \<Gamma>, remove_dead_code e, T)"
      unfolding var\<^sub>2(1-1)
      by -(rule dc_relI[where V = V], auto)
    moreover
    have "(rdcH V \<Gamma>, remove_dead_code e, Upd x # T) \<Rightarrow> ((x,remove_dead_code e) # rdcH V \<Gamma>, remove_dead_code e, T)"
      by rule simp_all
    ultimately
    show ?thesis unfolding eqs var\<^sub>2 by blast
  next
  case (let\<^sub>1 \<Delta>)
    let "(?\<Delta>', ?body')" = "((restrict_reachable (map_ran (\<lambda>_. remove_dead_code) \<Delta>) (remove_dead_code z)), (remove_dead_code z))"
    let "?V'" = "domA \<Delta> - reachable (map_ran (\<lambda>_. remove_dead_code) \<Delta>) ?body'"

    from fresh_distinct[OF let\<^sub>1(4)] fresh_distinct_fv[OF let\<^sub>1(5)] V\<^sub>1
    have "V \<inter> domA \<Delta> = {}" by blast
    hence [simp]: "(rdcH (?V' \<union> V) \<Delta>) = ?\<Delta>'"
      unfolding restrict_reachable_def rdcH_def
      by -(rule restrictA_cong,  auto)
    
    have [simp]: "(rdcH (?V' \<union> V) \<Gamma>) = (rdcH V \<Gamma>)"
      using fresh_distinct[OF let\<^sub>1(4)]
      by (auto intro: rdcH_cong_set simp add: fresh_star_at_base)

    have "?V' \<union> V \<subseteq> domA (\<Delta> @ \<Gamma>) \<union> fv S" using V\<^sub>1 by auto
    moreover
    {
    have "?V' \<inter> fv ?\<Delta>' = {}" using fv_heap_reachable by auto
    moreover
    have "?V' \<inter> fv \<Gamma> = {}"
      using let\<^sub>1(4) by (auto simp add: fresh_star_def fresh_def fv_def)
    hence "?V' \<inter> fv (rdcH V \<Gamma>) = {}"
      by (rule disjoint_mono[OF _ subset_refl rdch_fv_subset])
    moreover
    have "?V' \<inter> fv ?body' = {}" using fv_e_reachable by auto
    moreover
    have "?V' \<inter> fv S = {}" using fresh_distinct_fv[OF let\<^sub>1(5)] by auto
    moreover
    have "V \<inter> fv ?\<Delta>' = {}" using V\<^sub>2 `V \<inter> domA \<Delta> = {}` unfolding let\<^sub>1 by auto
    moreover
    have "V \<inter> fv (rdcH V \<Gamma>) = {}" using V\<^sub>2 by auto
    moreover
    have "V \<inter> fv ?body' = {}" using V\<^sub>2  `V \<inter> domA \<Delta> = {}` unfolding let\<^sub>1 by auto
    moreover
    have "V \<inter> fv S = {}"  using V\<^sub>2 by auto
    ultimately
    have "(?V' \<union> V) \<inter> fv (rdcH (?V' \<union> V) (\<Delta> @ \<Gamma>), ?body', S) = {}"
      using fresh_distinct[OF let\<^sub>1(4)] by auto
    }
    ultimately
    have "(\<Delta> @ \<Gamma>, z, S) \<triangleright> (rdcH (?V' \<union> V) (\<Delta> @ \<Gamma>), ?body', S)"..
    also
    have "atom ` domA ?\<Delta>' \<sharp>* rdcH V \<Gamma>" and  "atom ` domA ?\<Delta>' \<sharp>* S"
      using let\<^sub>1(4,5) by (auto simp add: fresh_star_def fresh_Pair)
    from SmartLet_stepI[OF this]
    have "(rdcH V \<Gamma>, remove_dead_code (Terms.Let \<Delta> z), S) \<Rightarrow>\<^sup>* (rdcH (?V' \<union> V) (\<Delta> @ \<Gamma>), ?body', S)"
      using fresh_distinct[OF let\<^sub>1(4)] by simp
    ultimately
    show ?thesis unfolding let\<^sub>1 by blast
  qed
  thus ?thesis unfolding eqs.
qed

theorem DeadCodeRemovalCorrectSteps:
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, T)"
  assumes "(\<Gamma>, e, S) \<triangleright> (\<Gamma>', e', S')"
  shows  "\<exists> \<Delta>' z' T'. (\<Delta>, z, T) \<triangleright> (\<Delta>', z', T') \<and> (\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Delta>', z', T')"
using assms
  by (induction rule: rtranclp_induct)(fastforce dest: DeadCodeRemovalCorrectStep)+

corollary
  assumes "[] : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
   shows  "\<exists> \<Delta>' z'. [] : remove_dead_code e \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
proof-
  let "?S" = "map Dummy L"
  have *: "set (map Dummy L) \<subseteq> range Dummy" by auto

  have "L = flattn ?S" by (induction L) auto
  from lemma_2[OF assms(1) this]
  have "([], e, ?S) \<Rightarrow>\<^sup>* (\<Delta>, z, ?S)".
  moreover
  have "([], e, ?S) \<triangleright> (rdcH {} [], remove_dead_code e, ?S)" by (rule dc_rel.intros) auto
  hence "([], e, ?S) \<triangleright> ([], remove_dead_code e, ?S)" by simp
  ultimately
  obtain \<Delta>' z' T' where "(\<Delta>, z, ?S) \<triangleright> (\<Delta>', z', T')" and "([], remove_dead_code e, ?S) \<Rightarrow>\<^sup>* (\<Delta>', z', T')"
    by (metis DeadCodeRemovalCorrectSteps)
  hence "([], remove_dead_code e, ?S) \<Rightarrow>\<^sup>* (\<Delta>', remove_dead_code z, ?S)" by (auto elim: dc_rel.cases)
  from dummy_stack_balanced[OF * this]
  obtain T where "bal ([], remove_dead_code e, map Dummy L) T (\<Delta>', remove_dead_code z, map Dummy L)".
  moreover
  have "isLam z" using assms(1) by (induction) simp
  hence "isLam (remove_dead_code z)" by (rule isLam_remove_dead_code)
  ultimately
  have "[] : remove_dead_code e \<Down>\<^bsub>flattn ?S\<^esub> \<Delta>' : remove_dead_code z"
    by (rule lemma_3)
  also have "flattn ?S = L" by (induction L) auto
  finally
  show ?thesis by blast
qed

end
