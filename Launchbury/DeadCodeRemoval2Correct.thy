theory DeadCodeRemoval2Correct
imports Launchbury LaunchburyAbstractTransformation DeadCodeRemoval2
begin

definition rdcH :: "var set \<Rightarrow> heap \<Rightarrow> heap"
  where "rdcH S \<Gamma> = restrictA (-S) (clearjunk (map_ran (\<lambda> _ e . remove_dead_code e) \<Gamma>))" 

inductive dc_rel :: "(heap \<times> exp) \<Rightarrow> var list \<Rightarrow> (heap \<times> exp) \<Rightarrow>  bool" ("_ \<triangleright>\<^bsub>_\<^esub> _" [50,50,50] 50 )
  where "S \<subseteq> domA \<Gamma> \<union> set L \<Longrightarrow> S \<inter> fv (rdcH S \<Gamma>, remove_dead_code e, L) = {} \<Longrightarrow> (\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (rdcH S \<Gamma>, remove_dead_code e)"

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

interpretation rel_lambda_cong dc_rel
  by default (auto elim!: dc_rel.cases simp del: exp_assn.eq_iff(4))
interpretation rel_app_cong dc_rel
  by default (auto elim: dc_rel.cases)
interpretation rel_var_cong dc_rel
  by default (auto elim: dc_rel.cases)

lemma rdcH_eqvt[eqvt]: "\<pi> \<bullet> (rdcH S \<Gamma>) = rdcH (\<pi> \<bullet> S) (\<pi> \<bullet> \<Gamma>)"
  unfolding rdcH_def by perm_simp rule

lemma rdch_fresh[intro]: "a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> rdcH S \<Gamma>"
  by (induction \<Gamma> rule: clearjunk.induct)
     (auto simp add:  rdcH_def fresh_Nil fresh_Pair fresh_Cons  eqvt_fresh_cong1[OF remove_dead_code.eqvt] fresh_delete)

lemma rdch_fv_subset: "fv (rdcH S \<Gamma>) \<subseteq> fv \<Gamma>"
  using rdch_fresh unfolding fresh_def fv_def by auto

lemma rdch_Cons[simp]:
  "x \<notin> S \<Longrightarrow> rdcH S ((x, z) # \<Gamma>) = (x, remove_dead_code z) # rdcH S (delete x \<Gamma>)"
  unfolding rdcH_def
  by (auto simp add: clearjunk_restrict[symmetric] delete_map_ran[symmetric] simp del: delete_map_ran)

interpretation reds_rel_fresh dc_rel
  by default (auto elim!: dc_rel.cases intro: eqvt_fresh_cong1[OF remove_dead_code.eqvt])

interpretation rel_lambda_case dc_rel by default

lemma Lam_eq_same_var[simp]: "Lam [y]. e = Lam [y]. e' \<longleftrightarrow>  e = e'"
  by auto (metis fresh_PairD(2) obtain_fresh)

interpretation rel_app_case dc_rel
proof
  fix \<Gamma> e x L \<Gamma>' e''
  assume "(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', App e'' x)"
  thus "(\<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e'')" 
    by (fastforce elim!: dc_rel.cases intro!: dc_rel.intros)
next
  fix \<Gamma> y body x L \<Gamma>' body'
  assume "(\<Gamma>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', Lam [y]. body')"
  thus "(\<Gamma>, body[y::=x]) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', body'[y::=x])"
    apply (auto elim!: dc_rel.cases intro!: dc_rel.intros dest: set_mp  simp del: exp_assn.eq_iff(4) simp add: subst_remove_dead_code disjoint_iff_not_equal fv_subst_eq split: if_splits)
    apply (auto simp add: subst_remove_dead_code[symmetric] fv_subst_eq  split: if_splits)
    done
qed

interpretation rel_var_case dc_rel
proof
  case (goal1 \<Gamma> x L \<Gamma>' e thesis)
  show thesis
  proof (rule goal1)

    from goal1(1)
    obtain S where "\<Gamma>' = rdcH S \<Gamma>"
      and "S \<subseteq> domA \<Gamma> \<union> set L" and "S \<inter> fv (rdcH S \<Gamma>, Var x, L) = {}" by (auto elim!: dc_rel.cases)
    hence "x \<notin> S" by auto

    from `map_of \<Gamma> x = Some e` and `\<Gamma>' = _` and `x \<notin> S`
    show "map_of \<Gamma>' x = Some (remove_dead_code e)" by (auto simp add: map_of_rdcH)

    have *: "\<And> S . fv (rdcH S (delete x \<Gamma>)) \<subseteq> fv (rdcH S \<Gamma>)" by (metis delete_rdcH fv_delete_subset)

    from `map_of \<Gamma>' x = Some (remove_dead_code e)`
    have **: "fv (remove_dead_code e) \<subseteq> fv \<Gamma>'" by (metis domA_from_set map_of_fv_subset map_of_is_SomeD option.sel)

    from goal1(1)
    show "(delete x \<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (delete x \<Gamma>', remove_dead_code e)"
      by (fastforce elim!: dc_rel.cases intro!: dc_rel.intros dest: set_mp[OF *]  set_mp[OF **]  simp add: disjoint_iff_not_equal)
  qed
next
  fix \<Gamma> z x L \<Gamma>' z'
  assume "(\<Gamma>, z) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', z')"
  then obtain S where "\<Gamma>' = rdcH S \<Gamma>" and "z' = remove_dead_code z"
      and "S \<subseteq> insert x (domA \<Gamma> \<union> set L)" and "S \<inter> fv (rdcH S \<Gamma>, remove_dead_code z, x # L) = {}" by (auto elim!: dc_rel.cases)

  from this(4)
  have "x \<notin> S" by auto
  moreover
  assume "x \<notin> domA \<Gamma>"
  ultimately
  have [simp]: "rdcH S ((x, z) # \<Gamma>) = (x,remove_dead_code z) # rdcH S \<Gamma>" by simp

  have  "((x, z) # \<Gamma>, z) \<triangleright>\<^bsub>L\<^esub> (rdcH S ((x, z) # \<Gamma>), remove_dead_code z)"
    apply (rule dc_rel.intros) using `S \<subseteq>  _` `S \<inter> _ = _`  by auto
  thus "((x, z) # \<Gamma>, z) \<triangleright>\<^bsub>L\<^esub> ((x, z') # \<Gamma>', z')"
    unfolding `\<Gamma>' = _` `z' = _` by auto
qed

locale let_removed = 
  fixes \<Gamma> as body
  assumes "domA as \<inter> fv body = {} "


lemma map_fst_map_ran[simp]: "map fst (map_ran f l) = map fst l" by (induction l) auto

lemma permute_list_id: "supp p \<subseteq> set xs \<Longrightarrow>  p \<bullet> xs = xs \<Longrightarrow> p = 0"
proof (induction xs)
  case Nil
  hence "supp p = {}" by auto
  thus "p = 0" by (metis empty_subsetI supp_perm_singleton)
next
  case (Cons x xs)
  hence "p \<bullet> x = x" by auto
  hence "x \<notin> supp p" by (metis fresh_def fresh_perm)
  with Cons show "p = 0" by auto
qed

lemma Abs_lst_same[simp]: "[xs]lst. (y::'a::fs) = [xs]lst. y' \<longleftrightarrow> y = y'"
  apply rule
  prefer 2
  apply simp
  unfolding Abs_eq_iff2
  apply (erule exE)
  apply auto
  unfolding alpha_lst.simps
  apply (subgoal_tac "p = 0")
  apply auto[1]
  apply (auto simp add: permute_list_id)
  done

lemma Let_eq_same_var[simp]:
  assumes "map fst as = map fst as'"
  shows "Terms.Let as e = Terms.Let as' e' \<longleftrightarrow> (as = as' \<and> e = e')"
proof-
  from assms have  "map (\<lambda>x. atom (fst x)) as = map (\<lambda>x. atom (fst x)) as'"
    by (induction as as' rule: list_induct2') auto
  thus ?thesis by auto
qed

lemma disjoint_mono: "A \<inter> B = {} \<Longrightarrow>  A' \<subseteq> A \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> A' \<inter> B' = {}" by auto

lemma disjoint_Un1: "(A \<union> B) \<inter> C = {} \<longleftrightarrow> A \<inter> C = {} \<and> B \<inter> C = {} " by auto
lemma disjoint_Un2: "C \<inter> (A \<union> B) = {} \<longleftrightarrow> C \<inter> A = {} \<and> C \<inter> B = {} " by auto

theorem DeadCodeRemovalCorrect:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "(\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')"
   shows  "\<exists> \<Delta>' z'. (\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
  using assms
proof(nominal_induct arbitrary: \<Gamma>' e' rule:reds.strong_induct)
case (Lambda \<Gamma> x e L) thus ?case by (rule lambda_case)
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z body) thus ?case by (rule app_case)
next
case (Variable \<Gamma> x e L \<Delta> z \<Gamma>' var) thus ?case by (rule var_case)
next
case (Let as \<Gamma> L body \<Delta> z \<Gamma>' let')
  let "Terms.Let ?as' ?body'" = "Terms.Let (restrict_reachable (map_ran (\<lambda>_. remove_dead_code) as) (remove_dead_code body)) (remove_dead_code body)"

  from `(\<Gamma>, Terms.Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')` 
  obtain S where "\<Gamma>' = rdcH S \<Gamma>" and "let' = SmartLet ?as' ?body'"
  and "S \<subseteq> domA \<Gamma> \<union> set L" and S: "S \<inter> fv (rdcH S \<Gamma>, SmartLet ?as' ?body', L) = {}"  by (auto elim!: dc_rel.cases)

  let "?S'" = "domA as - reachable (map_ran (\<lambda>_. remove_dead_code) as) ?body'"

  from  `S \<subseteq> _` and fresh_distinct[OF Let(1)] and fresh_distinct_list[OF Let(2)]
  have "S \<inter> domA as = {}" by auto 
  hence [simp]: "(rdcH (?S' \<union> S) as) = ?as'"
    unfolding restrict_reachable_def rdcH_def
    by -(rule restrictA_cong,  auto)
  
  have [simp]: "(rdcH (?S' \<union> S) \<Gamma>) = (rdcH S \<Gamma>)"
    using fresh_distinct[OF Let(1)]
    by (auto intro: rdcH_cong_set simp add: fresh_star_at_base)

  have "(as @ \<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (rdcH (?S' \<union> S) (as @ \<Gamma>), ?body')"
  proof (rule dc_rel.intros)
    show "(?S' \<union> S) \<subseteq> domA (as @ \<Gamma>) \<union> set L" using `S \<subseteq> domA \<Gamma> \<union> set L` by auto

    have "?S' \<inter> fv ?as' = {}"
      using fv_heap_reachable by auto
    moreover
    have "?S' \<inter> fv \<Gamma> = {}"
      using Let(1) by (auto simp add: fresh_star_def fresh_def fv_def)
    hence "?S' \<inter> fv (rdcH S \<Gamma>) = {}"
      by (rule disjoint_mono[OF _ subset_refl rdch_fv_subset])
    moreover
    have "?S' \<inter> fv (?body') = {}"
      using fv_e_reachable by auto
    moreover
    have "?S' \<inter> fv L = {}"
      using fresh_distinct_list[OF Let(2)] by auto
    moreover
    have "S \<inter> fv ?as' = {}"
      using S `S \<inter> domA as = {}` by auto
    moreover
    have "S \<inter> fv (rdcH S \<Gamma>) = {}"
      using S by auto
    moreover
    have "S \<inter> fv (?body') = {}"
      using S `S \<inter> domA as = {}` by auto
    moreover
    have "S \<inter> fv L = {}"
      using S by auto
    ultimately
    show "(?S' \<union> S) \<inter> fv (rdcH (?S' \<union> S) (as @ \<Gamma>), ?body', L) = {}" using fresh_distinct[OF Let(1)] by auto
  qed
  hence "(as @ \<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (?as' @ \<Gamma>', ?body')" unfolding `\<Gamma>'=_` using fresh_distinct[OF Let(1)] by simp
  from Let(4)[OF this]
  obtain \<Delta>' z' where "(\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z')" and "?as' @ \<Gamma>' : ?body' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'" by auto
  from reds_SmartLet[OF _ this(2)]
  have "\<Gamma>' : let' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'" unfolding `\<Gamma>'=_`  `let' = _`
    using Let(1,2) by (auto simp add: fresh_star_def fresh_Pair)
  with `(\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z')`
  show ?case  by auto
qed


corollary
  assumes "[] : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
   shows  "\<exists> \<Delta>' z'. [] : remove_dead_code e \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
proof-
  have "([], e) \<triangleright>\<^bsub>L\<^esub> (rdcH {} [], remove_dead_code e)" by (rule dc_rel.intros) auto
  hence "([], e) \<triangleright>\<^bsub>L\<^esub> ([], remove_dead_code e)" by simp
  from DeadCodeRemovalCorrect[OF assms this]
  show ?thesis by auto
qed

end
