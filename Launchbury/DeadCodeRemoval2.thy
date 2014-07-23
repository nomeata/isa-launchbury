theory DeadCodeRemoval2
imports Terms Substitution
begin

definition reach_graph :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
  where
  "reach_graph \<Gamma> v\<^sub>1 v\<^sub>2 = (case map_of \<Gamma> v\<^sub>1 of Some e \<Rightarrow> v\<^sub>2 \<in> fv e | None \<Rightarrow> False)"

lemma reach_graph_eqvt[eqvt]: "\<pi> \<bullet> reach_graph \<Gamma>  v\<^sub>1 v\<^sub>2 = reach_graph (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> v\<^sub>1)  (\<pi> \<bullet> v\<^sub>2)"
  unfolding reach_graph_def by perm_simp rule

definition reachable :: "heap \<Rightarrow> exp \<Rightarrow> var set"
  where
  "reachable \<Gamma> e = {v . \<exists> v\<^sub>1 \<in> fv e . (reach_graph \<Gamma>)\<^sup>*\<^sup>* v\<^sub>1 v}" (* ImageP would be nicer *)

lemma reachable_eqvt[eqvt]: "\<pi> \<bullet> reachable \<Gamma> e = reachable (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding reachable_def by perm_simp rule

definition restrict_reachable :: "heap \<Rightarrow> exp \<Rightarrow> heap"
  where 
  "restrict_reachable \<Gamma> e = restrictA (reachable \<Gamma> e) (clearjunk \<Gamma>)"

lemma domA_restrict_reachable[simp]: "domA (restrict_reachable \<Gamma> e) = domA \<Gamma> \<inter> reachable \<Gamma> e" 
  unfolding restrict_reachable_def by simp

lemma restrict_reachable_eqvt[eqvt]: "\<pi> \<bullet> restrict_reachable \<Gamma> e = restrict_reachable (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding restrict_reachable_def by perm_simp rule

lemma restrict_reachable_eqvt2: "eqvt restrict_reachable"
  unfolding eqvt_def by (rule, perm_simp, rule)

lemma supp_restrictA: "supp (restrictA s \<Gamma>) \<subseteq> supp \<Gamma>"
  by (induction \<Gamma>) (auto simp add: supp_Cons supp_Pair)

lemma supp_delete: "supp (delete x \<Gamma>) \<subseteq> supp \<Gamma>"
  by (induction \<Gamma>) (auto simp add: supp_Cons supp_Pair)

lemma supp_clearjunkA: "supp (clearjunk \<Gamma>) \<subseteq> supp \<Gamma>"
  by (induction \<Gamma> rule: clearjunk.induct) (auto simp add: supp_Cons supp_Pair dest: set_mp[OF supp_delete])

lemma supp_restrict_reachable_subset: "supp (restrict_reachable \<Gamma> e) \<subseteq> supp \<Gamma>"
  unfolding restrict_reachable_def using supp_restrictA supp_clearjunkA by (rule subset_trans)

lemma supp_list_union: "supp l = \<Union>{supp x |x. x \<in> set l}"
  by (induction l) (auto simp add: supp_Nil supp_Cons)
lemma fv_list_union: "fv l = \<Union>{fv x |x. x \<in> set l}"
  by (induction l) auto

lemma set_restrictA: "set (restrictA S \<Gamma>) \<subseteq> set \<Gamma>"
  by (induction \<Gamma>) auto

lemma fv_restrictA:
  assumes "x \<in> fv (restrictA S (clearjunk \<Gamma>))"
  obtains y where "y \<in> S" and "(reach_graph \<Gamma>)\<^sup>=\<^sup>= y x"
proof-
  from assms[unfolded fv_list_union]
  obtain y e where "(y, e) \<in> set (restrictA S (clearjunk \<Gamma>))" and  "x = y \<or> x \<in> fv e" by auto
  show thesis
  proof
    from `(y, e) \<in> set (restrictA S (clearjunk \<Gamma>))`
    have "y \<in> domA (restrictA S (clearjunk \<Gamma>))" by (rule domA_from_set)
    thus "y \<in> S" by simp

    from `(y, e) \<in> set (restrictA S (clearjunk \<Gamma>))`
    have "(y, e) \<in> set (clearjunk \<Gamma>)" using set_restrictA by auto
    hence "map_of (clearjunk \<Gamma>) y = Some e" by (rule map_of_is_SomeI[OF distinct_clearjunk])
    hence "map_of \<Gamma> y = Some e" by (simp add: map_of_clearjunk)
    with `x = y \<or> x \<in> fv e`
    show "(reach_graph \<Gamma>)\<^sup>=\<^sup>= y x"  by (auto simp add:  reach_graph_def)
  qed
qed


lemma all_occuring_heap_vars_reachable: "(fv (restrict_reachable \<Gamma> e) \<union> fv e) \<inter> domA \<Gamma> \<subseteq> reachable \<Gamma> e"
unfolding restrict_reachable_def
proof(intro subsetI, elim IntE UnE)
  fix x
  assume "x \<in> domA \<Gamma>"
  assume "x \<in> fv e"
  thus "x \<in> reachable \<Gamma> e" unfolding reachable_def by auto
next
  fix x
  assume "x \<in> domA \<Gamma>"
  assume "x \<in> fv (restrictA (reachable \<Gamma> e) (clearjunk \<Gamma>))" (is " _ \<in> fv ?\<Gamma>'")
  then obtain y where "y \<in> (reachable \<Gamma> e)" and  "(reach_graph \<Gamma>)\<^sup>=\<^sup>= y x"
    by (rule fv_restrictA)
  hence "x \<in> reachable \<Gamma> e"
    unfolding reachable_def by (auto intro: tranclp_into_rtranclp  rtranclp_into_tranclp1) 
  thus "x \<in> reachable \<Gamma> e" unfolding reachable_def by auto
qed

nominal_function
  remove_dead_code :: "exp \<Rightarrow> exp"
where
  "remove_dead_code (Lam [x]. e) = Lam [x]. remove_dead_code e"
| "remove_dead_code (App e x) = App (remove_dead_code e) x"
| "remove_dead_code (Var x) = Var x"
| "remove_dead_code (Let as e) = Let (restrict_reachable (map_ran (\<lambda> _ e. remove_dead_code e) as) (remove_dead_code e)) (remove_dead_code e)"
proof-
case goal1 thus ?case
  unfolding remove_dead_code_graph_aux_def eqvt_def 
  apply rule
  apply perm_simp
  apply rule
  done
next
case goal3 thus ?case
  by (metis Terms.Let_def exp_assn.exhaust(1) heapToAssn_asToHeap)
next
case (goal4 x e x' e')
  from goal4(5)
  show ?case
  proof (rule eqvt_lam_case)
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Lam [x]. e"
    hence *: "supp \<pi> \<sharp>* Lam [x]. remove_dead_code_sumC e"
      by (auto simp add:  fresh_star_def fresh_eqvt_at[OF goal4(1)] exp_assn.fsupp)
      
    have "Lam [(\<pi> \<bullet> x)]. remove_dead_code_sumC (\<pi> \<bullet> e) =  \<pi> \<bullet> Lam [x]. remove_dead_code_sumC e"
        by (simp add: pemute_minus_self eqvt_at_apply'[OF goal4(1)])
    also have "\<dots> = Lam [x]. remove_dead_code_sumC e" by (rule perm_supp_eq[OF *])
    finally show  "Lam [(\<pi> \<bullet> x)]. remove_dead_code_sumC (\<pi> \<bullet> e) = Lam [x]. remove_dead_code_sumC e".
  qed
next
case (goal13 as body as' body')
  from goal13(13)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
  
    from goal13(2) have eqvt_at1: "eqvt_at remove_dead_code_sumC body" by auto
    from goal13(1)
    have eqvt_at2: "eqvt_at (map_ran (\<lambda>_. remove_dead_code_sumC)) as" by (induction as) (fastforce simp add: eqvt_at_def)+

    assume assm: "supp \<pi> \<sharp>* Let as body"

    let ?as' = "restrict_reachable (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)"
    let ?body' = "remove_dead_code_sumC body"
    let ?rable = "reachable (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)"

    have "supp (Let ?as' ?body') \<subseteq> supp as \<union> supp body"
      by (auto 4 4 simp add: exp_assn.supp Let_supp
          dest!: set_mp[OF supp_eqvt_at[OF eqvt_at1 finite_supp]]
                 set_mp[OF supp_eqvt_at[OF eqvt_at2 finite_supp]]
                 set_mp[OF supp_restrict_reachable_subset]
                 )
    moreover
    have "(fv ?as' \<union> fv ?body') \<inter> (domA  (map_ran (\<lambda>_. remove_dead_code_sumC) as)) \<subseteq> reachable (map_ran (\<lambda>_. remove_dead_code_sumC) as) ?body'"
      by (rule all_occuring_heap_vars_reachable)
    ultimately
    have supp_subset: "supp (Let ?as' ?body') \<subseteq> supp (Let as body)"
      by (auto simp add: Let_supp fv_def)
    with assm
    have *: "supp \<pi> \<sharp>* Let ?as' ?body'"  by (auto simp add: fresh_star_def fresh_def)


    have "Let (restrict_reachable (map_ran (\<lambda>_. remove_dead_code_sumC) (\<pi> \<bullet> as))  (remove_dead_code_sumC (\<pi> \<bullet> body))) (remove_dead_code_sumC (\<pi> \<bullet> body)) =
      \<pi> \<bullet> Let ?as' ?body'"
      unfolding  Let_perm_simps restrict_reachable_eqvt eqvt_at_apply'[OF eqvt_at1] subst eqvt_at_apply'[OF eqvt_at2] ..
    also have "\<dots> = Let ?as' ?body'" by (rule perm_supp_eq[OF *])
    finally show "Let (restrict_reachable (map_ran (\<lambda>_. remove_dead_code_sumC) (\<pi> \<bullet> as)) (remove_dead_code_sumC (\<pi> \<bullet> body))) (remove_dead_code_sumC (\<pi> \<bullet> body)) =
         (Let ?as' ?body')".
  qed
qed auto
nominal_termination (eqvt) by lexicographic_order

lemma subst_remove_dead_code: "(remove_dead_code e)[y::=x] = remove_dead_code (e [y::=x])"
  and "(map_ran (\<lambda> _ e. remove_dead_code e) \<Gamma>)[y::h=x] = map_ran (\<lambda> _ e. remove_dead_code e) (\<Gamma>[y::h=x])"
proof (nominal_induct e and \<Gamma>  avoiding: y x rule:exp_heap_strong_induct)
case (Let \<Gamma> e y x)
  thus ?case
  by (cases "domA \<Gamma> \<inter> fv e = {}") (auto simp add: fresh_star_at_base fv_subst_eq fresh_star_Pair )
qed auto

end
