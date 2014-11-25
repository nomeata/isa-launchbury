theory CoCallCardinality
imports FTreeCardinality CoCallAnalysis
begin

definition aeFtree :: "AEnv \<Rightarrow> var ftree"
  where "aeFtree ae = many_among (edom ae)"

lemma cont_aeFtree[THEN cont_compose, cont2cont, simp]:
  "cont aeFtree"
  sorry

inductive_set valid_lists :: "var set \<Rightarrow> CoCalls \<Rightarrow> var list set"
  for S G
  where  "[] \<in> valid_lists S G"
  | "set xs \<subseteq> ccNeighbors {x} G \<Longrightarrow> xs \<in> valid_lists S G \<Longrightarrow> x \<in> S \<Longrightarrow> x#xs \<in> valid_lists S G"

inductive_simps valid_lists_simps[simp]: "[] \<in> valid_lists S G" "(x#xs) \<in> valid_lists S G"
inductive_cases vald_lists_ConsE: "(x#xs) \<in> valid_lists S G"

lemma  valid_lists_downset_aux:
  "xs \<in> valid_lists S CoCalls \<Longrightarrow> butlast xs \<in> valid_lists S CoCalls"
  by (induction xs) (auto dest: in_set_butlastD)


lift_definition ccFTree :: "var set \<Rightarrow> CoCalls \<Rightarrow> var ftree" is "\<lambda> S G. valid_lists S G" 
  by (auto intro: valid_lists_downset_aux)

lemma valid_lists_subset: "xs \<in> valid_lists S G \<Longrightarrow> set xs \<subseteq> S"
  by (induction rule: valid_lists.induct) auto

lemma paths_ccFTree[simp]: "paths (ccFTree S G) = valid_lists S G" by transfer auto

lemma cont_ccFTree1[THEN cont_compose, cont2cont, simp]:
  "cont ccFTree"
  sorry

lemma cont_ccFTree2[THEN cont_compose, cont2cont, simp]:
  "cont (ccFTree S)"
  sorry

lemma carrier_ccFTree: "carrier (ccFTree S G) \<subseteq> S"
  by transfer (auto dest: valid_lists_subset)

lemma valid_lists_mono1:
  assumes "S \<subseteq> S'"
  shows "valid_lists S G \<subseteq> valid_lists S' G"
proof
  fix xs
  assume "xs \<in> valid_lists S G"
  thus "xs \<in> valid_lists S' G"
    by (induction rule: valid_lists.induct) (auto dest: set_mp[OF assms])
qed


lemma ccFTree_mono1: "S \<subseteq> S' \<Longrightarrow> ccFTree S G \<sqsubseteq> ccFTree S' G"
  by transfer (rule valid_lists_mono1)

lemma ccFTree_mono2: "G \<sqsubseteq> G' \<Longrightarrow> ccFTree S G \<sqsubseteq> ccFTree S G'"
  by (rule cont2monofunE[OF cont_ccFTree2[OF cont_id]])

lemma valid_lists_cc_restr: "valid_lists S G = valid_lists S (cc_restr S G)"
proof(rule set_eqI)
  fix xs
  show "(xs \<in> valid_lists S G) = (xs \<in> valid_lists S (cc_restr S G))"
    by (induction xs) (auto dest: set_mp[OF valid_lists_subset])
qed

lemma ccFTree_cc_restr: "ccFTree S G = ccFTree S (cc_restr S G)"
  by transfer' (rule valid_lists_cc_restr)

lemma ccFTree_cong_below: "cc_restr S G \<sqsubseteq> cc_restr S G' \<Longrightarrow> ccFTree S G \<sqsubseteq> ccFTree S G'"
  by (metis ccFTree_mono2 ccFTree_cc_restr)
  
lemma ccFTree_cong: "cc_restr S G = cc_restr S G' \<Longrightarrow> ccFTree S G = ccFTree S G'"
  by (metis ccFTree_cc_restr)


lemma interleave_valid_list:
  "xs \<in> ys \<otimes> zs \<Longrightarrow> ys \<in> valid_lists S G \<Longrightarrow> zs \<in> valid_lists S' G' \<Longrightarrow> xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
proof (induction rule:interleave_induct)
  case Nil
  show ?case by simp
next
  case (left ys zs xs x)

  from `x # ys \<in> valid_lists S G`
  have "x \<in> S" and "set ys \<subseteq> ccNeighbors {x} G" and "ys \<in> valid_lists S G"
    by auto
 
  from `xs \<in> ys \<otimes> zs`
  have "set xs = set ys \<union> set zs" by (rule interleave_set)
  with `set ys \<subseteq> ccNeighbors {x} G` valid_lists_subset[OF `zs \<in> valid_lists S' G'`]
  have "set xs \<subseteq> ccNeighbors {x} (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (auto simp add: ccNeighbors_ccProd `x \<in> S`)
  moreover
  from `ys \<in> valid_lists S G` `zs \<in> valid_lists S' G'`
  have "xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (rule left.IH)
  moreover
  from `x \<in> S`
  have "x \<in> S \<union> S'" by simp
  ultimately
  show ?case..
next
  case (right ys zs xs x)

  from `x # zs \<in> valid_lists S' G'`
  have "x \<in> S'" and "set zs \<subseteq> ccNeighbors {x} G'" and "zs \<in> valid_lists S' G'"
    by auto
 
  from `xs \<in> ys \<otimes> zs`
  have "set xs = set ys \<union> set zs" by (rule interleave_set)
  with `set zs \<subseteq> ccNeighbors {x} G'` valid_lists_subset[OF `ys \<in> valid_lists S G`]
  have "set xs \<subseteq> ccNeighbors {x} (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (auto simp add: ccNeighbors_ccProd `x \<in> S'`)
  moreover
  from `ys \<in> valid_lists S G` `zs \<in> valid_lists S' G'`
  have "xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (rule right.IH)
  moreover
  from `x \<in> S'`
  have "x \<in> S \<union> S'" by simp
  ultimately
  show ?case..
qed

lemma interleave_ccFTree: 
   "ccFTree S G \<otimes>\<otimes> ccFTree S' G' \<sqsubseteq> ccFTree (S \<union> S') (G \<squnion> G' \<squnion> ccProd S S')"
   by transfer' (auto, erule (2) interleave_valid_list)

lemma interleave_valid_list':
  "xs \<in> valid_lists (S \<union> S') G \<Longrightarrow> \<exists> ys zs. xs \<in> ys \<otimes> zs \<and> ys \<in> valid_lists S G \<and> zs \<in> valid_lists S' G"
proof(induction rule: valid_lists.induct[case_names Nil Cons])
  case Nil show ?case by simp
next
  case (Cons xs x)
  then obtain ys zs where "xs \<in> ys \<otimes> zs" "ys \<in> valid_lists S G" "zs \<in> valid_lists S' G" by auto

    from `xs \<in> ys \<otimes> zs` have "set xs = set ys \<union> set zs" by (rule interleave_set)
    with `set xs \<subseteq> ccNeighbors {x} G` 
    have "set ys \<subseteq> ccNeighbors {x} G" and "set zs \<subseteq> ccNeighbors {x} G"  by auto
  
  from `x \<in> S \<union> S'`
  show ?case
  proof
    assume "x \<in> S"
    with `set ys \<subseteq> ccNeighbors {x} G` `ys \<in> valid_lists S G`
    have "x # ys \<in> valid_lists S G"
      by rule
    moreover
    from `xs \<in> ys \<otimes> zs`
    have "x#xs \<in> x#ys \<otimes> zs"..
    ultimately
    show ?thesis using `zs \<in> valid_lists S' G` by blast
  next
    assume "x \<in> S'"
    with `set zs \<subseteq> ccNeighbors {x} G` `zs \<in> valid_lists S' G`
    have "x # zs \<in> valid_lists S' G"
      by rule
    moreover
    from `xs \<in> ys \<otimes> zs`
    have "x#xs \<in> ys \<otimes> x#zs"..
    ultimately
    show ?thesis using `ys \<in> valid_lists S G` by blast
  qed
qed


lemma interleave_ccFTree': 
   "ccFTree (S \<union> S') G \<sqsubseteq> ccFTree S G \<otimes>\<otimes> ccFTree S' G"
   by transfer' (auto dest!:  interleave_valid_list')


lemma many_calls_valid_list:
  "xs \<in> valid_lists {x} (ccProd {x} {x}) \<Longrightarrow> xs \<in> range (\<lambda>n. replicate n x)"
  by (induction rule: valid_lists.induct) (auto, metis UNIV_I image_iff replicate_Suc)

lemma many_calls_ccFTree:
  shows "many_calls x = ccFTree {x} (ccProd {x} {x})"
  apply(transfer')
  apply (auto intro: many_calls_valid_list)
  apply (induct_tac n)
  apply (auto simp add: ccNeighbors_ccProd)
  done

lemma filter_valid_lists:
  "xs \<in> valid_lists S G \<Longrightarrow> filter P xs \<in> valid_lists {a \<in> S. P a} G"
by (induction rule:valid_lists.induct) auto

lemma filter_valid_lists':
  "xs \<in> valid_lists {x' \<in> S. P x'} G \<Longrightarrow> xs \<in> filter P ` valid_lists S G"
proof (induction xs )
  case Nil thus ?case by auto  (metis filter.simps(1) image_iff valid_lists_simps(1))
next
  case (Cons x xs)
  from Cons.prems
  have "set xs \<subseteq> ccNeighbors {x} G" and "xs \<in> valid_lists {x' \<in> S. P x'} G" and "x \<in> S" and "P x" by auto

  from this(2) have "set xs \<subseteq> {x' \<in> S. P x'}" by (rule valid_lists_subset)
  hence "\<forall>x \<in> set xs. P x" by auto
  hence [simp]: "filter P xs = xs" by (rule filter_True)
  
  from Cons.IH[OF `xs \<in> _`]
  have "xs \<in> filter P ` valid_lists S G".

  from  `xs \<in> valid_lists {x' \<in> S. P x'} G`
  have "xs \<in> valid_lists S G" by (rule set_mp[OF valid_lists_mono1, rotated]) auto

  from `set xs \<subseteq> ccNeighbors {x} G` this `x \<in> S`
  have "x # xs \<in> valid_lists S G" by rule

  hence "filter P (x # xs) \<in> filter P ` valid_lists S G" by (rule imageI)
  thus ?case using `P x` `filter P xs =xs` by simp
qed

lemma without_ccFTree[simp]:
   "without x (ccFTree S G) = ccFTree (S - {x}) G"
by (transfer' fixing: x) (auto dest: filter_valid_lists'  filter_valid_lists[where P = "(\<lambda> x'. x'\<noteq> x)"]  simp add: set_diff_eq)

lemma repeatable_ccFTree_ccSquare: "S \<subseteq> S' \<Longrightarrow> repeatable (ccFTree S (ccSquare S'))"
   unfolding repeatable_def
   by transfer (auto simp add:ccNeighbors_ccSquare dest: set_mp[OF valid_lists_subset])

locale CoCallCardinality = CoCallAnalysis + CoCallAnalyisHeap + CorrectArityAnalysisLet' +
  assumes ccExp_App: "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a"
  assumes ccExp_Lam: "cc_restr (fv (Lam [y]. e)) (ccExp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> ccExp (Lam [y]. e)\<cdot>n"
  assumes ccExp_subst: "x \<notin>  S \<Longrightarrow> y \<notin> S \<Longrightarrow> cc_restr S (ccExp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (ccExp e\<cdot>a)"
  assumes ccExp_pap: "isLam e \<Longrightarrow> ccExp e\<cdot>0 = ccSquare (fv e)"
begin

definition Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fexp e = (\<Lambda> a. ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a))"

lemma Fexp_simp: "Fexp e\<cdot>a = ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a)"
  unfolding Fexp_def sorry

lemma carrier_Fexp: "carrier (Fexp e\<cdot>a) \<subseteq> fv e"
  unfolding Fexp_simp
  by (auto  dest!: set_mp[OF carrier_ccFTree] set_mp[OF Aexp_edom])

definition Fheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fheap \<Gamma> e = (\<Lambda> a. ccFTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccHeap \<Gamma> e\<cdot>a))"

lemma Fheap_simp: "Fheap \<Gamma> e\<cdot>a = ccFTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccHeap \<Gamma> e\<cdot>a)"
  unfolding Fheap_def sorry

sublocale FutureAnalysis Fexp.

sublocale FutureAnalysisCarrier Fexp
  by default (rule carrier_Fexp)

sublocale FutureAnalysisCorrect Fexp
proof default
  fix x e a

  from edom_mono[OF Aexp_App]
  have *: "{x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> edom (Aexp (App e x)\<cdot>a)" by auto

  have **: "{x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> insert x (fv e)"
    by (intro subset_trans[OF *] subset_trans[OF Aexp_edom]) auto

  have "many_calls x \<otimes>\<otimes> Fexp e\<cdot>(inc\<cdot>a) = many_calls x \<otimes>\<otimes> ccFTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))"
    unfolding Fexp_simp..
  also have "\<dots> = ccFTree {x} (ccProd {x} {x}) \<otimes>\<otimes> ccFTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))"
    unfolding many_calls_ccFTree..
  also have "\<dots> \<sqsubseteq> ccFTree ({x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a))) (ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (rule interleave_ccFTree)
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp (App e x)\<cdot>a)) (ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (rule ccFTree_mono1[OF *])
  also have "ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))) = ccExp e\<cdot>(inc\<cdot>a) \<squnion> (ccProd {x} {x} \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    apply (rule trans[OF join_assoc])
    apply (rule trans[OF join_comm])
    apply (rule trans[OF join_assoc])
    apply (rule arg_cong[OF join_comm])
    done
  also have "\<dots> = ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} ({x} \<union> (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (simp add:  ccProd_union[symmetric] del: ccProd_union)
  also have "ccProd {x} ({x} \<union> (edom (Aexp e\<cdot>(inc\<cdot>a)))) \<sqsubseteq> ccProd {x} (insert x (fv e))"
    by (rule ccProd_mono2[OF **])
  also have "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a"
    by (rule ccExp_App)
  also have "ccFTree (edom (Aexp (App e x)\<cdot>a)) (ccExp (App e x)\<cdot>a) =  Fexp (App e x)\<cdot>a"
    unfolding Fexp_simp..
  finally
  show "many_calls x \<otimes>\<otimes> Fexp e\<cdot>(inc\<cdot>a) \<sqsubseteq> Fexp (App e x)\<cdot>a"
    by this simp_all
next
  fix y e n
  from edom_mono[OF Aexp_Lam]
  have *: "edom (Aexp e\<cdot>(pred\<cdot>n)) - {y} \<subseteq> edom (Aexp (Lam [y]. e)\<cdot>n)" by auto

  have "without y (Fexp e\<cdot>(pred\<cdot>n)) = without y (ccFTree (edom (Aexp e\<cdot>(pred\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n)))"
    unfolding Fexp_simp..
  also have "\<dots> = ccFTree (edom (Aexp e\<cdot>(pred\<cdot>n)) - {y}) (ccExp e\<cdot>(pred\<cdot>n))"
    by (rule  without_ccFTree)
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (ccExp e\<cdot>(pred\<cdot>n))"
    by (rule ccFTree_mono1[OF *])
  also have "\<dots> = ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (cc_restr ((edom (Aexp (Lam [y]. e)\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n)))"
    by (rule ccFTree_cc_restr)
  also have "(cc_restr ((edom (Aexp (Lam [y]. e)\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n))) \<sqsubseteq> (cc_restr (fv (Lam [y]. e)) (ccExp e\<cdot>(pred\<cdot>n)))"
    by (rule cc_restr_mono1[OF Aexp_edom])
  also have "\<dots> \<sqsubseteq> ccExp (Lam [y]. e)\<cdot>n"
    by (rule ccExp_Lam)
  also have "ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (ccExp (Lam [y]. e)\<cdot>n) = Fexp (Lam [y]. e)\<cdot>n"
    unfolding Fexp_simp..
  finally
  show "without y (Fexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Fexp (Lam [y]. e)\<cdot>n" by this simp_all
next
  fix e y x a

  from edom_mono[OF Aexp_subst]
  have *: "edom (Aexp e[y::=x]\<cdot>a) \<subseteq> insert x (edom (Aexp e\<cdot>a) - {y})" by simp


  have "Fexp e[y::=x]\<cdot>a = ccFTree (edom (Aexp e[y::=x]\<cdot>a)) (ccExp e[y::=x]\<cdot>a)"
    unfolding Fexp_simp..
  also have "\<dots> \<sqsubseteq> ccFTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a)"
    by (rule ccFTree_mono1[OF *])
  also have "\<dots> \<sqsubseteq> many_calls x \<otimes>\<otimes> without x (\<dots>)"
    by (rule paths_many_calls_subset)
  also have "without x (ccFTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a))
    = ccFTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e[y::=x]\<cdot>a)"
    by simp
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e\<cdot>a)"
    by (rule ccFTree_cong_below[OF ccExp_subst]) auto
  also have "\<dots> = without y (ccFTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a))"
    by simp (metis Diff_insert Diff_insert2)
  also have "ccFTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a) \<sqsubseteq> ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)"
    by (rule ccFTree_mono1) auto
  also have "\<dots> = Fexp e\<cdot>a"
    unfolding Fexp_simp..
  finally
  show "Fexp e[y::=x]\<cdot>a \<sqsubseteq> many_calls x \<otimes>\<otimes> without y (Fexp e\<cdot>a)"
    by this simp_all
next
  fix v a
  have "up\<cdot>a \<sqsubseteq> (Aexp (Var v)\<cdot>a) v" by (rule Aexp_Var)
  hence "v \<in> edom (Aexp (Var v)\<cdot>a)" by (auto simp add: edom_def)
  hence "[v] \<in> valid_lists (edom (Aexp (Var v)\<cdot>a)) (ccExp (Var v)\<cdot>a)"
    by auto
  thus "single v \<sqsubseteq> Fexp (Var v)\<cdot>a"
    unfolding Fexp_simp by (auto intro: single_below)
next
  fix e
  assume "isLam e"
  hence [simp]: "ccExp e\<cdot>0 = ccSquare (fv e)" by (rule ccExp_pap)
  thus "repeatable (Fexp e\<cdot>0)"
    unfolding Fexp_simp by (auto intro: repeatable_ccFTree_ccSquare[OF Aexp_edom])
qed


sublocale FutureAnalysisCardinalityHeap Fexp Aexp Aheap Fheap
  apply default
  sorry

end

