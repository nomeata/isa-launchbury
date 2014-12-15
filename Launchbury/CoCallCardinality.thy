theory CoCallCardinality
imports FTreeCardinality CoCallAnalysis
begin

lemma subset_ccNeighbors:
  "S \<subseteq> ccNeighbors {x} G \<longleftrightarrow> ccProd {x} S \<sqsubseteq> G"
  by transfer (auto simp add: sym_def)

lemma elem_ccNeighbors:
  "xa \<in> ccNeighbors {x} G \<longleftrightarrow> (xa--x\<in>G)"
  by transfer (auto simp add: sym_def)




(*
definition ccApprox :: "var ftree \<Rightarrow> CoCalls"
  where "ccApprox t =  lub (ccFromList ` (paths t))"
*)
lift_definition ccApprox :: "var ftree \<Rightarrow> CoCalls"
  is "\<lambda> xss .  lub (ccFromList ` xss)".

lemma ccApprox_paths: "ccApprox t = lub (ccFromList ` (paths t))" by transfer simp

lemma ccApprox_strict[simp]: "ccApprox \<bottom> = \<bottom>"
  by (simp add: ccApprox_paths empty_is_bottom[symmetric])

lemma in_ccApprox: "(x--y\<in>(ccApprox t)) \<longleftrightarrow> (\<exists> xs \<in> paths t. (x--y\<in>(ccFromList xs)))"
  unfolding ccApprox_paths
  by transfer auto

lemma ccApprox_mono: "paths t \<subseteq> paths t' \<Longrightarrow> ccApprox t \<sqsubseteq> ccApprox t'"
  by (rule below_CoCallsI) (auto simp add: in_ccApprox)

lemma ccApprox_mono': "t \<sqsubseteq>  t' \<Longrightarrow> ccApprox t \<sqsubseteq> ccApprox t'"
  by (metis below_set_def ccApprox_mono paths_mono_iff)

lemma ccApprox_belowI: "(\<And> xs. xs \<in> paths t \<Longrightarrow> ccFromList xs \<sqsubseteq> G) \<Longrightarrow> ccApprox t \<sqsubseteq> G"
  unfolding ccApprox_paths
  by transfer auto

lemma ccApprox_below_iff: "ccApprox t \<sqsubseteq> G \<longleftrightarrow> (\<forall> xs \<in> paths t. ccFromList xs \<sqsubseteq> G)"
  unfolding ccApprox_paths by transfer auto

lemma cc_restr_ccApprox_below_iff: "cc_restr S (ccApprox t) \<sqsubseteq> G \<longleftrightarrow> (\<forall> xs \<in> paths t. cc_restr S (ccFromList xs) \<sqsubseteq> G)"
  unfolding ccApprox_paths cc_restr_lub
  by transfer auto

lemma ccFromList_below_ccApprox:
  "xs \<in> paths t \<Longrightarrow> ccFromList xs \<sqsubseteq> ccApprox t" 
by (rule below_CoCallsI)(auto simp add: in_ccApprox)

lemma ccApprox_nxt_below:
  "ccApprox (nxt t x) \<sqsubseteq> ccApprox t"
by (rule below_CoCallsI)(auto simp add: in_ccApprox paths_nxt_eq elim!:  bexI[rotated])

lemma ccFromList_filter[simp]: "x--y\<in>ccFromList (filter P xs) \<longleftrightarrow> x--y\<in>ccFromList xs \<and> P x \<and> P y"
  by (induction xs) auto

lemma ccApprox_ftree_restr_nxt_below:
  "ccApprox (ftree_restr S (nxt t x)) \<sqsubseteq> ccApprox (ftree_restr S t)"
by (rule below_CoCallsI)
   (auto simp add: in_ccApprox filter_paths_conv_free_restr[symmetric] paths_nxt_eq  elim!:  bexI[rotated])

lemma ccApprox_ftree_restr[simp]: "ccApprox (ftree_restr S t) = cc_restr S (ccApprox t)"
  by (rule CoCalls_eqI) (auto simp add: in_ccApprox filter_paths_conv_free_restr[symmetric] )

lemma interleave_ccFromList:
  "xs \<in> interleave ys zs \<Longrightarrow> ccFromList xs = ccFromList ys \<squnion> ccFromList zs \<squnion> ccProd (set ys) (set zs)"
  by (induction rule: interleave_induct)
     (auto simp add: interleave_set ccProd_comm ccProd_insert2[where S' = "set xs" for xs]  ccProd_insert1[where S' = "set xs" for xs] )

lemma ccApprox_both: "ccApprox (t \<otimes>\<otimes> t') = ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t')"
proof (rule below_antisym)
  show "ccApprox (t \<otimes>\<otimes> t') \<sqsubseteq> ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t')"
  by (rule below_CoCallsI)
     (auto 4 4  simp add: in_ccApprox paths_both Union_paths_carrier[symmetric]  interleave_ccFromList)
next
  have "ccApprox t \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (rule ccApprox_mono[OF both_contains_arg1])
  moreover
  have "ccApprox t' \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (rule ccApprox_mono[OF both_contains_arg2])
  moreover
  have "ccProd (carrier t) (carrier t') \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
  proof(rule ccProd_belowI)
    fix x y
    assume "x \<in> carrier t" and "y \<in> carrier t'"
    then obtain xs ys where "x \<in> set xs" and "y \<in> set ys"
      and "xs \<in> paths t" and "ys \<in> paths t'" by (auto simp add: Union_paths_carrier[symmetric])
    hence "xs @ ys \<in> paths (t \<otimes>\<otimes> t')" by (metis paths_both append_interleave)
    moreover
    from `x \<in> set xs` `y \<in> set ys`
    have "x--y\<in>(ccFromList (xs@ys))" by simp
    ultimately
    show "x--y\<in>(ccApprox (t \<otimes>\<otimes> t'))" by (auto simp add: in_ccApprox simp del: ccFromList_append)
  qed
  ultimately
  show "ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t') \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (simp add: join_below_iff)
qed

lemma wild_recursion:
  assumes "ccApprox  t \<sqsubseteq> G"
  assumes "\<And> x. x \<notin> S \<Longrightarrow> f x = empty"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccProd (ccNeighbors S G) (carrier (f x)) \<sqsubseteq> G"
  shows "ccApprox (ftree_restr (-S) (substitute f {} t)) \<sqsubseteq> G"
proof(rule ccApprox_belowI)
  fix xs

  def seen \<equiv> "{} :: var set"

  assume "xs \<in> paths (ftree_restr (- S) (substitute f {} t))"
  then obtain xs' xs'' T where "xs = [x\<leftarrow>xs' . x \<notin> S]" and "substitute'' f T xs'' xs'" and "T = {}" and "xs'' \<in> paths t"
    by (auto simp add: filter_paths_conv_free_restr2[symmetric] substitute_substitute'')
 
  note this(2,3)
  moreover
  from `ccApprox t \<sqsubseteq> G` and `xs'' \<in> paths t`
  have  "ccFromList xs'' \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff)
  moreover
  note assms(2)
  moreover
  from assms(3-4)
  have "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccFromList ys \<sqsubseteq> G"
    and "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccProd (ccNeighbors S G) (set ys) \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff Union_paths_carrier[symmetric] cc_lub_below_iff)
  moreover
  have "ccProd seen (set xs'') \<sqsubseteq> G" unfolding seen_def by simp
  ultimately 
  have "ccFromList [x\<leftarrow>xs' . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set xs') \<sqsubseteq> G"
  proof(induction f T xs'' xs' arbitrary: seen rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs f x xs' xs T ys)
    from `T = {}` have [simp]: "f_nxt f T x = f" by (simp add: f_nxt_def)

    have seen_x: "ccProd seen {x} \<sqsubseteq> G"
      using Cons.prems
      by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)

    show ?case
    proof(cases "x \<in> S")
      case True

      from Cons.prems
      have "ccProd {x} (set xs) \<sqsubseteq> G" by (auto simp add: join_below_iff)
      with `x \<in> S`
      have subset1: "set xs \<subseteq> ccNeighbors S G" by transfer auto

      from Cons.prems
      have "seen \<subseteq> ccNeighbors {x} G"
        by (auto simp add: subset_ccNeighbors ccProd_insert2[where S' = "set xs" for xs] join_below_iff ccProd_comm)
      hence subset2: "seen \<subseteq> ccNeighbors S G" 
        by (rule order_trans[OF _ ccNeighbors_mono[OF insert_subsetI[OF  `x \<in> S`  empty_subsetI] below_refl]])
        
      from True Cons.prems Cons.hyps
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set ys) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH)
        apply (auto simp add: ccApprox_both join_below_iff ftree_restr_both interleave_ccFromList interleave_set  ccProd_insert2[where S' = "set xs" for xs]
                   intro: below_trans[OF ccProd_mono1[OF subset1]]  below_trans[OF ccProd_mono1[OF subset2]])
        done
      with True seen_x
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G  \<and> ccProd seen (set (x#ys)) \<sqsubseteq> G" 
        by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)
    next
      case False
  
      from False Cons.prems Cons.hyps
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (insert x seen) (set ys) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH[where seen = "insert x seen"])
        apply (auto simp add: ccApprox_both join_below_iff ftree_restr_both interleave_ccFromList
                   simp add:  ccProd_insert2[where S' = "set xs" for xs]
                   simp add:  ccProd_insert1[where S' = "seen"])
        done
      moreover
      from this
      have "ccProd {x} (set ys) \<sqsubseteq>  G"
        by (auto simp add: ccProd_insert1[where S' = "seen"] join_below_iff)
      hence "ccProd {x} {x \<in> set ys. x \<notin> S} \<sqsubseteq> G"
        by (rule below_trans[rotated, OF _ ccProd_mono2]) auto
      moreover
      note False seen_x
      ultimately
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set (x # ys)) \<sqsubseteq> G"
        by (auto simp add: join_below_iff  simp add:  ccProd_insert2[where S' = "set xs" for xs]   ccProd_insert1[where S' = "seen"])
    qed
  qed
  with `xs = _`
  show "ccFromList xs \<sqsubseteq> G" by simp
qed

lemma ccFromList_replicate[simp]: "ccFromList (replicate n x) = (if n \<le> 1 then \<bottom>  else ccProd {x} {x})"
  by (induction n) auto

lemma ccApprox_many_calls[simp]:
  "ccApprox (many_calls x) = ccProd {x} {x}"
  by transfer' (rule CoCalls_eqI, auto)

lemma ccApprox_single[simp]:
  "ccApprox (FTree.single y) = \<bottom>"
  by transfer' auto

lemma carrier_single[simp]: "carrier (single y) = {y}"
  by transfer auto

lemma ccApprox_either[simp]: "ccApprox (t \<oplus>\<oplus> t') = ccApprox t \<squnion> ccApprox t'"
  by transfer' (rule CoCalls_eqI, auto)

  

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

lemma carrier_ccFTree[simp]: "carrier (ccFTree S G) = S"
  apply transfer
  apply (auto dest: valid_lists_subset)
  apply (rule_tac x = "[x]" in bexI)
  apply auto
  done

lemma ccProd_below_cc_restr:
  "ccProd S S' \<sqsubseteq> cc_restr S'' G \<longleftrightarrow> ccProd S S' \<sqsubseteq> G \<and> (S = {} \<or> S' = {} \<or> S \<subseteq> S'' \<and> S' \<subseteq> S'')"
  by transfer auto

lemma valid_lists_ccFromList:
  "xs \<in> valid_lists S G \<Longrightarrow> ccFromList xs \<sqsubseteq> cc_restr S G"
by (induction rule:valid_lists.induct)
   (auto simp add: join_below_iff subset_ccNeighbors ccProd_below_cc_restr elim: set_mp[OF valid_lists_subset])

lemma ccApprox_ccFTree[simp]: "ccApprox (ccFTree S G) = cc_restr S G"
proof (transfer' fixing: S G, rule below_antisym)
  show "lub (ccFromList ` valid_lists S G) \<sqsubseteq> cc_restr S G"
    apply (rule is_lub_thelub_ex)
    apply (metis coCallsLub_is_lub)
    apply (rule is_ubI)
    apply clarify
    apply (erule valid_lists_ccFromList)
    done
next
  show "cc_restr S G \<sqsubseteq> lub (ccFromList ` valid_lists S G)"
  proof (rule below_CoCallsI)
    fix x y
    have "x--y\<in>(ccFromList [y,x])" by simp
    moreover
    assume "x--y\<in>(cc_restr S G)"
    hence "[y,x] \<in> valid_lists S G"  by (auto simp add: elem_ccNeighbors)
    ultimately
    show "x--y\<in>(lub (ccFromList ` valid_lists S G))"
      by (rule in_CoCallsLubI[OF _ imageI])
  qed
qed

lemma below_ccFTreeI:
  assumes "carrier t \<subseteq> S" and "ccApprox t \<sqsubseteq> G"
  shows "t \<sqsubseteq> ccFTree S G"
unfolding paths_mono_iff[symmetric] below_set_def
proof
  fix xs
  assume "xs \<in> paths t"
  with assms
  have "xs \<in> valid_lists S G"
  proof(induction xs arbitrary : t)
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    from `x # xs \<in> paths t`
    have "possible t x" and "xs \<in> paths (nxt t x)" by (auto simp add: Cons_path)

    have "ccProd {x} (set xs) \<sqsubseteq> ccFromList (x # xs)" by simp
    also
    from `x # xs \<in> paths t` 
    have "\<dots> \<sqsubseteq> ccApprox t"
      by (rule ccFromList_below_ccApprox)
    also
    note `ccApprox t \<sqsubseteq> G`
    finally
    have "ccProd {x} (set xs) \<sqsubseteq> G" by this simp_all
    hence "set xs \<subseteq> ccNeighbors {x} G" unfolding subset_ccNeighbors.
    moreover
    have "xs \<in> valid_lists S G"
    proof(rule Cons.IH)
      show "xs \<in> paths (nxt t x)" by fact
    next
      from `carrier t \<subseteq> S`
      show "carrier (nxt t x) \<subseteq> S" 
        by (rule order_trans[OF carrier_nxt_subset])
    next
      from `ccApprox t \<sqsubseteq> G`
      show "ccApprox (nxt t x) \<sqsubseteq> G" 
        by (rule below_trans[OF ccApprox_nxt_below])
    qed
    moreover
    from  `carrier t \<subseteq> S` and `possible t x`
    have "x \<in> S" by (rule carrier_possible_subset)
    ultimately
    show ?case..
  qed
    
  thus "xs \<in> paths (ccFTree S G)" by (metis paths_ccFTree)
qed    

lemma ccFTree_below_singleI:
  assumes "S \<inter> S' \<inter> ccManyCalls G = {}"
  shows "ccFTree S G \<sqsubseteq> singles S'"
proof-
  {
  fix xs x
  assume "x \<in> S'"

  assume "xs \<in> valid_lists S G"
  hence "length [x'\<leftarrow>xs . x' = x] \<le> Suc 0"
  proof(induction rule: valid_lists.induct[case_names Nil Cons])
    case Nil thus ?case by simp
  next
    case (Cons xs x')
    show ?case
    proof(cases "x' = x")
      case True with `x' \<in> S`
      have "x \<in> S" by simp
      from this `x \<in> S'`
      have "x--x\<notin>G" using assms by auto
      hence "x \<notin> ccNeighbors {x} G" by (metis elem_ccNeighbors)
      with Cons
      show ?thesis by (auto simp add: filter_empty_conv)
    next
      case False
      with Cons
      show ?thesis by auto
    qed
  qed
  }
  thus ?thesis by transfer auto
qed

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

lemma multi_calls_ccFTree:
  assumes "xs \<in> paths (ccFTree S G)"
  assumes "\<not> one_call_in_path x xs"
  shows "x \<in> S" and "x \<in> ccManyCalls G"
proof-
  from assms(1) have "xs \<in> valid_lists S G" by simp 

  have "x \<in> set xs" by (metis assms(2) filter_True one_call_in_path_filter)
  with `xs \<in> valid_lists S G`
  show "x \<in> S" by (metis  subsetCE valid_lists_subset)

  show "x \<in> ccManyCalls G"
  proof(rule ccontr)
    assume "x \<notin> ccManyCalls G"
    with `xs \<in> valid_lists S G` 
    have "one_call_in_path x xs"
    by (induction rule: valid_lists.induct) (auto simp add: no_call_in_path_set_conv)
    with assms(2)
    show False..
  qed
qed


text {* An alternative definition *}

inductive valid_lists' :: "var set \<Rightarrow> CoCalls \<Rightarrow> var set \<Rightarrow> var list \<Rightarrow> bool"
  for S G
  where  "valid_lists' S G prefix []"
  | "prefix \<subseteq> ccNeighbors {x} G \<Longrightarrow> valid_lists' S G (insert x prefix) xs \<Longrightarrow> x \<in> S \<Longrightarrow> valid_lists' S G prefix (x#xs)"

inductive_simps valid_lists'_simps[simp]: "valid_lists' S G prefix []" "valid_lists' S G prefix (x#xs)"
inductive_cases vald_lists'_ConsE: "valid_lists' S G prefix (x#xs)"

lemma valid_lists_valid_lists':
  "xs \<in> valid_lists S G \<Longrightarrow> ccProd prefix (set xs) \<sqsubseteq> G \<Longrightarrow> valid_lists' S G prefix xs"
proof(induction arbitrary: prefix rule: valid_lists.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons xs x)

  from Cons.prems Cons.hyps Cons.IH[where prefix = "insert x prefix"]
  show ?case
  by (auto simp add: insert_is_Un[where A = "set xs"]  insert_is_Un[where A = prefix]
                     join_below_iff subset_ccNeighbors elem_ccNeighbors ccProd_comm simp del: Un_insert_left )
qed

lemma valid_lists'_valid_lists_aux:
  "valid_lists' S G prefix xs \<Longrightarrow>  x \<in> prefix \<Longrightarrow> ccProd (set xs) {x} \<sqsubseteq> G"
proof(induction  rule: valid_lists'.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons prefix x xs)
  thus ?case
    apply (auto simp add: ccProd_insert2[where S' = prefix] ccProd_insert1[where S' = "set xs"] join_below_iff subset_ccNeighbors)
    by (metis Cons.hyps(1) dual_order.trans empty_subsetI insert_subset subset_ccNeighbors)
qed

lemma valid_lists'_valid_lists:
  "valid_lists' S G prefix xs \<Longrightarrow> xs \<in> valid_lists S G"
proof(induction  rule: valid_lists'.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons prefix x xs)
  thus ?case
    by (auto simp add: insert_is_Un[where A = "set xs"]  insert_is_Un[where A = prefix]
                   join_below_iff subset_ccNeighbors elem_ccNeighbors ccProd_comm simp del: Un_insert_left 
         intro: valid_lists'_valid_lists_aux)
qed

text {* Yet another definition *}

lemma valid_lists_characterization:
  "xs \<in> valid_lists S G \<longleftrightarrow> set xs \<subseteq> S \<and> (\<forall>n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G)"
proof(safe)
  fix x
  assume "xs \<in> valid_lists S G"
  from  valid_lists_subset[OF this]
  show "x \<in> set xs \<Longrightarrow> x \<in> S" by auto
next
  fix n
  assume "xs \<in> valid_lists S G"
  thus "ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G"
  proof(induction arbitrary: n rule: valid_lists.induct[case_names Nil Cons])
    case Nil thus ?case by simp
  next
    case (Cons xs x)
    show ?case
    proof(cases n)
      case 0 thus ?thesis by simp
    next
      case (Suc n)
      with Cons.hyps Cons.IH[where n = n]
      show ?thesis
      apply (auto simp add: ccProd_insert1[where S' = "set xs" for xs] join_below_iff subset_ccNeighbors)
      by (metis dual_order.trans set_drop_subset subset_ccNeighbors)
    qed
  qed
next
  assume "set xs \<subseteq> S"
  and "\<forall> n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G" 
  thus "xs \<in> valid_lists S G"
  proof (induction xs)
    case Nil thus ?case by simp
  next
    case (Cons x xs)
    from `\<forall>n. ccProd (set (take n (x # xs))) (set (drop n (x # xs))) \<sqsubseteq> G`
    have "\<forall>n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G"
      by -(rule, erule_tac x = "Suc n" in allE, auto simp add: ccProd_insert1[where S' = "set xs" for xs] join_below_iff)
    from Cons.prems Cons.IH[OF _ this]
    have "xs \<in> valid_lists S G" by auto
    with Cons.prems(1)  spec[OF `\<forall>n. ccProd (set (take n (x # xs))) (set (drop n (x # xs))) \<sqsubseteq> G`, where x = 1]
    show ?case by (simp add: subset_ccNeighbors)
  qed
qed
  


locale CoCallCardinality = CoCallAnalysis + CoCallAnalyisHeap + CorrectArityAnalysisLet' +
  assumes ccExp_App: "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a"
  assumes ccExp_Lam: "cc_restr (fv (Lam [y]. e)) (ccExp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> ccExp (Lam [y]. e)\<cdot>n"
  assumes ccExp_subst: "x \<notin>  S \<Longrightarrow> y \<notin> S \<Longrightarrow> cc_restr S (ccExp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (ccExp e\<cdot>a)"
  assumes ccExp_pap: "isLam e \<Longrightarrow> ccExp e\<cdot>0 = ccSquare (fv e)"
  assumes ccExp_Let: "cc_restr (-domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> ccExp (Let \<Gamma> e)\<cdot>a"
  (*
  assumes ccExp_ccField: "ccField (ccExp e\<cdot>a) \<subseteq> fv e"
  *)

  (*  assumes ccHeap_ccField: "ccField (ccHeap \<Gamma> e\<cdot>a) \<subseteq> domA \<Gamma>" *)
  
  (*
  assumes linear_Exp: "isLinear \<Delta> e a \<Longrightarrow> ccLinear (domA \<Delta>) (ccExp e\<cdot>a)"
  assumes linear_Heap: "isLinear \<Delta> e a \<Longrightarrow> map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x= up\<cdot>a' \<Longrightarrow> ccLinear (domA \<Delta>) (ccExp e'\<cdot>a')"
  *)

  assumes ccHeap_Exp: "ccExp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  assumes ccHeap_Heap: "map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x= up\<cdot>a' \<Longrightarrow> ccExp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  assumes ccHeap_Extra_Edges:
    "map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x = up\<cdot>a' \<Longrightarrow> ccProd (fv e') (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  
  assumes aHeap_thunks: "x \<in> thunks \<Gamma> \<Longrightarrow> x \<in> edom (Aheap \<Gamma> e\<cdot>a) \<Longrightarrow> x \<notin> calledOnce \<Gamma> e a \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"

  
  assumes calledOnce_exp: "calledOnce \<Delta> e a \<inter> ccManyCalls (ccExp e\<cdot>a) = {}"
  assumes calledOnce_heap: "map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x = up\<cdot>u' \<Longrightarrow> edom (Aexp e'\<cdot>u') \<inter> calledOnce \<Delta> e a = {}"

begin

(*
lemma cc_restr_ccExp': "cc_restr (fv e) (ccExp e\<cdot>a) = ccExp e\<cdot>a"
  by (rule cc_restr_noop[OF ccExp_ccField])
*)

definition Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fexp e = (\<Lambda> a. ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a))"

lemma Fexp_simp: "Fexp e\<cdot>a = ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a)"
  unfolding Fexp_def sorry

lemma carrier_Fexp': "carrier (Fexp e\<cdot>a) \<subseteq> fv e"
  unfolding Fexp_simp carrier_ccFTree
  by (rule Aexp_edom)

sublocale FutureAnalysis Fexp.

sublocale FutureAnalysisCarrier Fexp
  by default (rule carrier_Fexp')

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
  also have "ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))) = ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} ({x} \<union> (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (simp add: ccProd_union2[symmetric] del: ccProd_union2)
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

definition Fheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fheap \<Gamma> e = (\<Lambda> a. ftree_restr (edom (Aheap \<Gamma> e\<cdot>a)) (singles (calledOnce \<Gamma> e a)))"

lemma Fheap_simp: "Fheap \<Gamma> e\<cdot>a = ftree_restr (edom (Aheap \<Gamma> e\<cdot>a)) (singles (calledOnce \<Gamma> e a))"
  unfolding Fheap_def sorry

lemma carrier_Fheap':"carrier (Fheap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    unfolding Fheap_simp carrier_ccFTree by simp

lemma carrier_substitute_aux:
  assumes "xs \<in> paths (substitute f T t)"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A" 
  shows   "set xs \<subseteq> A"
  using assms
  apply(induction  f T t xs rule: substitute_induct)
  apply auto
  apply (metis carrier_possible_subset)
  apply (metis carrier_f_nxt carrier_nxt_subset carrier_possible_subset contra_subsetD order_trans)
  done

text {*
It is tricky to relate @{term substitute} and @{term ccApprox}.
We do this separately for no-recursive bindings, linearly-recursive bindings and others.
*}



 
lemma ccFromList_filter[simp]:
  "ccFromList (filter P xs) = cc_restr {x. P x} (ccFromList xs)"
by (induction xs) (auto simp add: Collect_conj_eq)

lemma cc_restr_Compl_eq[simp]:
  "cc_restr {x. x \<notin> S} = cc_restr (-S)"
  by (metis Compl_eq)


lemma substitute_not_carrier:
  assumes "x \<notin> carrier t"
  assumes "\<And> x'. x \<notin> carrier (f x')"
  shows "x \<notin>  carrier (substitute f T t)"
proof-
  have "ftree_restr ({x}) (substitute f T t) = ftree_restr ({x}) t"
  proof(rule ftree_rest_substitute)
    fix x'
    from `x \<notin> carrier (f x')`
    show "carrier (f x') \<inter> {x} = {}" by auto
  qed
  hence "x \<notin> carrier (ftree_restr ({x}) (substitute f T t)) \<longleftrightarrow> x \<notin> carrier (ftree_restr ({x}) t)" by metis
  with assms(1)
  show ?thesis by simp
qed




lemma both_below_singles1:
  assumes "t \<sqsubseteq> singles S"
  assumes "carrier t' \<inter> S = {}"
  shows "t \<otimes>\<otimes> t' \<sqsubseteq> singles S"
proof (rule ftree_belowI)
  fix xs
  assume "xs \<in> paths (t \<otimes>\<otimes> t')"
  then obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> ys \<otimes> zs" by (auto simp add: paths_both)
  with assms 
  have "ys \<in> paths (singles S)" and "set zs \<inter> S = {}"
    by (metis below_ftree.rep_eq contra_subsetD paths.rep_eq, auto simp add: Union_paths_carrier[symmetric])
  with `xs \<in> ys \<otimes> zs`
  show "xs \<in> paths (singles S)"
    by (induction) (auto simp add: paths_singles no_call_in_path_set_conv interleave_set dest: more_than_one_setD split: if_splits)
qed

lemma substitute_below_singlesI:
  assumes "t \<sqsubseteq> singles S"
  assumes "\<And> x. carrier (f x) \<inter> S = {}"
  shows "substitute f T t \<sqsubseteq> singles S"
proof(rule ftree_belowI)
  fix xs
  assume "xs \<in> paths (substitute f T t)"
  thus "xs \<in> paths (singles S)"
  using assms
  proof(induction f T t xs arbitrary: S rule: substitute_induct)
    case Nil
    thus ?case by simp
  next
    case (Cons f T t x xs)

    from `x#xs \<in> _`
    have xs: "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by auto
    moreover

    from `t \<sqsubseteq> singles S`
    have "nxt t x \<sqsubseteq> singles S" 
      by (metis "FTree-HOLCF.nxt_mono" below_trans nxt_singles_below_singles)
    from this `carrier (f x) \<inter> S = {}`
    have "nxt t x \<otimes>\<otimes> f x \<sqsubseteq> singles S"
      by (rule both_below_singles1)
    moreover
    { fix x'
      from  `carrier (f x') \<inter> S = {}`
      have "carrier (f_nxt f T x x') \<inter> S = {}"
        by (auto simp add: f_nxt_def)
    }
    ultimately
    have IH: "xs \<in> paths (singles S)"
      by (rule Cons.IH) 
  
  show ?case
    proof(cases "x \<in> S")
      case True
      with `carrier (f x) \<inter> S = {}`
      have "x \<notin> carrier (f x)" by auto
      moreover
      from `t \<sqsubseteq> singles S`
      have "nxt t x \<sqsubseteq> nxt (singles S) x" by (rule nxt_mono)
      hence "carrier (nxt t x) \<subseteq> carrier (nxt (singles S) x)" by (rule carrier_mono)
      from set_mp[OF this] True
      have "x \<notin> carrier (nxt t x)" by auto
      ultimately
      have "x \<notin> carrier (nxt t x \<otimes>\<otimes> f x)" by simp
      hence "x \<notin> carrier (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))"
      proof(rule substitute_not_carrier)
        fix x'  
        from `carrier (f x') \<inter> S = {}` `x \<in> S`
        show "x \<notin> carrier (f_nxt f T x x')" by (auto simp add: f_nxt_def)
      qed
      with xs
      have "x \<notin> set xs" by (auto simp add: Union_paths_carrier[symmetric])
      with IH
      have "xs \<in> paths (without x (singles S))" by (rule paths_withoutI)
      thus ?thesis using True by (simp add: Cons_path)
    next
      case False
      with IH
      show ?thesis by (simp add: Cons_path)
    qed
  qed
qed

(*
lemma linear_recursion:
  assumes "ccLinear S (ccApprox t)"
  assumes "ccApprox  t \<sqsubseteq> G"
  assumes "\<And> x. x \<notin> S \<Longrightarrow> f x = empty"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccLinear S (ccApprox (f x))"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccProd (ccNeighbors S G) (carrier (f x)) \<sqsubseteq> G"
  shows "ccApprox (ftree_restr (-S) (substitute f {} t)) \<sqsubseteq> G"
proof(rule ccApprox_belowI)
  fix xs

  def seen \<equiv> "{} :: var set"

  assume "xs \<in> paths (ftree_restr (- S) (substitute f {} t))"
  then obtain xs' xs'' T where "xs = [x\<leftarrow>xs' . x \<notin> S]" and "substitute'' f T xs'' xs'" and "T = {}" and "xs'' \<in> paths t"
    by (auto simp add: filter_paths_conv_free_restr2[symmetric] substitute_substitute'')
 
  note this(2,3)
  moreover
  from `ccLinear S (ccApprox t)` and `ccApprox t \<sqsubseteq> G` and `xs'' \<in> paths t`
  have "ccLinear S (ccFromList xs'')" and "ccFromList xs'' \<sqsubseteq> G"
    by (auto simp add: ccLinear_ccApprox ccApprox_below_iff)
  moreover
  note assms(3)
  moreover
  from assms(4-6)
  have "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccLinear S (ccFromList ys)"
    and "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccFromList ys \<sqsubseteq> G"
    and "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccProd (ccNeighbors S G) (set ys) \<sqsubseteq> G"
    by (auto simp add: ccLinear_ccApprox ccApprox_below_iff Union_paths_carrier[symmetric] cc_lub_below_iff)
  moreover
  have "ccProd seen (set xs'') \<sqsubseteq> G" unfolding seen_def by simp
  ultimately 
  have "ccFromList [x\<leftarrow>xs' . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set xs') \<sqsubseteq> G"
  proof(induction f T xs'' xs' arbitrary: seen rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs f x xs' xs T ys)
    from `T = {}` have [simp]: "f_nxt f T x = f" by (simp add: f_nxt_def)

    have seen_x: "ccProd seen {x} \<sqsubseteq> G"
      using Cons.prems
      by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)

    show ?case
    proof(cases "x \<in> S")
      case True

      from Cons.prems
      have "ccProd {x} (set xs) \<sqsubseteq> G" by (auto simp add: join_below_iff)
      with `x \<in> S`
      have subset1: "set xs \<subseteq> ccNeighbors S G" by transfer auto

      from Cons.prems
      have "seen \<subseteq> ccNeighbors {x} G"
        by (auto simp add: subset_ccNeighbors ccProd_insert2[where S' = "set xs" for xs] join_below_iff ccProd_comm)
      hence subset2: "seen \<subseteq> ccNeighbors S G" 
        by (rule order_trans[OF _ ccNeighbors_mono[OF insert_subsetI[OF  `x \<in> S`  empty_subsetI] below_refl]])
        
      from True Cons.prems Cons.hyps
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set ys) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH)
        apply (auto simp add: ccApprox_both join_below_iff ftree_restr_both interleave_ccFromList interleave_set  ccProd_insert2[where S' = "set xs" for xs]
                   intro: below_trans[OF ccProd_mono1[OF subset1]]  below_trans[OF ccProd_mono1[OF subset2]])
        done
      with True seen_x
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G  \<and> ccProd seen (set (x#ys)) \<sqsubseteq> G" 
        by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)
    next
      case False
  
      from False Cons.prems Cons.hyps
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (insert x seen) (set ys) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH[where seen = "insert x seen"])
        apply (auto simp add: ccApprox_both join_below_iff ftree_restr_both interleave_ccFromList
                   simp add:  ccProd_insert2[where S' = "set xs" for xs]
                   simp add:  ccProd_insert1[where S' = "seen"])
        done
      moreover
      from this
      have "ccProd {x} (set ys) \<sqsubseteq>  G"
        by (auto simp add: ccProd_insert1[where S' = "seen"] join_below_iff)
      hence "ccProd {x} {x \<in> set ys. x \<notin> S} \<sqsubseteq> G"
        by (rule below_trans[rotated, OF _ ccProd_mono2]) auto
      moreover
      note False seen_x
      ultimately
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set (x # ys)) \<sqsubseteq> G"
        by (auto simp add: join_below_iff  simp add:  ccProd_insert2[where S' = "set xs" for xs]   ccProd_insert1[where S' = "seen"])
    qed
  qed
  with `xs = _`
  show "ccFromList xs \<sqsubseteq> G" by simp
qed
*)

(*
text {*
It is tricky to relate @{term substitute} and @{term ccApprox}. This inductive definition
should help separating this proof into several steps.
*}

inductive called_via :: "(var \<Rightarrow> var ftree) \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
 where "y \<in> carrier (f x) \<Longrightarrow> called_via f x y"
     | "called_via f x y \<Longrightarrow> called_via f y z \<Longrightarrow> called_via f x z"

inductive
  substitute_co_call :: "var \<Rightarrow> var \<Rightarrow> (var \<Rightarrow> var ftree) \<Rightarrow> var ftree \<Rightarrow> bool"
where
    "x--y\<in>(ccApprox t) \<Longrightarrow> called_via f x x' \<Longrightarrow> called_via f y y' \<Longrightarrow> substitute_co_call x' y' f t"

thm substitute''.intros
lemma ccApprox_substitute_co_call:
  assumes "x--y\<in>(ccApprox (substitute f T t))"
  shows   "substitute_co_call x y f t"
proof-
  from assms
  obtain xs where "xs \<in> paths (substitute f T t)" and "x--y\<in>(ccFromList xs)"
    by (auto simp add: in_ccApprox)
  from this(1)
  obtain xs' where "substitute'' f T xs' xs"  and "xs' \<in> paths t"  by (auto simp add: substitute_substitute'')
  from this `x--y\<in>(ccFromList xs)`
  show  "substitute_co_call x y f t"
  proof(induction arbitrary: t rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs f x' xs' xs T ys)
    from `x' # xs \<in> paths t`
    have "possible t x'" and  "xs \<in> paths (nxt t x')"
      by (auto simp add: Cons_path)
    
    from this(2) and `xs' \<in> xs \<otimes> zs` and `zs \<in> paths (f x')`
    have "xs' \<in> paths (nxt t x' \<otimes>\<otimes> f x')" by (auto simp add: paths_both)

    {
    assume "x--y\<in>(ccFromList ys)"
    from Cons.IH[OF `xs' \<in> paths (nxt t x' \<otimes>\<otimes> f x')` this]
    have "substitute_co_call x y (f_nxt f T x') (nxt t x' \<otimes>\<otimes> f x')".
    
    have ?case sorry
    }
    moreover
    
    ultimately
    show ?case using  `x--y\<in>(ccFromList (x' # ys))`
      apply auto

    { assume "x' \<noteq> x" and "x' \<noteq> y"
      with `x--y\<in>(ccFromList (x' # xs))`
      have "x--y\<in>(ccFromList xs)" by simp
      from Cons.IH[OF `xs \<in> _ ` this]
      have "substitute_co_call x y (f_nxt f T x') (nxt t x' \<otimes>\<otimes> f x')".
      then obtain x0 y0 where "x0--y0\<in>(ccApprox (nxt t x' \<otimes>\<otimes> f x'))"
                          and "called_via (f_nxt f T x') x0 x"
                          and "called_via (f_nxt f T x') y0 y" by (auto elim: substitute_co_call.cases)

      from `called_via (f_nxt f T x') x0 x`
      have "called_via f x0 x" sorry
      from `called_via (f_nxt f T x') y0 y`
      have "called_via f y0 y" sorry


      from `x0--y0\<in>(ccApprox (nxt t x' \<otimes>\<otimes> f x'))`
      have ?case
      proof(auto simp add: ccApprox_both)
        assume "x0--y0\<in>(ccApprox (f x'))"
        show ?thesis   sorry
      next
        assume "x0--y0\<in>(ccApprox (nxt t x'))"
        hence "x0--y0\<in>(ccApprox t)" sorry
        moreover
        note `called_via f x0 x`
        moreover
        note `called_via f y0 y`
        ultimately
        show ?thesis..
     next
       assume "x0 \<in> carrier (nxt t x')"
       hence "x0--x' \<in>(ccApprox t)" sorry
       moreover
       note `called_via f x0 x`
       moreover
       assume "y0 \<in> carrier (f x')"
       hence "called_via f x' y0" sorry
       from this  `called_via f y0 y`
       have "called_via f x' y" sorry
       ultimately
       show ?thesis..
    next
       assume "y0 \<in> carrier (nxt t x')"
       hence "x'--y0 \<in>(ccApprox t)" sorry
       moreover
       assume "x0 \<in> carrier (f x')"
       hence "called_via f x' x0" sorry
       from this  `called_via f x0 x`
       have "called_via f x' x" sorry
       moreover
       note `called_via f y0 y`
       ultimately
       show ?thesis..
    qed
    }
    
    show ?case
oops
*)

(*
lemma ccApprox_substitute_aux:
  assumes "substitute'' f T xs ys"
  assumes "ccFromList (prefix@xs) \<sqsubseteq> G"
  assumes "\<And> x. x \<in> set ys \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G" 
  shows   "ccFromList (prefix@ys) \<sqsubseteq> G"
using assms
proof(induction f T xs ys arbitrary: prefix rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons zs f x xs' xs T ys)
  from `ccFromList (prefix @ x # xs) \<sqsubseteq> G`
  have  "ccFromList prefix \<sqsubseteq> G"
    and "ccProd (set prefix) (insert x (set xs)) \<sqsubseteq> G"
    and "ccProd {x} (set xs) \<sqsubseteq> G"
    and "ccFromList xs \<sqsubseteq> G"
    by (auto simp add: join_below_iff)

  from Cons have "ccApprox (f x) \<sqsubseteq> G" and *: "\<And>x. x \<in> set ys \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G" by auto
  with Cons.hyps(1)
  have "ccFromList zs \<sqsubseteq> G" by (metis below_trans ccFromList_below_ccApprox) 
  
  have "ccFromList ((prefix@[x])@ys) \<sqsubseteq> G"
  proof (rule Cons.IH)
    have "ccProd {x} (set zs) \<sqsubseteq> G" sorry
    moreover
    have "ccFromList zs \<sqsubseteq> G" by fact
    moreover
    have "ccProd (set xs) (set zs) \<sqsubseteq> G" sorry
    moreover
    have "ccProd (set prefix) (set zs) \<sqsubseteq> G" sorry
    moreover
    note `ccFromList (prefix @ x # xs) \<sqsubseteq> G`
    ultimately
    show "ccFromList ((prefix @ [x]) @ xs') \<sqsubseteq> G"    
      using interleave_ccFromList[OF `xs' \<in> xs \<otimes> zs`] interleave_set[OF  `xs' \<in> xs \<otimes> zs`]
          by (auto simp add: ccApprox_both join_below_iff ccProd_insert2[where S' = "S \<union> S'" for S S'] ccProd_insert2[where S' = "set xs" for xs])
  next
    fix x'
    assume "x' \<in> set ys"
    thus "ccApprox (f_nxt f T x x') \<sqsubseteq> G" sorry
  qed
  moreover
  thm Cons
  have "ccProd {x} (set ys) \<sqsubseteq> G" sorry
  ultimately
  show ?case by simp
qed

lemma ccFTree_Let:
  assumes "isLinear \<Delta> e a"
  shows "ccFTree (edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)) (ccHeap \<Delta> e\<cdot>a) \<sqsubseteq>
         ccFTree (edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a)) (ccExp (Let \<Delta> e)\<cdot>a)"
 using Aexp_Let[of \<Delta> e a]  ccExp_Let_linear[OF assms] 
 by (rule below_trans[OF ccFTree_mono1[OF edom_mono] ccFTree_mono2])

lemma substitute'_valid_list:
  assumes "xs \<in> paths (substitute f (thunks \<Delta>) t)"
  assumes "f = env_restr (- (S \<inter> thunks \<Delta>)) (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))" 
  assumes "ccProd (carrier t) S \<sqsubseteq> ccBindsExtra \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a, ccHeap \<Delta> e\<cdot>a) \<squnion> ccExp e\<cdot>a"
  shows   "valid_lists' (edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)) (ccBindsExtra \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a, ccHeap \<Delta> e\<cdot>a) \<squnion> ccExp e\<cdot>a) S xs"
using assms
proof(induction  f "thunks \<Delta>" t xs arbitrary: S rule: substitute_induct)
  case Nil
  thus ?case by simp
next
  case (Cons f t x xs)

  from `x # xs \<in> paths (substitute f (thunks \<Delta>) t)`
  have "possible t x" and "xs \<in> paths (substitute (f_nxt f (thunks \<Delta>) x) (thunks \<Delta>) (nxt t x \<otimes>\<otimes> f x))"
    by auto

  note this(2)
  moreover

  have [simp]: "(- {x} \<inter> (- S \<union> - thunks \<Delta>)) = (- insert x (S \<inter> thunks \<Delta>))" by auto
    
  from  Cons.prems(2)
  have "f_nxt f (thunks \<Delta>) x = env_restr (-(insert x S \<inter> thunks \<Delta>)) (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))"
    by (cases "x \<in> thunks \<Delta>")
       (auto simp add: f_nxt_def env_delete_def[symmetric] empty_is_bottom env_delete_restr)
  moreover
  from below_trans[OF ccProd_mono1[OF carrier_nxt_subset] `ccProd (carrier t) _ \<sqsubseteq> _`]
  have "ccProd (carrier (nxt t x \<otimes>\<otimes> f x)) (insert x S) \<sqsubseteq> ccBindsExtra \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a, ccHeap \<Delta> e\<cdot>a) \<squnion> ccExp e\<cdot>a" 
    apply (auto simp add: join_below_iff ccProd_insert2[where S' = S])
    thm ccProd_mono1[OF carrier_nxt_subset]
    sor ry
  ultimately
  have IH: "valid_lists' (edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)) (ccBindsExtra \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a, ccHeap \<Delta> e\<cdot>a) \<squnion> ccExp e\<cdot>a) (insert x S) xs"  
    by (rule Cons.hyps)

  have "x \<in> carrier t" by (metis `possible t x` carrier_possible)
  hence "ccProd {x} S \<sqsubseteq> ccProd (carrier t) S" by (auto intro: ccProd_mono1)
  with `ccProd (carrier t) _ \<sqsubseteq> _`
  have "S \<subseteq> ccNeighbors {x} (ccBindsExtra \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a, ccHeap \<Delta> e\<cdot>a) \<squnion> ccExp e\<cdot>a)"
    unfolding subset_ccNeighbors
    by (rule below_trans[rotated])
  moreover
  note IH
  moreover
  have "x \<in> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)" sorry
  ultimately
  show ?case..
qed
*)

lemma in_carrier_fup[simp]:
  "x' \<in> carrier (fup\<cdot>f\<cdot>u) \<longleftrightarrow> (\<exists> u'. u = up\<cdot>u' \<and> x' \<in> carrier (f\<cdot>u'))"
  by (cases u) auto

sublocale FutureAnalysisCardinalityHeap Fexp Aexp Aheap Fheap
proof default
  fix \<Gamma> e a
  show "carrier (Fheap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    by (rule carrier_Fheap')
next
  fix x \<Gamma> p e a
  assume "x \<in> thunks \<Gamma>"
  moreover
  assume "p \<in> paths (Fheap \<Gamma> e\<cdot>a)" "\<not> one_call_in_path x p"
  hence "x \<in> edom (Aheap \<Gamma> e\<cdot>a)" and  "\<not> x\<in> calledOnce \<Gamma> e a"
    unfolding Fheap_simp
    by (auto simp add: paths_ftree_restr_singles dest: more_than_one_setD)
  ultimately
  show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
    by (rule aHeap_thunks)
next
  fix \<Delta> e a

  show "ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>)  (Fexp e\<cdot>a)) \<sqsubseteq> Fexp (Let \<Delta> e)\<cdot>a"
  unfolding Fexp_simp
  proof (rule below_ccFTreeI)
    have "carrier (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
       = carrier (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))) - domA \<Delta>"
        by auto
    also
    have "carrier (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)))
         \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
    proof (rule carrier_substitute_below)
    show "carrier (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)" by simp
    next
      fix x
      assume "x \<in> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
      show "carrier ((ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
      proof(cases "map_of \<Delta> x")
        case None thus ?thesis by (simp add: Fexp.AnalBinds_lookup)
      next
        case (Some e')
        hence "carrier ((ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) = carrier (fup\<cdot>(Fexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))"
            by (simp add: Fexp.AnalBinds_lookup)
        also have "\<dots> \<subseteq> edom (fup\<cdot>(Aexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))"
          by (auto simp add: Fexp_simp)
        also have "\<dots> = edom (ABind x e'\<cdot>(Aheap \<Delta> e\<cdot>a))" by (simp add: ABind_def Aexp'_def)
        also have "\<dots> \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))" using Some
          by (rule edom_mono[OF monofun_cfun_fun[OF ABind_below_ABinds]])
        also have "\<dots> \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)" by simp
        finally show ?thesis.
      qed
    qed
    also have "\<dots> \<subseteq> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a)"
      by (rule edom_mono[OF Aexp_Let])
    also have "edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a) - domA \<Delta> = edom (Aexp (Let \<Delta> e)\<cdot>a)"
      by (auto dest: set_mp[OF edom_Aheap] set_mp[OF Aexp_edom])
    finally
    show "carrier (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
          \<subseteq> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)"  by this auto
  next

    have "ccApprox (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
      \<sqsubseteq> ccApprox (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) {} (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))"
      by (intro ccApprox_mono ftree_restr_mono[folded paths_mono_iff, unfolded below_set_def] substitute_monoT) auto
    also have "\<dots> = cc_restr (- domA \<Delta>) \<dots>"  by simp
    also have "\<dots> \<sqsubseteq> cc_restr (- domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)"
    proof(rule cc_restr_mono2[OF wild_recursion])
    (*
      have "ccLinear (domA \<Delta>) (ccExp e\<cdot>a)" using linear by (rule linear_Exp)
      thus "ccLinear (domA \<Delta>) (ccApprox (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)))"
        by auto
    next
    *)
      have "ccExp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Exp)
      thus "ccApprox (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
        by (auto intro: below_trans[OF cc_restr_below_arg])
    next
      fix x
      assume "x \<notin> domA \<Delta>"
      thus "(Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x = empty"
        by (metis Fexp.AnalBinds_not_there empty_is_bottom)
    next
      fix x
      assume "x \<in> domA \<Delta>"
      then obtain e' where e': "map_of \<Delta> x = Some e'" by (metis domA_map_of_Some_the)
      
      (*
      thus "ccLinear (domA \<Delta>) (ccApprox ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x))"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        with linear e'
        have "ccLinear (domA \<Delta>) (ccExp e'\<cdot>a')" by (rule linear_Heap)
        thus ?thesis using up e' by (auto simp add: Fexp.AnalBinds_lookup Fexp_simp)
      qed
      *)
      
      show "ccApprox ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        with e'
        have "ccExp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Heap)
        thus ?thesis using up e'
          by (auto simp add: Fexp.AnalBinds_lookup Fexp_simp  intro: below_trans[OF cc_restr_below_arg])
      qed

      show "ccProd (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)) (carrier ((Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        have subset: "(carrier (fup\<cdot>(Fexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))) \<subseteq> fv e'"
          using up e' by (simp add: Fexp.AnalBinds_lookup carrier_Fexp)
        
        from e' up
        have "ccProd (fv e') (ccNeighbors (domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"  
          by (rule ccHeap_Extra_Edges)
        then
        show ?thesis using e'
          by (simp add: Fexp.AnalBinds_lookup  Fexp_simp ccProd_comm  below_trans[OF ccProd_mono2[OF subset]])
      qed
    qed
    also have "\<dots> \<sqsubseteq> ccExp (Let \<Delta> e)\<cdot>a"
      by (rule ccExp_Let)
    finally
    show "ccApprox (ftree_restr (- domA \<Delta>) (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
        \<sqsubseteq> ccExp (Terms.Let \<Delta> e)\<cdot>a" by this simp_all

  qed

  have "ftree_restr (domA \<Delta>)            (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
      = ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))"
    sorry
  also
  have "substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a) \<sqsubseteq> singles (calledOnce \<Delta> e a)"
  proof(rule substitute_below_singlesI)
    show "Fexp e\<cdot>a \<sqsubseteq> singles (calledOnce \<Delta> e a)"
      unfolding Fexp_simp
      using calledOnce_exp
      by (auto intro!: ccFTree_below_singleI)
  next
    fix x
    show "carrier ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<inter> calledOnce \<Delta> e a = {}"
      using calledOnce_heap[unfolded disjoint_iff_not_equal]
      by (force simp add: Fexp.AnalBinds_lookup Fexp_simp split: option.split)
  qed
  hence "ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
      \<sqsubseteq> ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (singles (calledOnce \<Delta> e a))"
    by (rule ftree_restr_mono)
  also have "\<dots> = Fheap \<Delta> e\<cdot>a"
    unfolding Fheap_simp..
  finally
  show "ftree_restr (domA \<Delta>) (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<sqsubseteq> Fheap \<Delta> e\<cdot>a".

qed
end

end
