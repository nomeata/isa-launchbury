theory FTree
imports Main ConstOn "List-Interleavings"
begin

subsection {* Prefix-closed sets of lists *}

definition downset where
  "downset xss = (\<forall>x n. x \<in> xss \<longrightarrow> take n x \<in> xss)"

lemma downsetE[elim]:
  "downset xss  \<Longrightarrow> xs \<in> xss \<Longrightarrow> butlast xs \<in> xss"
by (auto simp add: downset_def butlast_conv_take)

lemma downset_appendE[elim]:
  "downset xss \<Longrightarrow> xs@ys \<in> xss \<Longrightarrow> xs \<in> xss"
by (auto simp add: downset_def) (metis append_eq_conv_conj)

lemma downset_hdE[elim]:
  "downset xss \<Longrightarrow> xs \<in> xss \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> [hd xs] \<in> xss"
by (auto simp add: downset_def) (metis take_0 take_Suc)


lemma downsetI[intro]:
  assumes "\<And> xs. xs \<in> xss \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> butlast xs \<in> xss"
  shows  "downset xss"
unfolding downset_def
proof(intro impI allI )
  from assms
  have butlast: "\<And> xs. xs \<in> xss \<Longrightarrow> butlast xs \<in> xss"
    by (metis butlast.simps(1))

  fix xs n
  assume "xs \<in> xss"
  show "take n xs \<in> xss"
  proof(cases "n \<le> length xs")
  case True
    from this
    show ?thesis
    proof(induction rule: inc_induct)
    case base with `xs \<in> xss` show ?case by simp
    next
    case (step n')
      from butlast[OF step.IH] step(2)
      show ?case by (simp add: butlast_take)
    qed      
  next
  case False with `xs \<in> xss` show ?thesis by simp
  qed
qed

lemma [simp]: "downset {[]}" by auto

lemma downset_mapI: "downset xss \<Longrightarrow> downset (map f ` xss)"
  by (fastforce simp add: map_butlast[symmetric])

lemma downset_filter:
  assumes "downset xss"
  shows "downset (filter P ` xss)"
proof(rule, elim imageE, clarsimp)
  fix xs
  assume "xs \<in> xss"
  thus "butlast (filter P xs) \<in> filter P ` xss"
  proof (induction xs rule: rev_induct)
    case Nil thus ?case by force
  next
    case snoc
    thus ?case using `downset xss`  by (auto intro: snoc.IH)
  qed
qed

subsection {* The type of infinite labled trees *}

typedef 'a ftree = "{xss :: 'a list set . [] \<in> xss \<and> downset xss}" by auto

setup_lifting type_definition_ftree

subsection {* Deconstructors *}

lift_definition possible ::"'a ftree \<Rightarrow> 'a \<Rightarrow> bool"
  is "\<lambda> xss x. \<exists> xs. x#xs \<in> xss".

lift_definition nxt ::"'a ftree \<Rightarrow> 'a \<Rightarrow> 'a ftree"
  is "\<lambda> xss x. insert [] {xs | x' xs . x'#xs \<in> xss \<and> x' = x}"
  apply (auto simp add: downset_def)
  by (metis take_Suc_Cons)

subsection {* Trees as set of paths *}

lift_definition paths :: "'a ftree \<Rightarrow> 'a list set" is "(\<lambda> x. x)".

lemma paths_inj: "paths t = paths t' \<Longrightarrow> t = t'" by transfer auto

lemma paths_injs_simps[simp]: "paths t = paths t' \<longleftrightarrow> t = t'" by transfer auto

lemma paths_Nil[simp]: "[] \<in> paths t" by transfer simp

lemma paths_Cons_nxt:
  "possible t x \<Longrightarrow> xs \<in> paths (nxt t x) \<Longrightarrow> (x#xs) \<in> paths t"
  by transfer auto

lemma paths_Cons_nxt_iff:
  "possible t x \<Longrightarrow> xs \<in> paths (nxt t x) \<longleftrightarrow> (x#xs) \<in> paths t"
  by transfer auto

lemma possible_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> possible t x \<Longrightarrow> possible t' x"
  by transfer auto

lemma nxt_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (nxt t x) \<subseteq> paths (nxt t' x)"
  by transfer auto

lemma ftree_eqI: "(\<And> x xs. x#xs \<in> paths t \<longleftrightarrow> x#xs \<in> paths t') \<Longrightarrow> t = t'"
  apply (rule paths_inj)
  apply (rule set_eqI)
  apply (case_tac x)
  apply auto
  done

lemma paths_nxt[elim]:
 assumes "xs \<in> paths (nxt t x)"
 obtains "x#xs \<in> paths t"  | "xs = []"
 using assms by transfer auto

lemma Cons_path: "x # xs \<in> paths t \<longleftrightarrow> possible t x \<and> xs \<in> paths (nxt t x)"
 by transfer auto

lemma Cons_pathI[intro]:
  assumes "possible t x \<longleftrightarrow> possible t' x"
  assumes "possible t x \<Longrightarrow> possible t' x \<Longrightarrow> xs \<in> paths (nxt t x) \<longleftrightarrow> xs \<in> paths (nxt t' x)"
  shows  "x # xs \<in> paths t \<longleftrightarrow> x # xs \<in> paths t'"
using assms by (auto simp add: Cons_path)

lemma paths_nxt_eq: "xs \<in> paths (nxt t x) \<longleftrightarrow> xs = [] \<or> x#xs \<in> paths t"
 by transfer auto

lemma ftree_coinduct:
  assumes "P t t'"
  assumes "\<And> t t' x . P t t' \<Longrightarrow> possible t x \<longleftrightarrow> possible t' x"
  assumes "\<And> t t' x . P t t' \<Longrightarrow> possible t x \<Longrightarrow> possible t' x \<Longrightarrow> P (nxt t x) (nxt t' x)"
  shows "t = t'"
proof(rule paths_inj, rule set_eqI)
  fix xs
  from assms(1)
  show "xs \<in> paths t \<longleftrightarrow> xs \<in> paths t'"
  proof (induction xs arbitrary: t t')
  case Nil thus ?case by simp
  next
  case (Cons x xs t t')
    show ?case
    proof (rule Cons_pathI)
      from `P t t'`
      show "possible t x \<longleftrightarrow> possible t' x" by (rule assms(2))
    next
      assume "possible t x" and "possible t' x"
      with `P t t'`
      have "P (nxt t x) (nxt t' x)" by (rule assms(3))
      thus "xs \<in> paths (nxt t x) \<longleftrightarrow> xs \<in> paths (nxt t' x)" by (rule Cons.IH)
    qed
  qed
qed



subsection {* Repeatable trees *}

definition repeatable where "repeatable t = (\<forall>x . possible t x \<longrightarrow> nxt t x = t)"

lemma nxt_repeatable[simp]: "repeatable t \<Longrightarrow> possible t x \<Longrightarrow> nxt t x = t"
  unfolding repeatable_def by auto
 
subsubsection {* Simple trees *}

lift_definition empty :: "'a ftree" is "{[]}" by auto

lemma possible_empty[simp]: "possible empty x' \<longleftrightarrow> False"
  by transfer auto

lemma nxt_not_possible[simp]: "\<not> possible t x \<Longrightarrow> nxt t x = empty"
  by transfer auto

lemma paths_empty[simp]: "paths empty = {[]}" by transfer auto

lift_definition single :: "'a \<Rightarrow> 'a ftree" is "\<lambda> x. {[], [x]}"
  by auto

lemma possible_single[simp]: "possible (single x) x' \<longleftrightarrow> x = x'"
  by transfer auto

lemma nxt_single[simp]: "nxt (single x) x' =  empty"
  by transfer auto

lift_definition and_then :: "'a \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> x xss. insert [] (op # x ` xss)"
  by (auto intro!: downsetI split: if_splits)

lemma possible_and_then[simp]: "possible (and_then x t) x' \<longleftrightarrow> x = x'"
  by transfer auto

lemma nxt_and_then[simp]: "nxt (and_then x t) x = t"
  by transfer auto

lemma paths_and_then_Cons[simp]: "x'#xs \<in> paths (and_then x t) \<longleftrightarrow> x' = x \<and> xs \<in> paths t"
 by transfer force
 
lift_definition many_calls :: "'a \<Rightarrow> 'a ftree" is "\<lambda> x. range (\<lambda> n. replicate n x)"
  by (auto simp add: downset_def)

lemma possible_many_calls[simp]: "possible (many_calls x) x' \<longleftrightarrow> x = x'"
  by transfer (force simp add: Cons_replicate_eq)

lemma nxt_many_calls[simp]: "nxt (many_calls x) x' = (if x' =  x then many_calls x else empty)"
  by transfer (force simp add: Cons_replicate_eq)

lemma repeatable_many_calls: "repeatable (many_calls x)"
  unfolding repeatable_def by auto

lift_definition anything :: "'a ftree" is "UNIV"
  by auto

lemma possible_anything[simp]: "possible anything x' \<longleftrightarrow> True"
  by transfer auto

lemma nxt_anything[simp]: "nxt anything x = anything"
  by  transfer auto

subsection {* Disjoint union of trees *}

lift_definition either :: "'a ftree \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree"  is "op \<union>"
  by (auto simp add: downset_def)
  
lemma either_empty1[simp]: "either empty t = t"
  by transfer auto
lemma either_empty2[simp]: "either t empty = t"
  by transfer auto
lemma either_sym[simp]: "either t t2 = either t2 t"
  by transfer auto
lemma either_idem[simp]: "either t t = t"
  by transfer auto

lemma possible_either[simp]: "possible (either t t') x \<longleftrightarrow> possible t x \<or> possible t' x"
  by transfer auto

lemma nxt_either[simp]: "nxt (either t t') x = either (nxt t x) (nxt t' x)"
  by transfer auto

lemma paths_either[simp]: "paths (either t t') = paths t \<union> paths t'"
  by transfer simp


lift_definition Either :: "'a ftree set \<Rightarrow> 'a ftree"  is "\<lambda> S. insert [] (\<Union>S)"
  by (auto simp add: downset_def)

subsection {* Merging of trees *}

lift_definition both :: "'a ftree \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" (infixl "\<otimes>\<otimes>" 86)
  is "\<lambda> xss yss . \<Union> {xs \<otimes> ys | xs ys. xs \<in> xss \<and> ys \<in> yss}"
  apply (auto simp add: downset_def)
  apply (metis interleave_intros(1))
  apply (drule_tac n = n in interleave_take)
  apply auto
  apply metis
  done


lemma both_assoc[simp]: "t \<otimes>\<otimes> (t' \<otimes>\<otimes> t'') = (t \<otimes>\<otimes> t') \<otimes>\<otimes> t''"
  apply transfer
  apply auto
  apply (metis interleave_assoc2)
  apply (metis interleave_assoc1)
  done

lemma both_comm: "t \<otimes>\<otimes> t' = t' \<otimes>\<otimes> t"
  by transfer (auto, (metis interleave_comm)+)

lemma both_empty1[simp]: "empty \<otimes>\<otimes> t = t"
  by transfer auto

lemma both_empty2[simp]: "t \<otimes>\<otimes> empty = t"
  by transfer auto

lemma paths_both: "xs \<in> paths (t \<otimes>\<otimes> t') \<longleftrightarrow> (\<exists> ys \<in> paths t. \<exists> zs \<in> paths t'. xs \<in> ys \<otimes> zs)"
  by transfer fastforce

lemma both_contains_arg1: "paths t \<subseteq> paths (t \<otimes>\<otimes> t')"
  by transfer fastforce

lemma both_contains_arg2: "paths t' \<subseteq> paths (t \<otimes>\<otimes> t')"
  by transfer fastforce

lemma both_mono1:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (t \<otimes>\<otimes> t'') \<subseteq> paths (t' \<otimes>\<otimes> t'')"
  by transfer auto

lemma both_mono2:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (t'' \<otimes>\<otimes> t) \<subseteq> paths (t'' \<otimes>\<otimes> t')"
  by transfer auto

lemma possible_both[simp]: "possible (t \<otimes>\<otimes> t') x \<longleftrightarrow> possible t x \<or> possible t' x"
proof
  assume "possible (t \<otimes>\<otimes> t') x"
  then obtain xs where "x#xs \<in> paths (t \<otimes>\<otimes> t')"
    by transfer auto
  
  from `x#xs \<in> paths (t \<otimes>\<otimes> t')`
  obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "x#xs \<in> ys \<otimes> zs"
    by transfer auto

  from `x#xs \<in> ys \<otimes> zs`
  have "ys \<noteq> [] \<and> hd ys = x  \<or> zs \<noteq> [] \<and> hd zs = x"
    by (auto elim: interleave_cases)
  thus "possible t x \<or> possible t' x"
    using  `ys \<in> paths t`   `zs \<in> paths t'`
    by transfer auto
next
  assume "possible t x \<or> possible t' x"
  then obtain xs where "x#xs\<in> paths t \<or> x#xs\<in> paths t'"
    by transfer auto
  from this have "x#xs \<in> paths (t \<otimes>\<otimes> t')" by (auto dest: set_mp[OF both_contains_arg1]  set_mp[OF both_contains_arg2])
  thus "possible (t \<otimes>\<otimes> t') x" by transfer auto
qed

lemma nxt_both:
    "nxt (t' \<otimes>\<otimes> t) x = (if possible t' x \<and> possible t x then either (nxt t' x \<otimes>\<otimes> t) (t' \<otimes>\<otimes> nxt t x) else
                           if possible t' x then nxt t' x \<otimes>\<otimes> t else
                           if possible t x then t' \<otimes>\<otimes> nxt t x else
                           empty)"
  by (transfer, auto 4 4 intro: interleave_intros)

lemma Cons_both:
    "x # xs \<in> paths (t' \<otimes>\<otimes> t) \<longleftrightarrow> (if possible t' x \<and> possible t x then xs \<in> paths (nxt t' x \<otimes>\<otimes> t) \<or> xs \<in> paths (t' \<otimes>\<otimes> nxt t x) else
                           if possible t' x then xs \<in> paths (nxt t' x \<otimes>\<otimes> t) else
                           if possible t x then xs \<in> paths (t' \<otimes>\<otimes> nxt t x) else
                           False)"
  apply (auto simp add: paths_Cons_nxt_iff[symmetric] nxt_both)
  by (metis paths.rep_eq possible.rep_eq possible_both)

lemma Cons_both_possible_leftE: "possible t x \<Longrightarrow> xs \<in> paths (nxt t x \<otimes>\<otimes> t') \<Longrightarrow> x#xs \<in> paths (t \<otimes>\<otimes> t')"
  by (auto simp add: Cons_both)
lemma Cons_both_possible_rightE: "possible t' x \<Longrightarrow> xs \<in> paths (t \<otimes>\<otimes> nxt t' x) \<Longrightarrow> x#xs \<in> paths (t \<otimes>\<otimes> t')"
  by (auto simp add: Cons_both)

lemma either_both_distr[simp]:
  "either (t' \<otimes>\<otimes> t) (t' \<otimes>\<otimes> t'') = t' \<otimes>\<otimes> (either t t'')"
  by transfer auto

lemma either_both_distr2[simp]:
  "either (t' \<otimes>\<otimes> t) (t'' \<otimes>\<otimes> t) = either t' t'' \<otimes>\<otimes> t"
  by transfer auto

lemma nxt_both_repeatable[simp]:
  assumes [simp]: "repeatable t'"
  assumes [simp]: "possible t' x"
  shows "nxt (t' \<otimes>\<otimes> t) x = t' \<otimes>\<otimes> (either t (nxt t x))"
  by (auto simp add: nxt_both)

lemma nxt_both_many_calls[simp]: "nxt (many_calls x \<otimes>\<otimes> t) x = many_calls x \<otimes>\<otimes> either t (nxt t x)"
  by (simp add: repeatable_many_calls)

lemma and_then_both_single:
  "paths (and_then x t) \<subseteq> paths (single x \<otimes>\<otimes> t)"
proof
  fix xs
  assume "xs \<in> paths (and_then x t)"
  show "xs \<in> paths (single x \<otimes>\<otimes> t)"
  proof(cases "xs = []")
    case True thus ?thesis by simp
  next
    have "[x] \<in> paths (single x)" by transfer auto
    moreover
    case False
    with `xs \<in> paths (and_then x t)`
    obtain xs' where "xs = x # xs'" and "xs' \<in> paths t" by transfer auto
    moreover
    have "x # xs' \<in> interleave [x] xs'" by (auto intro: interleave_intros)
    ultimately
    show ?thesis by (auto simp add: paths_both)
  qed
qed

lemma repeatable_both_self[simp]:
  assumes [simp]: "repeatable t"
  shows "t \<otimes>\<otimes> t = t"
  apply (intro paths_inj set_eqI)
  apply (induct_tac x)
  apply (auto simp add: Cons_both paths_Cons_nxt_iff[symmetric])
  apply (metis Cons_both both_empty1 possible_empty)+
  done

lemma repeatable_both_both[simp]:
  assumes "repeatable t"
  shows "t \<otimes>\<otimes> t' \<otimes>\<otimes> t = t \<otimes>\<otimes> t'"
  by (metis repeatable_both_self[OF assms]  both_assoc both_comm)

lemma repeatable_both_both2[simp]:
  assumes "repeatable t"
  shows "t' \<otimes>\<otimes> t \<otimes>\<otimes> t = t' \<otimes>\<otimes> t"
  by (metis repeatable_both_self[OF assms]  both_assoc both_comm)


lemma repeatable_both_nxt:
  assumes "repeatable t"
  assumes "possible t' x"
  assumes "t' \<otimes>\<otimes> t = t'"
  shows "nxt t' x \<otimes>\<otimes> t = nxt t' x"
proof(rule classical)
  assume "nxt t' x \<otimes>\<otimes> t \<noteq> nxt t' x"
  hence "either (nxt t' x) t' \<otimes>\<otimes> t \<noteq> nxt t' x" by (metis (no_types) assms(1) both_assoc repeatable_both_self)
  thus "nxt t' x \<otimes>\<otimes> t = nxt t' x"  by (metis (no_types) assms either_both_distr2 nxt_both nxt_repeatable)
qed

lemma repeatable_both_both_nxt:
  assumes "t' \<otimes>\<otimes> t = t'"
  shows "t' \<otimes>\<otimes> t'' \<otimes>\<otimes> t = t' \<otimes>\<otimes> t''"
  by (metis assms both_assoc both_comm)


subsection {* The carrier of a tree *}

lift_definition carrier :: "'a ftree \<Rightarrow> 'a set" is "\<lambda> xss. \<Union>(set ` xss)".

lemma carrier_mono: "paths t \<subseteq> paths t' \<Longrightarrow> carrier t \<subseteq> carrier t'" by transfer auto

lemma carrier_possible:
  "possible t x \<Longrightarrow> x \<in> carrier t" by transfer force

lemma carrier_possible_subset:
   "carrier t \<subseteq> A \<Longrightarrow> possible t x \<Longrightarrow> x \<in> A" by transfer force

lemma carrier_nxt_subset:
  "carrier (nxt t x) \<subseteq> carrier t"
  by transfer auto

lemma Union_paths_carrier: "(\<Union>x\<in>paths t. set x) = carrier t"
  by transfer auto

lemma carrier_both[simp]:
  "carrier (t \<otimes>\<otimes> t') = carrier t \<union> carrier t'"
proof-
  {
  fix x
  assume "x \<in> carrier (t \<otimes>\<otimes> t')"
  then obtain xs where "xs \<in> paths (t \<otimes>\<otimes> t')" and "x \<in> set xs" by transfer auto
  then obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> interleave ys zs"
    by (auto simp add: paths_both)
  from this(3) have "set xs \<subseteq> set ys \<union> set zs" by (rule interleave_set)
  with `ys \<in> _` `zs \<in> _` `x \<in> set xs`
  have "x \<in> carrier t \<union> carrier t'"  by transfer auto
  }
  moreover
  note set_mp[OF carrier_mono[OF both_contains_arg1[where t=t and t' = t']]]
       set_mp[OF carrier_mono[OF both_contains_arg2[where t=t and t' = t']]]
  ultimately
  show ?thesis by auto
qed

subsection {* Removing elements from a tree *}

lift_definition without :: "'a \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> x xss. filter (\<lambda> x'. x' \<noteq> x) ` xss"
  apply (auto intro: downset_filter)
  apply (metis filter.simps(1) imageI)
  done

lift_definition ftree_restr :: "'a set \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> S xss. filter (\<lambda> x'. x' \<in> S) ` xss"
  apply (auto intro: downset_filter)
  apply (metis filter.simps(1) imageI)
  done

lemma filter_paths_conv_free_restr:
  "filter (\<lambda> x' . x' \<in> S) ` paths t = paths (ftree_restr S t)" by transfer auto

lemma filter_paths_conv_free_restr2:
  "filter (\<lambda> x' . x' \<notin> S) ` paths t = paths (ftree_restr (- S) t)" by transfer auto

lemma ftree_restr_is_empty: "carrier t \<inter> S = {} \<Longrightarrow> ftree_restr S t = empty"
  apply transfer
  apply (auto del: iffI )
  apply (metis SUP_bot_conv(2) SUP_inf inf_commute inter_set_filter set_empty)
  apply force
  done

lemma ftree_restr_noop: "carrier t \<subseteq> S \<Longrightarrow> ftree_restr S t = t"
  apply transfer
  apply (auto simp add: image_iff)
  apply (metis SUP_le_iff contra_subsetD filter_True)
  apply (rule_tac x = x in bexI)
  apply (metis SUP_upper contra_subsetD filter_True)
  apply assumption
  done

lemma ftree_restr_both:
  "ftree_restr S (t \<otimes>\<otimes> t') = ftree_restr S t \<otimes>\<otimes> ftree_restr S t'"
  by (force simp add: paths_both filter_paths_conv_free_restr[symmetric] intro: paths_inj filter_interleave  elim: interleave_filter)

lemma ftree_restr_nxt_subset: "x \<in> S \<Longrightarrow> paths (ftree_restr S (nxt t x)) \<subseteq> paths (nxt (ftree_restr S t) x)"
  by transfer (force simp add: image_iff)


lemma ftree_restr_nxt_subset2: "x \<notin> S \<Longrightarrow> paths (ftree_restr S (nxt t x)) \<subseteq> paths (ftree_restr S t)"
  apply transfer
  apply auto
  apply force
  by (metis filter.simps(2) imageI)

lemma ftree_restr_possible: "x \<in> S \<Longrightarrow> possible t x \<Longrightarrow> possible (ftree_restr S t) x"
  by transfer force

lemma ftree_restr_possible2: "possible (ftree_restr S t') x \<Longrightarrow> x \<in> S" 
  by transfer (auto, metis filter_eq_Cons_iff)


subsection {* Substituting trees for every node *}

context fixes f :: "'a \<Rightarrow> 'a ftree"
begin
fun substitute' :: "'a ftree \<Rightarrow> 'a list \<Rightarrow> bool"
  where substitute'_Nil: "substitute' t [] \<longleftrightarrow> True"
     |  substitute'_Cons: "substitute' t (x#xs) \<longleftrightarrow> possible t x \<and> substitute' (nxt t x \<otimes>\<otimes> f x) xs"
end

lemma downset_substitute: "downset (Collect (substitute' f t))"
apply (rule) unfolding mem_Collect_eq
proof-
  fix x
  assume "substitute' f t x"
  thus "substitute' f t (butlast x)" by(induction t x rule: substitute'.induct) (auto)
qed

lift_definition substitute :: "('a \<Rightarrow> 'a ftree) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> f t. Collect (substitute' f t)"
    by (simp add: downset_substitute)

lemma elim_substitute'[pred_set_conv]: "substitute' f t xs \<longleftrightarrow> xs \<in> paths (substitute f t)" by transfer auto

lemmas substitute_induct[case_names Nil Cons] = substitute'.induct
lemmas substitute_simps[simp] = substitute'.simps[unfolded elim_substitute']

lemma substitute_mono2: 
  assumes "paths t \<subseteq> paths t'"
  shows "paths (substitute f t) \<subseteq> paths (substitute f t')"
proof
  fix xs
  assume "xs \<in> paths (substitute f t)"
  thus "xs \<in> paths (substitute f t')"
  using assms
  proof(induction xs arbitrary:t  t')
  case Nil
    thus ?case by simp
  next
  case (Cons t x xs)
    thus ?case
    by (auto dest: possible_mono, metis both_comm both_mono2 nxt_mono)
  qed
qed

lemma substitute_mono1: 
  assumes "\<And>x. paths (f x) \<subseteq> paths (f' x)"
  shows "paths (substitute f t) \<subseteq> paths (substitute f' t)"
proof
  fix xs
  assume "xs \<in> paths (substitute f t)"
  thus "xs \<in> paths (substitute f' t)"
    by(induction xs arbitrary: t)
     (auto intro:  set_mp[OF substitute_mono2[OF  both_mono2[OF assms]]])
qed

lemma substitute_contains_arg: "paths t \<subseteq> paths (substitute f t)"
proof
  fix xs
  show "xs \<in> paths t \<Longrightarrow> xs \<in> paths (substitute f t)"
  proof (induction xs arbitrary: t)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    from `x # xs \<in> paths t` 
    have "possible t x" by transfer auto
    moreover
    from `x # xs \<in> paths t` have "xs \<in> paths (nxt t x)"
      by (auto simp add: paths_nxt_eq)
    hence "xs \<in> paths (nxt t x \<otimes>\<otimes> f x)" by (rule set_mp[OF both_contains_arg1])
    hence "xs \<in> paths (substitute f (nxt t x \<otimes>\<otimes> f x))" by (rule Cons.IH)
    ultimately
    show ?case by simp
  qed
qed

lemma possible_substitute[simp]: "possible (substitute f t) x \<longleftrightarrow> possible t x"
  by (metis Cons_both both_empty2 paths_Nil substitute_simps(2))

lemma nxt_substitute[simp]: "possible t x \<Longrightarrow> nxt (substitute f t) x = substitute f (nxt t x \<otimes>\<otimes> f x)"
  by (rule ftree_eqI) (simp add: paths_nxt_eq )

lemma substitute_either: "substitute f (either t t') = either (substitute f t) (substitute f t')"
proof-
  have [simp]: "\<And> t t' x . either (nxt t x) (nxt t' x) \<otimes>\<otimes> f x = either (nxt t x \<otimes>\<otimes> f x) (nxt t' x \<otimes>\<otimes> f x)" by (metis both_comm either_both_distr)
  {
  fix xs
  have "xs \<in> paths (substitute f (either t t'))  \<longleftrightarrow> xs \<in> paths (substitute f t)  \<or> xs \<in> paths (substitute f t')"
  proof (induction xs arbitrary: t t')
    case Nil thus ?case by simp
  next
    case (Cons x xs)
    note IH = Cons.IH[where t = "nxt t' x \<otimes>\<otimes> f x" and t' = "nxt t x \<otimes>\<otimes> f x", simp]
    show ?case
    apply (auto simp del: either_both_distr2)
        apply (metis IH both_comm either_both_distr either_empty2 nxt_not_possible)
    by (metis  IH both_comm both_empty1 either_both_distr either_empty1 nxt_not_possible)
  qed
  }
  thus ?thesis by (auto intro: paths_inj)
qed

lemma substitute_both: "substitute f (t \<otimes>\<otimes> t') = substitute f t \<otimes>\<otimes> substitute f t'"
proof (intro paths_inj set_eqI)
  fix xs
  show "(xs \<in> paths (substitute f (t \<otimes>\<otimes> t'))) = (xs \<in> paths (substitute f t \<otimes>\<otimes> substitute f t'))"
  proof (induction xs arbitrary: t t')
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    have [simp]: "nxt t x \<otimes>\<otimes> t' \<otimes>\<otimes> f x = nxt t x \<otimes>\<otimes> f x \<otimes>\<otimes> t'"
      by (metis both_assoc both_comm)
    have [simp]: "t \<otimes>\<otimes> nxt t' x \<otimes>\<otimes> f x = t \<otimes>\<otimes> (nxt t' x \<otimes>\<otimes> f x)"
      by (metis both_assoc both_comm)
    note Cons[where t = "nxt t x \<otimes>\<otimes> f x" and t' = t', simp]
    note Cons[where t = t and t' = "nxt t' x \<otimes>\<otimes> f x", simp]
    show ?case
      by (auto simp add: Cons_both nxt_both either_both_distr2[symmetric] substitute_either
                  simp del: both_assoc )
  qed
qed

lemma substitute_only_empty:
  assumes "const_on f (carrier t) empty"
  shows "substitute f t = t"
proof (intro paths_inj  set_eqI)
  fix xs
  from assms
  show "xs \<in> paths (substitute f t) \<longleftrightarrow> xs \<in> paths t"
  proof (induction xs arbitrary: t)
  case Nil thus ?case by simp
  case (Cons x xs t)
    from Cons.prems carrier_nxt_subset
    have "const_on f (carrier (nxt t x)) empty"
      by (rule const_on_subset)
    note Cons.IH[OF this, simp]

    note const_onD[OF Cons.prems carrier_possible, where y = x, simp]

    show ?case by (auto simp add: Cons_path)
  qed
qed

lemma substitute_and_then:
  "substitute f (and_then x t) = and_then x (substitute f (t \<otimes>\<otimes> f x))"
  by (rule ftree_eqI) auto

lemma substitute_remove_anyways_aux:
  assumes [simp]: "repeatable (f x)"
  assumes "xs \<in> paths (substitute f t)"
  assumes "t \<otimes>\<otimes> f x = t"
  shows "xs \<in> paths (substitute (f(x := empty)) t)"
  using assms(2,3)
  by (induction xs arbitrary: t)(auto  simp add: repeatable_both_nxt repeatable_both_both_nxt )

lemma substitute_remove_anyways:
  assumes "repeatable t"
  assumes "f x = t"
  shows "substitute f (t \<otimes>\<otimes> t') = substitute (f(x := empty)) (t \<otimes>\<otimes> t')"
proof (rule paths_inj, rule, rule subsetI)
  fix xs
  have "repeatable (f x)" using assms by simp
  moreover
  assume "xs \<in> paths (substitute f (t \<otimes>\<otimes> t'))"
  moreover
  have "t \<otimes>\<otimes> t' \<otimes>\<otimes> f x = t \<otimes>\<otimes> t'"
    by (metis assms both_assoc both_comm repeatable_both_self)
  ultimately
  show "xs \<in> paths (substitute (f(x := FTree.empty)) (t \<otimes>\<otimes> t'))"
      by (rule substitute_remove_anyways_aux)
next
  show "paths (substitute (f(x := FTree.empty)) (t \<otimes>\<otimes> t')) \<subseteq> paths (substitute f (t \<otimes>\<otimes> t'))"
    by (rule substitute_mono1) auto
qed 

lemma substitute_cong':
  assumes "xs \<in> paths (substitute f t)"
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> f x = f' x"
  shows "xs \<in> paths (substitute f' t)"
  using assms
  apply (induction xs arbitrary: t)
  apply auto
  by (metis (poly_guards_query) Un_subset_iff carrier_both carrier_nxt_subset carrier_possible_subset order.trans)

lemma substitute_cong_induct:
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> f x = f' x"
  shows "substitute f t = substitute f' t"
  apply (rule paths_inj)
  apply (rule set_eqI)
  using substitute_cong'[OF _ _ assms(2)] assms(1,3)
  by (metis (poly_guards_query))

lemma carrier_substitute1: "carrier t \<subseteq> carrier (substitute f t)"
    by (rule carrier_mono) (rule substitute_contains_arg)

lemma substitute_cong:
  assumes "\<And> x. x \<in> carrier (substitute f t) \<Longrightarrow> f x = f' x"
  shows "substitute f t = substitute f' t"
proof(rule substitute_cong_induct[OF _ _ assms])
  show "carrier t \<subseteq> carrier (substitute f t)"
    by (rule carrier_substitute1)
next
  fix x
  assume "x \<in> carrier (substitute f t)"
  then obtain xs where "xs \<in> paths (substitute f t)"  and "x \<in> set xs"  by transfer auto
  thus "carrier (f x) \<subseteq> carrier (substitute f t)"
  proof (induction xs arbitrary: t)
  case Nil thus ?case by simp
  next
  case (Cons x' xs t)
    from `x' # xs \<in> paths (substitute f t)`
    have "possible t x'" and "xs \<in> paths (substitute f (nxt t x' \<otimes>\<otimes> f x')) " by auto

    from `x \<in> set (x' # xs)`
    have "x = x' \<or> x \<in> set xs" by auto
    hence "carrier (f x) \<subseteq> carrier (substitute f (nxt t x' \<otimes>\<otimes> f x'))"
    proof
      assume "x = x'"
      have "carrier (f x) \<subseteq> carrier (nxt t x \<otimes>\<otimes> f x)" by simp
      also have "\<dots> \<subseteq> carrier (substitute f (nxt t x \<otimes>\<otimes> f x))" by (rule carrier_substitute1)
      finally show ?thesis unfolding `x = x'`.
    next
      assume "x \<in> set xs"
      from Cons.IH[OF `xs \<in> _ ` this]
      show "carrier (f x) \<subseteq> carrier (substitute f (nxt t x' \<otimes>\<otimes> f x'))".
    qed
    also
    from `possible t x'`
    have "carrier (substitute f (nxt t x' \<otimes>\<otimes> f x')) \<subseteq>  carrier (substitute f t)"
      apply transfer
      apply auto
      apply (rule_tac x = "x'#xa" in exI)
      apply auto
      done
    finally show ?case.
  qed
qed

lemma substitute_substitute:
  assumes "\<And> x. const_on f' (carrier (f x)) empty"
  shows "substitute f (substitute f' t) = substitute (\<lambda> x. f x \<otimes>\<otimes> f' x) t"
  apply(rule ftree_coinduct[where P = "\<lambda> t t'. \<exists> t''. t = substitute f (substitute f' t'') \<and> t' =  (substitute (\<lambda>x. f x \<otimes>\<otimes> f' x) t'')"])
  apply blast
  apply auto
  apply (rule_tac x = "nxt t'' x \<otimes>\<otimes> f x \<otimes>\<otimes> f' x" in exI)
  apply (auto simp add: substitute_both  substitute_only_empty[OF assms])
  by (metis both_comm both_assoc)

lemma ftree_rest_substitute:
  assumes "\<And> x. carrier (f x) \<inter> S = {}"
  shows "ftree_restr S (substitute f t) = ftree_restr S t"
proof(rule paths_inj, rule set_eqI, rule iffI)
  fix xs
  assume "xs \<in> paths (ftree_restr S (substitute f t))"
  then
  obtain xs' where [simp]: "xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths (substitute f t)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2)
  have "filter (\<lambda> x'. x' \<in> S) xs' \<in>  paths (ftree_restr S t)"
  proof (induction xs' arbitrary: t)
  case Nil thus ?case by simp
  next
  case (Cons x xs t)
    from Cons.prems
    have "possible t x" and "xs \<in> paths (substitute f (nxt t x \<otimes>\<otimes> f x))" by auto
    from  Cons.IH[OF this(2)]
    have "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (ftree_restr S (nxt t x) \<otimes>\<otimes> ftree_restr S (f x))" by (simp add: ftree_restr_both)
    hence "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (ftree_restr S (nxt t x))" by (simp add: ftree_restr_is_empty[OF assms])
    with `possible t x`
    show "[x'\<leftarrow>x#xs . x' \<in> S] \<in> paths (ftree_restr S t)"
      by (cases "x \<in> S") (auto simp add: Cons_path ftree_restr_possible  dest: set_mp[OF ftree_restr_nxt_subset2]  set_mp[OF ftree_restr_nxt_subset])
  qed
  thus "xs \<in> paths (ftree_restr S t)" by simp
next
  fix xs
  assume "xs \<in> paths (ftree_restr S t)"
  then obtain xs' where [simp]:"xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths t" 
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2)
  have "xs' \<in> paths (substitute f t)" by (rule set_mp[OF substitute_contains_arg])
  thus "xs \<in> paths (ftree_restr S (substitute f t))"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
qed

text {* An alternative characterization of substitution *}

inductive substitute'' :: "('a \<Rightarrow> 'a ftree) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f :: "'a \<Rightarrow> 'a ftree"
  where substitute''_Nil: "substitute'' f [] []"
     |  substitute''_Cons: "zs \<in> paths (f x) \<Longrightarrow> xs' \<in> interleave xs zs \<Longrightarrow> substitute'' f xs' ys \<Longrightarrow> substitute'' f (x#xs) (x#ys)"
inductive_cases substitute''_NilE[elim]: "substitute'' f xs []"  "substitute'' f [] xs"
inductive_cases substitute''_ConsE[elim]: "substitute'' f (x#xs) ys"

lemma substitute_substitute'':
  "xs \<in> paths (substitute f t) \<longleftrightarrow> (\<exists> xs' \<in> paths t. substitute'' f xs' xs)"
proof
  assume "xs \<in> paths (substitute f t)"
  thus "\<exists> xs' \<in> paths t. substitute'' f xs' xs"
  proof(induction xs arbitrary: t)
    case Nil
    have "substitute'' f [] []"..
    thus ?case by auto
  next
    case (Cons x xs t)
    from `x # xs \<in> paths (substitute f t)`
    have "possible t x" and "xs \<in> paths (substitute f (nxt t x \<otimes>\<otimes> f x))" by (auto simp add: Cons_path)
    from Cons.IH[OF this(2)]
    obtain xs' where "xs' \<in> paths (nxt t x \<otimes>\<otimes> f x)" and "substitute'' f xs' xs" by auto
    from this(1)
    obtain ys' zs' where "ys' \<in> paths (nxt t x)" and "zs' \<in> paths (f x)" and "xs' \<in> interleave ys' zs'" 
      by (auto simp add: paths_both)
  
    from this(2,3) `substitute'' f xs' xs`
    have "substitute'' f (x # ys') (x # xs)"..
    moreover
    from `ys' \<in> paths (nxt t x)` `possible t x`
    have "x # ys' \<in> paths t"  by (simp add: Cons_path)
    ultimately
    show ?case by auto
  qed
next
  assume "\<exists> xs' \<in> paths t. substitute'' f xs' xs"
  then obtain xs' where  "substitute'' f xs' xs" and "xs' \<in> paths t"  by auto
  thus "xs \<in> paths (substitute f t)"
  proof(induction arbitrary: t rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs x xs' xs ys t)
    from Cons.prems Cons.hyps
    show ?case by (force simp add: Cons_path paths_both intro!: Cons.IH)
  qed
qed

lemma ftree_rest_substitute2:
  assumes "\<And> x. carrier (f x) \<subseteq> S"
  assumes "\<And> x. const_on f (-S) empty"
  shows "ftree_restr S (substitute f t) = substitute f (ftree_restr S t)"
proof(rule paths_inj, rule set_eqI, rule iffI)
  fix xs
  assume "xs \<in> paths (ftree_restr S (substitute f t))"
  then
  obtain xs' where [simp]: "xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths (substitute f t)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2)
  have "filter (\<lambda> x'. x' \<in> S) xs' \<in> paths (substitute f (ftree_restr S t))"
  proof (induction xs' arbitrary: t)
  case Nil thus ?case by simp
  next
  case (Cons x xs t)
    from Cons.prems
    have "possible t x" and "xs \<in> paths (substitute f (nxt t x \<otimes>\<otimes> f x))" by auto
    from  Cons.IH[OF this(2)]
    have *: "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (substitute f (ftree_restr S (nxt t x \<otimes>\<otimes> f x)))" by (simp add: ftree_restr_both)
    thus ?case
      using `possible t x` assms(2)
      by (cases "x \<in> S")
         (force simp add: ftree_restr_both ftree_restr_noop[OF assms(1)] intro: ftree_restr_possible
                  dest: set_mp[OF substitute_mono2[OF both_mono1[OF ftree_restr_nxt_subset]]]  set_mp[OF substitute_mono2[OF ftree_restr_nxt_subset2]])+
  qed
  thus "xs \<in> paths (substitute f (ftree_restr S t))" by simp
next
  fix xs
  assume "xs \<in> paths (substitute f (ftree_restr S t))"
  then obtain xs' where "xs' \<in> paths t" and "substitute'' f (filter (\<lambda> x'. x'\<in>S) xs') xs "
    unfolding substitute_substitute''
    by (auto simp add: filter_paths_conv_free_restr[symmetric])

  from this(2)
  have "\<exists> xs''. xs = filter (\<lambda> x'. x'\<in>S) xs'' \<and> substitute'' f xs' xs''"
  proof(induction "(xs',xs)" arbitrary: xs' xs rule: measure_induct_rule[where f = "\<lambda> (xs,ys). length (filter (\<lambda> x'. x' \<notin> S) xs) + length ys"])
  case (less xs ys)
    note `substitute'' f [x'\<leftarrow>xs . x' \<in> S] ys`

    show ?case
    proof(cases xs)
    case Nil with less.prems have "ys = []" by auto
      thus ?thesis using Nil by (auto,  metis filter.simps(1) substitute''_Nil)
    next
    case (Cons x xs')
      show ?thesis
      proof (cases "x \<in> S")
      case True with Cons less.prems
        have "substitute'' f (x# [x'\<leftarrow>xs' . x' \<in> S]) ys" by simp
        from substitute''_ConsE[OF this]
        obtain zs xs'' ys' where "ys = x # ys'" and "zs \<in> paths (f x)" and "xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] zs" and "substitute'' f xs'' ys'".
        from `zs \<in> paths (f x)`  assms(1)
        have "set zs \<subseteq> S" by (auto simp add: Union_paths_carrier[symmetric])
        hence [simp]: "[x'\<leftarrow>zs . x' \<in> S] = zs" "[x'\<leftarrow>zs . x' \<notin> S] = []" 
            by (metis UnCI Un_subset_iff eq_iff filter_True,
               metis `set zs \<subseteq> S` filter_False insert_absorb insert_subset)
        
        from `xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] zs`
        have "xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] [x'\<leftarrow>zs . x' \<in> S]" by simp
        then obtain xs''' where "xs'' = [x'\<leftarrow>xs''' . x' \<in> S]" and "xs''' \<in> interleave xs' zs" by (rule interleave_filter)

        from `xs''' \<in> interleave xs' zs`
        have l: "\<And> P. length (filter P xs''') = length (filter P xs') + length (filter P zs)"
          by (induction) auto
        
        from `substitute'' f xs'' ys'` `xs'' = _`
        have "substitute'' f [x'\<leftarrow>xs''' . x' \<in> S] ys'" by simp
        hence "\<exists>ys''. ys' = [x'\<leftarrow>ys'' . x' \<in> S] \<and> substitute'' f xs''' ys''"
            by (rule less.hyps[rotated])
               (auto simp add: `ys = _ ` `xs =_` `x \<in> S` `xs'' = _`[symmetric] l)
        then obtain ys'' where "ys' = [x'\<leftarrow>ys'' . x' \<in> S]" and "substitute'' f xs''' ys''" by blast
        hence "ys = [x'\<leftarrow>x#ys'' . x' \<in> S]" using `x \<in> S` `ys = _` by simp
        moreover
        from `zs \<in> paths (f x)` `xs''' \<in> interleave xs' zs` `substitute'' f xs''' ys''`
        have "substitute'' f (x#xs') (x#ys'')"
          by rule
        ultimately
        show ?thesis unfolding Cons by blast
      next
      case False with Cons less.prems
        have "substitute'' f ([x'\<leftarrow>xs' . x' \<in> S]) ys" by simp
        hence "\<exists>ys'. ys = [x'\<leftarrow>ys' . x' \<in> S] \<and> substitute'' f xs' ys'"
            by (rule less.hyps[rotated]) (auto simp add:  `xs =_` `x \<notin>  S`)
        then obtain ys' where "ys = [x'\<leftarrow>ys' . x' \<in> S]" and "substitute'' f xs' ys'" by auto
        
        from this(1)
        have "ys = [x'\<leftarrow>x#ys' . x' \<in> S]" using `x \<notin> S` `ys = _` by simp
        moreover
        have [simp]: "f x = empty" using `x \<notin> S` assms(2) by force
        from `substitute'' f xs' ys'`
        have "substitute'' f (x#xs') (x#ys')"
          by (auto intro: substitute''.intros)
        ultimately
        show ?thesis unfolding Cons by blast
      qed
    qed
  qed
  then obtain xs'' where "xs = filter (\<lambda> x'. x'\<in>S) xs''" and "substitute'' f xs' xs''" by auto
  from this(2) `xs' \<in> paths t`
  have "xs'' \<in> paths (substitute f t)" by (auto simp add: substitute_substitute'')
  with `xs = _`
  show "xs \<in> paths (ftree_restr S (substitute f t))"
    by (auto simp add:  filter_paths_conv_free_restr[symmetric])
qed

end
