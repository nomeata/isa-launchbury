theory FTree
imports Main
begin

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

typedef 'a ftree = "{xss :: 'a list set . [] \<in> xss \<and> downset xss}" by auto

setup_lifting type_definition_ftree

lift_definition possible ::"'a ftree \<Rightarrow> 'a \<Rightarrow> bool"
  is "\<lambda> xss x. \<exists> xs \<in> xss. xs \<noteq> [] \<and> hd xs = x".

lift_definition nxt ::"'a ftree \<Rightarrow> 'a \<Rightarrow> 'a ftree"
  is "\<lambda> xss x. insert [] {xs | x' xs . x'#xs \<in> xss \<and> x' = x}"
  apply (auto simp add: downset_def)
  by (metis take_Suc_Cons)

lift_definition empty :: "'a ftree" is "{[]}" by auto

lemma possible_empty[simp]: "possible empty x' \<longleftrightarrow> False"
  by transfer auto

lemma nxt_empty[simp]: "nxt empty x' =  empty"
  by transfer auto
 
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


lift_definition many_calls :: "'a \<Rightarrow> 'a ftree" is "\<lambda> x. range (\<lambda> n. replicate n x)"
  by (auto simp add: downset_def)

lemma possible_many_calls[simp]: "possible (many_calls x) x' \<longleftrightarrow> x = x'"
  by transfer auto

lemma nxt_many_calls[simp]: "nxt (many_calls x) x' = (if x' =  x then many_calls x else empty)"
  by transfer (force simp add: Cons_replicate_eq)

lift_definition anything :: "'a ftree" is "UNIV"
  by auto

lemma possible_anything[simp]: "possible anything x' \<longleftrightarrow> True"
  by transfer auto

lemma nxt_anything[simp]: "nxt anything x = anything"
  by  transfer auto

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

lift_definition Either :: "'a ftree set \<Rightarrow> 'a ftree"  is "\<lambda> S. insert [] (\<Union>S)"
  by (auto simp add: downset_def)

inductive interleave' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where [simp]: "interleave' [] [] []"
  | "interleave' xs ys zs \<Longrightarrow>interleave' (x#xs) ys (x#zs)"
  | "interleave' xs ys zs \<Longrightarrow>interleave' xs (x#ys) (x#zs)"

definition interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" 
  where "interleave xs ys = Collect (interleave' xs ys)"
lemma elim_interleave'[pred_set_conv]: "interleave' xs ys zs \<longleftrightarrow> zs \<in> interleave xs ys" unfolding interleave_def by simp

lemmas interleave_intros[intro?] = interleave'.intros[to_set]
lemmas interleave_intros(1)[simp]
lemmas interleave_induct[consumes 1, induct set: interleave, case_names Nil left right] = interleave'.induct[to_set]
lemmas interleave_cases[consumes 1, cases set: interleave] = interleave'.cases[to_set]
lemmas interleave_simps = interleave'.simps[to_set]

inductive_cases interleave_nilE[elim!]: "[] \<in> interleave xs ys"

inductive_cases interleave_ConsE[elim]: "(x#xs) \<in> interleave ys zs"
inductive_cases interleave_ConsE2[elim]: "xs \<in> interleave (x#ys) zs"
inductive_cases interleave_ConsE3[elim]: "xs \<in> interleave ys (x#zs)"


lemma interleave_comm: "xs \<in> interleave ys zs \<Longrightarrow> xs \<in> interleave zs ys"
  by (induction rule: interleave_induct) (auto intro: interleave_intros)

lemma interleave_Nil1[simp]: "interleave [] xs = {xs}"
proof-
  have interleave_only_left: "xs \<in> interleave [] xs"
  by (induction xs) (auto intro: interleave_intros)
  moreover
  {fix x ys
  have "x \<in> interleave ys xs \<Longrightarrow> ys = []\<Longrightarrow> x = xs"
  by (induction rule: interleave_induct) auto
  }
  ultimately
  show ?thesis by blast
qed

lemma interleave_Nil2[simp]: "interleave xs [] = {xs}"
proof-
  have interleave_only_left: "xs \<in> interleave xs []"
  by (induction xs) (auto intro: interleave_intros)
  moreover
  {fix x ys
  have "x \<in> interleave xs ys \<Longrightarrow> ys = []\<Longrightarrow> x = xs"
  by (induction rule: interleave_induct) auto
  }
  ultimately
  show ?thesis by blast
qed  

lemma interleave_nil_simp[simp]: "[] \<in> interleave xs ys \<longleftrightarrow> xs = [] \<and> ys = []"
  by auto


lemma interleave_assoc1: "a \<in> interleave xs ys \<Longrightarrow> b \<in> interleave a zs \<Longrightarrow> \<exists> c. c \<in> interleave ys zs \<and>  b \<in> interleave xs c"
  by (induction b arbitrary: a  xs ys zs )
     (simp, fastforce del: interleave_ConsE elim!: interleave_ConsE  intro: interleave_intros)

lemma interleave_assoc2: "a \<in> interleave ys zs \<Longrightarrow> b \<in> interleave xs a \<Longrightarrow> \<exists> c. c \<in> interleave xs ys \<and>  b \<in> interleave c zs"
  by (induction b arbitrary: a  xs ys zs )
     (simp, fastforce del: interleave_ConsE elim!: interleave_ConsE  intro: interleave_intros)


lemma interleave_take: "zs \<in> interleave xs ys \<Longrightarrow> \<exists> n\<^sub>1 n\<^sub>2. n = n\<^sub>1 + n\<^sub>2 \<and>  take n zs \<in> interleave (take n\<^sub>1 xs) (take n\<^sub>2 ys)"
  apply(induction arbitrary: n rule:interleave_induct)
  apply auto
  apply arith
  apply (case_tac n, simp)
  apply (drule_tac x = nat in meta_spec)
  apply auto
  apply (rule_tac x = "Suc n\<^sub>1" in exI)
  apply (rule_tac x = "n\<^sub>2" in exI)
  apply (auto intro: interleave_intros)[1]

  apply (case_tac n, simp)
  apply (drule_tac x = nat in meta_spec)
  apply auto
  apply (rule_tac x = "n\<^sub>1" in exI)
  apply (rule_tac x = "Suc n\<^sub>2" in exI)
  apply (auto intro: interleave_intros)[1]
  done


lift_definition both :: "'a ftree \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree"
  is "\<lambda> xss yss . \<Union> {interleave xs ys | xs ys. xs \<in> xss \<and> ys \<in> yss}"
  apply (auto simp add: downset_def)
  apply (metis interleave_intros(1))
  apply (drule_tac n = n in interleave_take)
  apply auto
  apply metis
  done

lemma both_assoc[simp]: "both t (both t' t'') = both (both t t') t''"
  apply transfer
  apply auto
  apply (metis interleave_assoc2)
  apply (metis interleave_assoc1)
  done

lemma both_comm: "both t t' = both t' t"
  by transfer (auto, (metis interleave_comm)+)

lift_definition paths :: "'a ftree \<Rightarrow> 'a list set" is "(\<lambda> x. x)".

lemma paths_inj: "paths t = paths t' \<Longrightarrow> t = t'" by transfer auto

lemma paths_injs_simps[simp]: "paths t = paths t' \<longleftrightarrow> t = t'" by transfer auto

lemma paths_both: "xs \<in> paths (both t t') \<longleftrightarrow> (\<exists> ys \<in> paths t. \<exists> zs \<in> paths t'. xs \<in> interleave ys zs)"
  by transfer fastforce

lemma paths_either[simp]: "paths (either t t') = paths t \<union> paths t'"
  by transfer simp

lemma both_contains_arg1: "paths t \<subseteq> paths (both t t')"
  by transfer fastforce

lemma both_contains_arg2: "paths t' \<subseteq> paths (both t t')"
  by transfer fastforce

lemma paths_Nil[simp]: "[] \<in> paths t" by transfer simp

lemma paths_Cons_nxt:
  "possible t x \<Longrightarrow> xs \<in> paths (nxt t x) \<Longrightarrow> (x#xs) \<in> paths t"
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

lemma paths_nxt_eq: "xs \<in> paths (nxt t x) \<longleftrightarrow> xs = [] \<or> x#xs \<in> paths t"
 by transfer auto

lemma paths_and_then_Cons[simp]: "x'#xs \<in> paths (and_then x t) \<longleftrightarrow> x' = x \<and> xs \<in> paths t"
 by transfer force
 
lemma possible_both[simp]: "possible (both t t') x \<longleftrightarrow> possible t x \<or> possible t' x"
proof
  assume "possible (both t t') x"
  then obtain xs where "xs \<in> paths (both t t')" "xs \<noteq> []" "hd xs = x"
    by transfer auto
  
  from `xs \<in> paths (both t t')`
  obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> interleave ys zs"
    by transfer auto

  from `xs \<noteq> []` `hd xs = x` `xs \<in> interleave ys zs`
  have "ys \<noteq> [] \<and> hd ys = x  \<or> zs \<noteq> [] \<and> hd zs = x"
    by (cases xs)  (auto elim: interleave_cases)
  thus "possible t x \<or> possible t' x"
    using  `ys \<in> paths t`   `zs \<in> paths t'`
    by transfer auto
next
  assume "possible t x \<or> possible t' x"
  then obtain xs where "xs \<noteq> [] \<and> hd xs = x" and "xs \<in> paths t \<or> xs \<in> paths t'"
    by transfer auto
  from this(2) have "xs \<in> paths (both t t')" by (auto dest: set_mp[OF both_contains_arg1]  set_mp[OF both_contains_arg2])
  with `xs \<noteq> [] \<and> hd xs = x`
  show "possible (both t t') x" by transfer auto
qed

lemma nxt_both_many_calls[simp]: "nxt (both (many_calls x) t) x = both (many_calls x) (either t (nxt t x))"
proof (intro paths_inj  set_eqI iffI)
  fix xs
  assume "xs \<in> paths (nxt (both (many_calls x) t) x) "
  thus  "xs \<in> paths (both (many_calls x) (either t (nxt t x)))"
  proof(rule paths_nxt)
    assume "xs = []" thus ?thesis by simp
  next
    assume "x # xs \<in> paths (both (many_calls x) t)"
    then obtain ys zs where "ys \<in> paths (many_calls x)" and "zs \<in> paths t" and "x#xs \<in> interleave ys zs"
      unfolding paths_both by auto
    from `x#xs \<in> interleave ys zs`
    show ?thesis
    proof
      fix ys'
      assume "ys = x # ys'" with `ys \<in> paths (many_calls x)`
      have "ys' \<in> paths (many_calls x)"
        by transfer ( auto, metis (poly_guards_query) list.distinct(2) list.sel(3) not0_implies_Suc range_eqI replicate.simps(1) replicate_Suc)
      moreover
      from `zs \<in> paths t` have "zs \<in> paths (either t (nxt t x))" by simp
      moreover
      assume "xs \<in> interleave ys' zs"
      ultimately
      show "xs \<in> paths (both (many_calls x) (either t (nxt t x)))" unfolding paths_both by auto
    next
      fix zs'
      note `ys \<in> paths (many_calls x)`
      moreover
      assume "zs = x # zs'" with `zs \<in> paths t`
      have "zs' \<in> paths (nxt t x)" by (simp add: paths_nxt_eq)
      moreover
      assume "xs \<in> interleave ys zs'"
      ultimately
      show "xs \<in> paths (both (many_calls x) (either t (nxt t x)))" unfolding paths_both by auto
    qed
  qed
next
  fix xs
  assume "xs \<in> paths (both (many_calls x) (either t (nxt t x)))"
  thus "xs \<in> paths (nxt (both (many_calls x) t) x)"
    by (fastforce simp add: paths_both paths_nxt_eq intro: interleave_intros paths_Cons_nxt)
qed

lemma and_then_both_single:
  "paths (and_then x t) \<subseteq> paths (both (single x) t)"
proof
  fix xs
  assume "xs \<in> paths (and_then x t)"
  show "xs \<in> paths (both (single x) t)"
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

lift_definition without :: "'a \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> x xss. filter (\<lambda> x'. x' \<noteq> x) ` xss"
  apply (auto intro: downset_filter)
  apply (metis filter.simps(1) imageI)
  done


inductive substitute' :: "('a \<Rightarrow> 'a ftree) \<Rightarrow> 'a ftree \<Rightarrow> 'a list \<Rightarrow> bool" for f
  where substitute'_Nil[simp]: "substitute' f t []"
  |  substitute'_Cons: "possible t x \<Longrightarrow> substitute' f (both (nxt t x) (f x)) xs \<Longrightarrow> substitute' f t (x#xs)"

lemma substitute'_contains_arg: "xs \<in> paths t \<Longrightarrow> substitute' f t xs"
proof (induction xs arbitrary: t)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  from `x # xs \<in> paths t` 
  have "possible t x" by transfer auto
  moreover
  from `x # xs \<in> paths t` have "xs \<in> paths (nxt t x)"
    by (auto simp add: paths_nxt_eq)
  hence "xs \<in> paths (both (nxt t x) (f x))" sorry
  hence "substitute' f (both (nxt t x) (f x)) xs" by (rule Cons.IH)
  ultimately
  show ?case..
qed

lemma downset_substitute: "downset (Collect (substitute' f t))"
apply (rule) unfolding mem_Collect_eq
proof-
  fix x
  assume "substitute' f t x"
  thus "substitute' f t (butlast x)"
    by(induction) (auto intro: substitute'.intros)
qed

lemma possible_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> possible t x \<Longrightarrow> possible t' x"
  by transfer auto

lemma nxt_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (nxt t x) \<subseteq> paths (nxt t' x)"
  by transfer auto

lemma both_mono1:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (both t t'') \<subseteq> paths (both t' t'')"
  by transfer auto

lemma both_mono2:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (both t'' t) \<subseteq> paths (both t'' t')"
  by transfer auto


lemma substitute'_mono2: 
  assumes "paths t \<subseteq> paths t'"
  assumes "substitute' f t x"
  shows "substitute' f t' x"
using assms(2,1)
proof(induction arbitrary: t' rule: substitute'.induct)
case substitute'_Nil
  thus ?case by simp
next
case (substitute'_Cons t x xs)
  note `possible t x` with substitute'_Cons.prems
  have "possible t' x" by (rule possible_mono)
  moreover
  from  substitute'_Cons.prems
  have "paths (nxt t x) \<subseteq> paths (nxt t' x)" by (rule nxt_mono)
  hence "paths (both (nxt t x) (f x)) \<subseteq> paths (both (nxt t' x) (f x))" by (rule both_mono1)
  hence "substitute' f (both (nxt t' x) (f x)) xs" by (rule substitute'_Cons.IH)
  ultimately
  show ?case..
qed


lemma substitute'_mono1: 
  assumes "\<And>x. paths (f x) \<subseteq> paths (f' x)"
  shows "substitute' f t x \<Longrightarrow> substitute' f' t x"
proof(induction rule: substitute'.induct)
case substitute'_Nil
  thus ?case by simp
next
case (substitute'_Cons t x xs)
  note `possible t x`
  moreover
  have "paths (both (nxt t x) (f x)) \<subseteq> paths (both (nxt t x) (f' x))" by (rule both_mono2[OF assms])
  with `substitute' f' (both (nxt t x) (f x)) xs `
  have "substitute' f' (both (nxt t x) (f' x)) xs" by (rule substitute'_mono2[rotated])
  ultimately
  show ?case..
qed

lemma substitute'_and_then:
  "substitute' f (and_then x t) (x'#xs) = (x' = x \<and> substitute' f (both t (f x)) xs)"
  by (auto elim: substitute'.cases intro: substitute'.intros)


lift_definition substitute :: "('a \<Rightarrow> 'a ftree) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> f t. Collect (substitute' f t)"
    by (simp add: downset_substitute)

lemma substitute_contains_arg: "paths t \<subseteq> paths (substitute f t)"
  by transfer (auto intro: substitute'_contains_arg)

lemma substitute_mono1: "(\<And> x. paths (f x) \<subseteq> paths (f' x)) \<Longrightarrow> paths (substitute f t) \<subseteq> paths (substitute f' t)"
  by transfer (auto intro: substitute'_mono1)

lemma substitute_mono2: "paths t \<subseteq> paths t' \<Longrightarrow> paths (substitute f t) \<subseteq> paths (substitute f t')"
  by transfer (auto intro: substitute'_mono2)


lemma paths_substitute: "xs \<in> paths (substitute f t) \<longleftrightarrow> substitute' f t xs" by transfer auto

lemma substitute_and_then:
  "substitute f (and_then x t) = and_then x (substitute f (both t (f x)))"
  by (auto intro: ftree_eqI simp add: paths_substitute substitute'_and_then)

  
end
