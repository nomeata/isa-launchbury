theory "List-Interleavings"
imports Main
begin

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
inductive_cases interleave_ConsConsE[elim]: "xs \<in> interleave (y#ys) (z#zs)"
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

lemma interleave_set: "zs \<in> interleave xs ys \<Longrightarrow> set zs \<subseteq> set xs \<union> set ys"
  by(induction rule:interleave_induct) auto


lemma interleave_tl: "xs \<in> interleave ys zs \<Longrightarrow> tl xs \<in> interleave (tl ys) zs \<or> tl xs \<in> interleave ys (tl zs)"
  by(induction rule:interleave_induct) auto

lemma interleave_butlast: "xs \<in> interleave ys zs \<Longrightarrow> butlast xs \<in> interleave (butlast ys) zs \<or> butlast xs \<in> interleave ys (butlast zs)"
  by (induction rule:interleave_induct) (auto intro: interleave_intros)

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

lemma filter_interleave: "xs \<in> interleave ys zs \<Longrightarrow> filter P xs \<in> interleave (filter P ys) (filter P zs)"
  by (induction rule: interleave_induct)  (auto intro: interleave_intros)


function foo where 
  "foo [] [] = undefined"
| "foo xs [] = undefined"
| "foo [] ys = undefined"
| "foo (x#xs) (y#ys) = undefined (foo xs (y#ys)) (foo (x#xs) ys)"
by pat_completeness auto
termination by lexicographic_order
lemmas list_induct2'' = foo.induct[case_names NilNil ConsNil NilCons ConsCons]

lemma interleave_filter:
  assumes "xs \<in> interleave (filter P ys) (filter P zs)"
  obtains xs' where "xs' \<in> interleave ys zs" and "xs = filter P xs'"
using assms
apply atomize_elim
proof(induction ys zs arbitrary: xs rule: list_induct2'')
case NilNil
  thus ?case by simp
next
case (ConsNil ys xs)
  thus ?case by auto
next
case (NilCons zs xs)
  thus ?case by auto
next
case (ConsCons y ys z zs xs)
  show ?case
  proof(cases "P y")
  case False
    with ConsCons.prems(1)
    have "xs \<in> interleave (filter P ys) (filter P (z#zs))" by simp
    from ConsCons.IH(1)[OF this]
    obtain xs' where "xs' \<in> interleave ys (z # zs)" "xs = filter P xs'" by auto
    hence "y#xs' \<in> interleave (y#ys) (z#zs)" and "xs = filter P (y#xs')"
      using False by (auto intro: interleave_intros)
    thus ?thesis by blast
  next
 case True
    show ?thesis
    proof(cases "P z")
    case False
      with ConsCons.prems(1)
      have "xs \<in> interleave (filter P (y#ys)) (filter P zs)" by simp
      from ConsCons.IH(2)[OF this]
      obtain xs' where "xs' \<in> interleave (y#ys) zs" "xs = filter P xs'" by auto
      hence "z#xs' \<in> interleave (y#ys) (z#zs)" and "xs = filter P (z#xs')"
        using False by (auto intro: interleave_intros)
      thus ?thesis by blast
    next
    case True
      from ConsCons.prems(1) `P y` `P z`
      have "xs \<in> interleave (y # filter P ys) (z # filter P zs)"  by simp
      thus ?thesis 
      proof(rule interleave_ConsConsE)
        fix xs'
        assume "xs = y # xs'" and "xs' \<in> interleave (filter P ys) (z # filter P zs)"
        hence "xs' \<in> interleave (filter P ys) (filter P (z#zs))" using `P z` by simp
        from ConsCons.IH(1)[OF this]
        obtain xs'' where "xs'' \<in> interleave ys (z # zs)" and "xs' = filter P xs''" by auto
        hence "y#xs'' \<in> interleave (y#ys) (z#zs)" and "y#xs' = filter P (y#xs'')"
          using `P y` by (auto intro: interleave_intros)
        thus ?thesis using `xs = _` by blast
      next
        fix xs'
        assume "xs = z # xs'" and "xs' \<in> interleave (y # filter P ys) (filter P zs)"
        hence "xs' \<in> interleave (filter P (y#ys)) (filter P zs)" using `P y` by simp
        from ConsCons.IH(2)[OF this]
        obtain xs'' where "xs'' \<in> interleave (y#ys) zs" and "xs' = filter P xs''" by auto
        hence "z#xs'' \<in> interleave (y#ys) (z#zs)" and "z#xs' = filter P (z#xs'')"
          using `P z` by (auto intro: interleave_intros)
        thus ?thesis using `xs = _` by blast
      qed
    qed
  qed
qed


end
