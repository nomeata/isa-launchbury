theory CycleCutOff
imports Main
begin

inductive P :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  for f :: "'a \<rightharpoonup> 'a"
  where PBase: "f x = None \<Longrightarrow> P f x xs"
     |  PStep: "f x = Some y \<Longrightarrow> P f y (x#xs) \<Longrightarrow> y \<notin> set (x#xs) \<Longrightarrow> P f x xs"

inductive P' :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  for f :: "'a \<rightharpoonup> 'a"
  where P'Base: "f x = None \<Longrightarrow> P' f x xs"
     |  P'Step: "f x = Some y \<Longrightarrow> P' f y (x#xs) \<Longrightarrow> P' f x xs"

lemma "P f x xs \<Longrightarrow> P' f x xs"
  by (induction x xs rule: P.induct)
     (elim P'.intros)+

fun valid_stack where
   "valid_stack f y (x#xs) \<longleftrightarrow> f x = Some y \<and> valid_stack f x xs"
 | "valid_stack f x [] \<longleftrightarrow> True"

fun map_pow where 
    "map_pow f 0 x = Some x"
  | "map_pow f (Suc n) x = Option.bind (f x) (map_pow f n) "

definition cycle where "cycle f x \<longleftrightarrow> (\<exists>n. map_pow f (Suc n) x = Some x)"

lemma [simp]: "f x = None \<Longrightarrow> \<not> cycle f x" by (simp add: cycle_def)

lemma map_pow_0[simp]: "map_pow f 0 = Some" by auto

lemma map_pow_Suc': "map_pow f (Suc n) x = Option.bind (map_pow f n x) f"
 by (induction f n x rule:map_pow.induct)
    (simp_all cong: Option.bind_cong )


(* Better with relations *)
definition fun_graph where "fun_graph f x y \<longleftrightarrow> f x = Some y"

fun valid_stack' where
   "valid_stack' f y (x#xs) \<longleftrightarrow> (fun_graph f)\<^sup>+\<^sup>+ x y \<and> valid_stack' f x xs"
 | "valid_stack' f x [] \<longleftrightarrow> True"

lemma bind_some: "Option.bind x f = Some y \<longleftrightarrow> (\<exists> y'. x = Some y' \<and> f y' = Some y)"
  by (cases x, auto)

lemma rel_to_map_pow: "(fun_graph f)\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists> n. map_pow f (Suc n) x = Some y"
proof (induction rule:converse_tranclp_induct)
case (base x)
  hence "f x = Some y" unfolding fun_graph_def.
  hence "map_pow f (Suc 0) x = Some y" by simp
  thus ?case..
next
case (step x y')
  from this(3)
  obtain n where "map_pow f (Suc n) y' = Some y" by blast
  moreover
  from `fun_graph f x y'`
  have "f x = Some y'" unfolding fun_graph_def.
  ultimately
  have "map_pow f (Suc (Suc n)) x = Some y" by simp
  thus ?case..
qed

lemma map_pow_to_rel: "map_pow f (Suc n) x = Some y \<Longrightarrow> (fun_graph f)\<^sup>+\<^sup>+ x y"
proof (induction f "Suc n" x arbitrary: n rule:map_pow.induct)
case (2 f n x)

  from this(2)
  have "f x \<noteq> None" by (clarsimp simp add: bind_some)
  then obtain y' where "f x = Some y'" by auto
  hence "(fun_graph f) x y'" by (simp add: fun_graph_def)
  hence "(fun_graph f)\<^sup>+\<^sup>+ x y'" ..

  show ?case
  proof (cases "n")
  case 0
    with 2(2) `f x = Some y'`
    have "y' = y" by (auto)
    thus ?thesis using `(fun_graph f)\<^sup>+\<^sup>+ x y'` by simp
  next
  case (Suc n')
    note `(fun_graph f)\<^sup>+\<^sup>+ x y'` 
    also
    from `f x = Some y'` 2(2) Suc
    have "map_pow f (Suc n') y' = Some y" by simp
    with `f x = Some y'` Suc
    have "(fun_graph f)\<^sup>+\<^sup>+ y' y"
      by (rule "2.hyps")
    finally
    show ?thesis.
  qed
qed

lemma cycle_rel_def: "cycle f x \<longleftrightarrow> (fun_graph f)\<^sup>+\<^sup>+ x x"
  unfolding cycle_def
  by (auto intro: map_pow_to_rel dest!: rel_to_map_pow)


(* Hard to prove with the relation. *)
lemma image_also_cycle:
  assumes "f x = Some y"
  assumes "cycle f x"
  shows "cycle f y"
proof-
  from `cycle f x` obtain n where "map_pow f (Suc n) x = Some x" unfolding cycle_def ..
  hence "map_pow f n y = Some x" using `f x = Some y` by simp
  hence "map_pow f (Suc n) y = Some y"  using `f x = Some y` by (simp add: map_pow_Suc' del:map_pow.simps)
  thus "cycle f y" unfolding cycle_def ..
qed

lemma rel_also_cycle:
  assumes "(fun_graph f)\<^sup>+\<^sup>+ x y"
  assumes "cycle f x"
  shows "cycle f y"
using assms
by (induction)  (auto intro: image_also_cycle simp add: fun_graph_def) 

lemma fun_graphI[intro!]: "f x = Some y \<Longrightarrow> fun_graph f x y"
  unfolding fun_graph_def.

lemma valid_stack_rel:
  "valid_stack f y xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> (fun_graph f)\<^sup>+\<^sup>+ x y"
  by (induction f y xs rule:valid_stack.induct)
     (auto 0 3 elim: tranclp_trans)

lemma valid_stack'_rel:
  "valid_stack' f y xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> (fun_graph f)\<^sup>+\<^sup>+ x y"
  by (induction f y xs rule:valid_stack'.induct)
     (auto 0 3 elim: tranclp_trans)

lemma
  assumes "P' f x xs"
  assumes "valid_stack' f x xs"
  shows "\<not> cycle f x" and "P f x xs"
using assms
proof (induction rule: P'.induct)
  case P'Base
    case 1 from P'Base show ?case by simp
    case 2 from P'Base show ?case by (rule PBase)
next
  case (P'Step x y xs)
    from `f x = Some y`
    have "fun_graph f x y" by rule
    hence "(fun_graph f)\<^sup>+\<^sup>+ x y" by rule
    moreover
    assume "valid_stack' f x xs"
    ultimately
    have "valid_stack' f y (x # xs)" by simp
    note P'Step.IH[OF this]

    from `f x = Some y ` `\<not> cycle f y`
    show "\<not> cycle f x" by (auto simp add: image_also_cycle)

    have "y \<notin> set (x # xs)"
    proof
      from `f x = Some y`
      have "fun_graph f x y" by rule
      also
      assume "y \<in> set (x#xs)"
      with `valid_stack' f y _`
      have "(fun_graph f)\<^sup>+\<^sup>+ y y"  by (rule valid_stack'_rel)
      hence "cycle f y" unfolding cycle_rel_def.
      with `\<not> cycle f y`
      show False..
    qed
    with `f x = Some y` `P f y (x # xs)`
    show "P f x xs" by (rule PStep)
qed
