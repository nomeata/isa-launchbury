theory LaunchburyAddBH
imports LaunchburyCombinedTaggedMap
begin

lemma tranclp_mono: "r \<le> s \<Longrightarrow> r\<^sup>+\<^sup>+ \<le> s\<^sup>+\<^sup>+"
  apply (rule)
  apply (erule tranclp.induct)
  apply (auto)
  done

inductive depRel :: "Heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
  for \<Gamma>
  where DepRelVar: "lookup \<Gamma> y = Some (Var x) \<Longrightarrow> depRel \<Gamma> y x"
      | DepRelApp: "lookup \<Gamma> y = Some (App (Var x) z) \<Longrightarrow> depRel \<Gamma> y x"

lemma depRel_cong':
  "lookup \<Delta> a = lookup \<Gamma> a \<Longrightarrow> depRel \<Gamma> a b \<Longrightarrow> depRel \<Delta> a b"
  by (auto elim!: depRel.cases intro:depRel.intros)

lemma depRel_cong:
  "lookup \<Gamma> a = lookup \<Delta> a \<Longrightarrow> depRel \<Gamma> a b = depRel \<Delta> a b"
  by (metis depRel_cong')

lemma depRel_fmap_upd_Not[simp]: "a \<noteq> x \<Longrightarrow> depRel (\<Gamma>(x f\<mapsto> e)) a b \<longleftrightarrow> depRel \<Gamma> a b"
  by (simp cong: depRel_cong)

lemma depRelConsI[intro]: "a \<noteq> x \<Longrightarrow> depRel \<Gamma> a b \<Longrightarrow> depRel (\<Gamma>(x f\<mapsto> e)) a b"
  by simp

lemma depRel_dom: "depRel \<Gamma> y x \<Longrightarrow> y \<in> fdom \<Gamma>"
  by (cases \<Gamma> y x rule: depRel.cases) (auto simp add: fdomIff )

lemma depRel_change_not_Domain:
  assumes "\<not> Domainp (depRel \<Gamma>) x"
  assumes "fmap_delete x \<Gamma> = fmap_delete x \<Delta>"
  shows "depRel \<Gamma> \<le> depRel \<Delta>"
proof rule
  fix a b
  assume "depRel \<Gamma> a b"
  moreover
  hence "x \<noteq> a" using assms(1) by auto
  hence "lookup \<Gamma> a = lookup \<Delta> a" using assms(2) by (metis lookup_fmap_delete)
  ultimately
  show "depRel \<Delta> a b" using assms(2)
    by (simp cong: depRel_cong)
qed

(*
lemma depRelTransConsI[intro]: "(depRel \<Gamma>)\<^sup>+\<^sup>+ a b \<Longrightarrow> (depRel ((x,e)#\<Gamma>))\<^sup>+\<^sup>+ a b"
  by (induction rule: tranclp_trans_induct[consumes 1]) auto
*)

definition cycle where "cycle \<Gamma> x \<longleftrightarrow> (depRel \<Gamma>)\<^sup>+\<^sup>+ x x"

lemma depRelE: "depRel \<Gamma> x y \<Longrightarrow> (\<exists> z. lookup \<Gamma> x = Some (Var z)) \<or> (\<exists> z y. lookup \<Gamma> x = Some (App (Var z) y))"
  by  (auto elim: depRel.cases)

lemma depRelTransE: "(depRel \<Gamma>)\<^sup>+\<^sup>+ x y \<Longrightarrow> (\<exists> z. lookup \<Gamma> x = Some (Var z)) \<or> (\<exists> z y. lookup \<Gamma> x = Some (App (Var z) y))"
  by (induction x y rule: tranclp_trans_induct[consumes 1, case_names base step])
     (auto dest: depRelE)

lemma lookup_eq_split: "lookup (f(a f\<mapsto> b)) x = Some r \<longleftrightarrow> ((x = a \<and> r = b) \<or> (x \<noteq> a \<and> lookup f x = Some r))"
  by transfer auto

lemma depRelAppE:
  "depRel (\<Gamma>(x f\<mapsto> App e y)) a b \<Longrightarrow> x = a \<and> e = Var b \<or> x \<noteq> a \<and> depRel \<Gamma> a b"
  by (induction rule:depRel.cases) 
     (auto simp add: lookup_eq_split intro: depRel.intros)

lemma depRelTransIndirect: 
  assumes "(depRel (\<Gamma>(x f\<mapsto> App e y)))\<^sup>+\<^sup>+ a b"
  assumes "atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)"
  shows "(depRel (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)))\<^sup>+\<^sup>+  a b"
using assms
proof (induction rule:tranclp_trans_induct[consumes 1, case_names base step])
  case (base a b)
  note depRel_dom[OF `depRel (\<Gamma>(x f\<mapsto> App e y)) a b`]
  with `atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)`
  have "n \<noteq> a"  by (metis fresh_fdom)

  from depRelAppE[OF base(1)]
  show ?case
  proof(elim conjE disjE)
    assume "x = a" and "e = Var b"

    have "(depRel (\<Gamma>(a f\<mapsto> App (Var n) y)(n f\<mapsto> Var b)))\<^sup>+\<^sup>+ a n" using `n \<noteq> a`
      by (fastforce intro: DepRelApp)
    also
    have "(depRel (\<Gamma>(a f\<mapsto> App (Var n) y)(n f\<mapsto> Var b)))\<^sup>+\<^sup>+ n b" 
      by (fastforce intro: DepRelVar)
    finally
    show ?thesis unfolding `x = a` `e = Var b`.
  next
    assume "x \<noteq> a " and "depRel \<Gamma> a b"  thus ?thesis using `n \<noteq> a` by auto
  qed
  next
  case (step a b c)
    thus ?case by auto
qed

lemma cycleIndirect: 
  assumes "cycle (\<Gamma>(x f\<mapsto> App e y)) z"
  assumes "atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)"
  shows "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) z"
by (metis depRelTransIndirect cycle_def assms)

inductive validStack :: "Heap \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> bool"
  for \<Gamma> where
    ValidStackNil: "validStack \<Gamma> x []"
  | ValidStackCons: "(depRel \<Gamma>)\<^sup>+\<^sup>+ y x \<Longrightarrow> validStack \<Gamma> y S \<Longrightarrow> validStack \<Gamma> x (y#S)"

lemma validStackIndirect:
  "validStack (\<Gamma>(x f\<mapsto> App e y)) z S \<Longrightarrow> atom n \<sharp> \<Gamma>(x f\<mapsto> App e y) \<Longrightarrow>
  validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) z S"
by (induction z S rule:validStack.induct)
   (auto intro: ValidStackNil ValidStackCons depRelTransIndirect)

lemma depRel_unique:
  "depRel \<Gamma> a b \<Longrightarrow> depRel \<Gamma> a c \<Longrightarrow> b = c"
  by (auto elim!: depRel.cases)

lemma validStack_to_top:
  "validStack \<Gamma> x S \<Longrightarrow> y \<in> set S \<Longrightarrow> (depRel \<Gamma>)\<^sup>+\<^sup>+ y x"
by (induction x S rule:validStack.induct) auto

lemma validStack_cycle:
  "validStack \<Gamma> x S \<Longrightarrow> x \<in> set S \<Longrightarrow> cycle \<Gamma> x"
by (metis validStack_to_top cycle_def)

lemma depRel_via:
  assumes "(depRel \<Gamma>)\<^sup>+\<^sup>+ a z"
  assumes "depRel \<Gamma> a b"
  shows   "b = z \<or> (depRel \<Gamma>)\<^sup>+\<^sup>+ b z"
using assms
by (induction a z rule:tranclp_trans_induct[consumes 1, case_names base step])
   (auto dest: depRel_unique tranclp_trans)

lemma validStackMono:
  "validStack \<Gamma> z S \<Longrightarrow> (depRel \<Gamma>)\<^sup>+\<^sup>+ \<le> (depRel \<Delta>)\<^sup>+\<^sup>+ \<Longrightarrow> validStack \<Delta> z S"
by (induction z S  rule:validStack.induct)(auto intro: validStack.intros)

lemma validStack_cong:
  assumes "validStack \<Gamma> z S"
  assumes cong: "\<And> x. (depRel \<Gamma>)\<^sup>+\<^sup>+ x z \<Longrightarrow> lookup \<Gamma> x = lookup \<Delta> x"
  shows  "validStack \<Delta> z S"
using assms
proof(induction z S rule:validStack.induct)
  case (ValidStackNil y) thus ?case by (intro validStack.intros)
next
  case (ValidStackCons y x S)
  from `(depRel \<Gamma>)\<^sup>+\<^sup>+ y x` ValidStackCons.prems
  have "(depRel \<Delta>)\<^sup>+\<^sup>+ y x"
  proof (induction y x rule:tranclp_trans_induct[consumes 1, case_names base step])
    case (base x' y)
    hence "lookup \<Gamma> x' = lookup \<Delta> x'" by auto
    with base(1)
    have "depRel \<Delta> x' y" by (simp cong: depRel_cong)
    thus ?case by auto
  next
    case step thus ?case by (metis tranclp_trans)
  qed
  moreover
  have "validStack \<Delta> y S"
  proof(rule ValidStackCons.IH)
    fix x'
    assume "(depRel \<Gamma>)\<^sup>+\<^sup>+ x' y" with `(depRel \<Gamma>)\<^sup>+\<^sup>+ y x`
    have "(depRel \<Gamma>)\<^sup>+\<^sup>+ x' x" by auto
    thus " lookup \<Gamma> x' = lookup \<Delta> x'"
      by (rule ValidStackCons)
  qed
  ultimately
  show "validStack \<Delta> x (y # S)"
    by (rule validStack.intros)
qed


(*
lemma validStackNextThere:
  "validStack \<Gamma> z S \<Longrightarrow> x \<in> set S \<Longrightarrow> depRel \<Gamma> x y \<Longrightarrow> y \<in> set (z#S)"
proof (induction z S arbitrary: y rule:validStack.induct)
  case ValidStackNil thus ?case by auto
next
  case (ValidStackCons y x' S y')
apply auto[1]
apply auto
*)



lemma cycle_depRel:
  assumes "cycle \<Gamma> x"
  assumes "depRel \<Gamma> x n"
  shows "cycle \<Gamma> n"
by (metis assms depRel_via cycle_def tranclp.simps)

theorem
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta>"
  assumes "validStack \<Gamma> x S"
  shows "\<not> cycle \<Gamma> x"  "validStack \<Delta> x S" and "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
  (* The third conclusion does not need the second, but inductive proofs compose so badly. *)
using assms
proof(induction \<Gamma> i u b "x#S" \<Delta> arbitrary: x S rule:reds.induct )
case (Lambda \<Gamma> x y e i u b S)
  case 1 show ?case by (auto dest: depRelTransE simp add: cycle_def) 
  case 2 thus ?case .
  case 3 show ?case by (rule reds.Lambda)
next
case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
  case 2
    from Application(1) have "n \<noteq> x"  "n \<notin> set S"
      by (simp_all add: fresh_Pair fresh_at_base fresh_at_base_list)
    hence "(depRel (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)))\<^sup>+\<^sup>+ x n" by (fastforce intro: DepRelApp)
    moreover
    from Application(1) have "atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)"
      by (simp add: fresh_Pair fresh_fmap_upd_eq fresh_fmap_delete_subset)
    with `validStack (\<Gamma>(x f\<mapsto> App e y)) x S`
    have "validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x S" by (rule validStackIndirect)
    ultimately
    have IH1: "validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n (x # S)"  by (rule ValidStackCons)
    hence "validStack (\<Delta>(n f\<mapsto> Lam [z]. e')) n (x # S)" by (rule Application.hyps)
    hence "validStack (\<Delta>(n f\<mapsto> Lam [z]. e')) x S" by (cases)
    hence IH2: "validStack (\<Delta>(x f\<mapsto> e'[z::=y])) x S"
    proof(rule validStack_cong)
      from stack_unchanged[OF Application.hyps(6)[OF IH1]] `n \<noteq> x`
      have "lookup (\<Delta>(n f\<mapsto> Lam [z]. e')) x = Some (App (Var n) y)"  by auto
      hence "depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n" by (rule DepRelApp)

      fix x'
      assume "(depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x' x"
      moreover
      have "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ n x"
        by (metis depRelTransE exp_assn.distinct(5) exp_assn.distinct(9) lookup_fmap_upd the.simps)
      moreover
      hence "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x x" using `depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n`
        by (metis depRel_via)
      ultimately
      have "x' \<noteq> x" "x' \<noteq> n" by auto
      thus "lookup (\<Delta>(n f\<mapsto> Lam [z]. e')) x' = lookup (\<Delta>(x f\<mapsto> e'[z::=y])) x'" by simp
    qed
    thus "validStack \<Theta> x S"
      by (rule Application.hyps)
  case 1
    from Application.hyps(4)[OF IH1]
    show ?case
    proof(rule contrapos_nn)
      assume "cycle (\<Gamma>(x f\<mapsto> App e y)) x"
      hence "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x"
        by (rule cycleIndirect[OF _ `atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)`])
      thus "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n" using `n \<noteq> x`
        by (auto elim!: cycle_depRel intro: DepRelApp)
    qed
  case 3
    from Application.hyps(1,2)
         Application.hyps(6)[OF IH1]
         Application.hyps(10)[OF IH2]
    show ?case by (rule reds.Application)
next
case (ApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
case 2
    from ApplicationInd(1) have "n \<noteq> x" by (simp add: fresh_Pair fresh_at_base)
    hence "(depRel (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)))\<^sup>+\<^sup>+ x n" by (fastforce intro: DepRelApp)
    moreover
    from ApplicationInd(1) have "atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)"
      by (simp add: fresh_Pair fresh_fmap_upd_eq fresh_fmap_delete_subset)
    with `validStack (\<Gamma>(x f\<mapsto> App e y)) x S`
    have "validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x S" by (rule validStackIndirect)
    ultimately
    have IH1: "validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n (x # S)"  by (rule ValidStackCons)
    hence "validStack (\<Delta>(n f\<mapsto> Lam [z]. e')) n (x # S)" by (rule ApplicationInd.hyps)
    hence "validStack (\<Delta>(n f\<mapsto> Lam [z]. e')) x S" by (cases)
    hence IH2: "validStack (\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e')) x S"
    proof(rule validStack_cong)
      from stack_unchanged[OF ApplicationInd.hyps(6)[OF IH1]] `n \<noteq> x`
      have "lookup (\<Delta>(n f\<mapsto> Lam [z]. e')) x = Some (App (Var n) y)"  by auto
      hence "depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n" by (rule DepRelApp)

      fix x'
      assume as: "(depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x' x"
      moreover
      have "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ n x"
        by (metis depRelTransE exp_assn.distinct(5) exp_assn.distinct(9) lookup_fmap_upd the.simps)
      moreover
      hence "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x x" using `depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n`
        by (metis depRel_via)
      ultimately
      have "x' \<noteq> x" "x' \<noteq> n" by auto
      moreover
      from as `x' \<noteq> n`
      have "x' \<in> fdom \<Delta>" by (metis (hide_lams, no_types) converse_tranclpE depRel_dom fmap_upd_fdom insert_iff)
      with ApplicationInd(2)
      have "x' \<noteq> z" by (auto simp add: fresh_Pair)
      ultimately
      show "lookup (\<Delta>(n f\<mapsto> Lam [z]. e')) x' =  lookup (\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e')) x'" by simp
    qed
    thus "validStack \<Theta> x S"
      by (rule ApplicationInd.hyps)
  case 1
    from ApplicationInd.hyps(4)[OF IH1]
    show ?case
    proof(rule contrapos_nn)
      assume "cycle (\<Gamma>(x f\<mapsto> App e y)) x"
      hence "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x"
        by (rule cycleIndirect[OF _ `atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)`])
      thus "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n" using `n \<noteq> x`
        by (auto elim!: cycle_depRel intro: DepRelApp)
    qed
  case 3
    from ApplicationInd.hyps(1,2)
         ApplicationInd.hyps(6)[OF IH1]
         ApplicationInd.hyps(10)[OF IH2]
    show ?case by (rule reds.ApplicationInd)
next
case (Variable y x S \<Gamma> i \<Delta>)
  hence "y \<noteq> x" by simp

  have "(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y" by (fastforce intro: DepRelVar) 
  moreover
  assume "validStack (\<Gamma>(x f\<mapsto> Var y)) x S"
  ultimately
  have "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S)"
    by (rule ValidStackCons)
  note hyps = Variable(3-5)[OF this]

  from stack_unchanged[OF hyps(3)] `y \<noteq> x`
  have "lookup \<Delta> x = Some (Var y)" by simp
  hence "depRel \<Delta> x y" by (auto intro: depRel.intros)

  from result_evaluated[OF hyps(3)]
  have "isLam (\<Delta> f! y)" by simp
  hence "\<not> Domainp (depRel \<Delta>) y" by (auto elim: depRel.cases)

  from `validStack \<Delta> y (x # S)` 
  have "validStack \<Delta> x S" by cases
  thus "validStack (fmap_copy \<Delta> y x) x S"
  proof (rule validStack_cong)
    fix x'
    assume "(depRel \<Delta>)\<^sup>+\<^sup>+ x' x"
    moreover
    from `\<not> Domainp (depRel \<Delta>) y`
    have " \<not>(depRel \<Delta>)\<^sup>+\<^sup>+ y x" by (metis Domainp.DomainI converse_tranclpE)
    hence " \<not>(depRel \<Delta>)\<^sup>+\<^sup>+ x x" using `depRel \<Delta> x y` by (metis depRel_via)
    ultimately
    have "x' \<noteq> x" by auto
    thus "lookup \<Delta> x' = lookup (fmap_copy \<Delta> y x) x'" by simp
  qed

  from hyps(1)
  show "\<not> cycle (\<Gamma>(x f\<mapsto> Var y)) x"
    by (auto elim!: contrapos_nn cycle_depRel intro: DepRelVar)

  from Variable(1,2) 
  show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> fmap_copy \<Delta> y x"
    by (rule reds.Variable)
next
case (VariableNoBH \<Gamma> x y i S \<Delta>)
  have "(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y" by (fastforce intro: DepRelVar) 
  moreover
  assume "validStack (\<Gamma>(x f\<mapsto> Var y)) x S"
  ultimately
  have "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S)"
    by (rule ValidStackCons)
  note hyps = VariableNoBH(2-4)[OF this]

  from hyps(1) `(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y`
  have "y \<noteq> x" by (auto simp add: cycle_def)

  from stack_unchanged[OF hyps(3)] `y \<noteq> x`
  have "lookup \<Delta> x = Some (Var y)" by simp
  hence "depRel \<Delta> x y" by (auto intro: depRel.intros)

  from result_evaluated[OF hyps(3)]
  have "isLam (\<Delta> f! y)" by simp
  hence "\<not> Domainp (depRel \<Delta>) y" by (auto elim: depRel.cases)

  from `validStack \<Delta> y (x # S)` 
  have "validStack \<Delta> x S" by cases
  thus "validStack (fmap_copy \<Delta> y x) x S"
  proof (rule validStack_cong)
    fix x'
    assume "(depRel \<Delta>)\<^sup>+\<^sup>+ x' x"
    moreover
    from `\<not> Domainp (depRel \<Delta>) y`
    have " \<not>(depRel \<Delta>)\<^sup>+\<^sup>+ y x" by (metis Domainp.DomainI converse_tranclpE)
    hence " \<not>(depRel \<Delta>)\<^sup>+\<^sup>+ x x" using `depRel \<Delta> x y` by (metis depRel_via)
    ultimately
    have "x' \<noteq> x" by auto
    thus "lookup \<Delta> x' = lookup (fmap_copy \<Delta> y x) x'" by simp
  qed

  from hyps(1)
  show "\<not> cycle (\<Gamma>(x f\<mapsto> Var y)) x"
    by (auto elim!: contrapos_nn cycle_depRel intro: DepRelVar)

  from hyps(1) `validStack (\<Gamma>(x f\<mapsto> Var y)) y (x#S)`
  have "y \<notin> set (x # S)"
    by (metis validStack_cycle)

  from this hyps(3)
  show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> fmap_copy \<Delta> y x"
    by (rule reds.Variable)
next
oops


end

