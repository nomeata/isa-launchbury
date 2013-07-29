theory LaunchburyAddBH
imports LaunchburyCombinedTaggedMap
begin

inductive depRel :: "Heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
  for \<Gamma>
  where DepRelVar: "lookup \<Gamma> y = Some (Var x) \<Longrightarrow> depRel \<Gamma> y x"
      | DepRelApp: "lookup \<Gamma> y = Some (App (Var x) z) \<Longrightarrow> depRel \<Gamma> y x"

lemma depRel_fmap_upd_Not[simp]: "a \<noteq> x \<Longrightarrow> depRel (\<Gamma>(x f\<mapsto> e)) a b \<longleftrightarrow> depRel \<Gamma> a b"
  by (auto elim!: depRel.cases intro:depRel.intros)

lemma depRelConsI[intro]: "a \<noteq> x \<Longrightarrow> depRel \<Gamma> a b \<Longrightarrow> depRel (\<Gamma>(x f\<mapsto> e)) a b"
  by simp

lemma depRel_dom: "depRel \<Gamma> y x \<Longrightarrow> y \<in> fdom \<Gamma>"
  by (cases \<Gamma> y x rule: depRel.cases) (auto simp add: fdomIff )

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
    from Application(1) have "n \<noteq> x" by (simp add: fresh_Pair fresh_at_base)
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
    hence IH2: "validStack (\<Delta>(x f\<mapsto> e'[z::=y])) x S" sorry
      (* Ansatz: n kommt nicht in S oder \<Delta> vor. Jede Kette die x enthält endet auch dort.
         Deswegen darf x entfernt werden. *)
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
    hence IH2: "validStack (\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e')) x S" sorry
      (* Ansatz: n kommt nicht in S oder \<Delta> vor. Jede Kette die x enthält endet auch dort.
         Deswegen darf x entfernt werden. *)
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

  from `validStack \<Delta> y (x # S)` `lookup \<Delta> x = Some (Var y)`
  show "validStack (fmap_copy \<Delta> y x) x S" sorry
    (* y ist Ende einer Kette, weil Lambda.
       Warum ist y \<notin> S?.. muss ich eh unten zeigen oder annehmen. *)

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

  from `validStack \<Delta> y (x # S)` `lookup \<Delta> x = Some (Var y)`
  show "validStack (fmap_copy \<Delta> y x) x S" sorry
    (* y ist Ende einer Kette, weil Lambda.
       Warum ist y \<notin> S?.. muss ich eh unten zeigen oder annehmen. *)

  (* Hier muss ich zeigen dass \<Down> die Struktur von DepRel, eingeschränkt auf S, erhält und nur ggf. verfeinert *)
  have "\<not> cycle \<Delta> y" sorry
  with hyps(2)
  have "y \<notin> set (x # S)" (* Hauptpunkt des Beweises! *)
    by (metis validStack_cycle)

  from this hyps(3)
  show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> fmap_copy \<Delta> y x"
    by (rule reds.Variable)
next
oops


end

