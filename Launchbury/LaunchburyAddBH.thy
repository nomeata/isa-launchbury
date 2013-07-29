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


inductive validStack :: "Heap \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> bool"
  for \<Gamma> where
    ValidStackNil: "validStack \<Gamma> x []"
  | ValidStackCons: "(depRel \<Gamma>)\<^sup>+\<^sup>+ y x \<Longrightarrow> validStack \<Gamma> y S \<Longrightarrow> validStack \<Gamma> x (y#S)"

lemma validStackIndirect:
  "validStack (\<Gamma>(x f\<mapsto> App e y)) z S \<Longrightarrow> atom n \<sharp> \<Gamma>(x f\<mapsto> App e y) \<Longrightarrow>
  validStack (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) z S"
by (induction z S rule:validStack.induct)
   (auto intro: ValidStackNil ValidStackCons depRelTransIndirect)


theorem
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta>"
  assumes "validStack \<Gamma> x S"
  shows "\<not> cycle \<Gamma> x"  "validStack \<Delta> x S" and "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
  (* The second conclusion does not need the first, but inductive proofs compose so badly. *)
using assms
proof(induction \<Gamma> i u b "x#S" \<Delta> arbitrary: x S rule:reds.induct )
case (Lambda x y e \<Gamma> i u b S)
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
  case 3
    note Application.hyps(1,2)
  
    moreover
    note Application.hyps(6)[OF IH1]
         Application.hyps(10)[OF IH2]
  
    ultimately
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
  case 3
    from ApplicationInd.hyps(1,2)
         ApplicationInd.hyps(6)[OF IH1]
         ApplicationInd.hyps(10)[OF IH2]
    show ?case by (rule reds.ApplicationInd)
next
  fix y x S \<Gamma> i \<Delta>
  assume hyp: "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S) \<Longrightarrow> validStack \<Delta> y (x # S)"

  have "(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y" by (fastforce intro: DepRelVar) 
  moreover
  assume "validStack (\<Gamma>(x f\<mapsto> Var y)) x S"
  ultimately
  have IP: "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S)"
    by (rule ValidStackCons)
  hence "validStack \<Delta> y (x # S)"
    by (rule hyp)
  thus "validStack (fmap_copy \<Delta> y x) x S" sorry
    (* Weiß ich, dass x \<mapsto> y immernoch gilt? *)
    (* y ist Ende einer Kette, weil Lambda.
       Warum ist y \<notin> S?.. muss ich eh unten zeigen oder annehmen. *)

  show "validStack (fmap_copy \<Delta> y x) x S" by fact


  {
    assume "y \<notin> set (x # S)"
    moreover
    assume "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>y # x # S\<^esub> \<Delta>"
    ultimately
    show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> (fmap_copy \<Delta> y x)"
      by (rule reds.Variable)
  next
    have "y \<notin> set (x # S)" sorry (* Hauptpunkt des Beweises! *)
    moreover
    assume "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S) \<Longrightarrow> \<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>y # x # S\<^esub> \<Delta>"
    note this[OF IP]
    ultimately
    show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> (fmap_copy \<Delta> y x)" by (rule reds.Variable)
  }
next
oops


end

