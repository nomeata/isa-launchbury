theory LaunchburyAddBH
imports LaunchburyCombinedTagged 
begin

inductive depRel :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
  for \<Gamma>
  where DepRelVar: "(y, Var x) \<in> set \<Gamma> \<Longrightarrow> depRel \<Gamma> y x"
      | DepRelApp: "(y, App (Var x) z) \<in> set \<Gamma> \<Longrightarrow> depRel \<Gamma> y x"

lemma depRelCons_Not[simp]: "a \<noteq> x \<Longrightarrow> depRel ((x,e)#\<Gamma>) a b \<longleftrightarrow> depRel \<Gamma> a b"
  by (auto elim!: depRel.cases intro:depRel.intros)

lemma depRelConsI[intro]: "depRel \<Gamma> a b \<Longrightarrow> depRel ((x,e)#\<Gamma>) a b"
  by (auto elim!: depRel.cases intro:depRel.intros)

lemma depRelTransConsI[intro]: "(depRel \<Gamma>)\<^sup>+\<^sup>+ a b \<Longrightarrow> (depRel ((x,e)#\<Gamma>))\<^sup>+\<^sup>+ a b"
  by (induction rule: tranclp_trans_induct[consumes 1]) auto

inductive validStack :: "heap \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> bool"
  for \<Gamma> where
    ValidStackNil: "validStack \<Gamma> x []"
  | ValidStackCons: "(depRel \<Gamma>)\<^sup>+\<^sup>+ y x \<Longrightarrow> validStack \<Gamma> y S \<Longrightarrow> validStack \<Gamma> x (y#S)"


lemma depRelAppE:
  "depRel ((x, App e y) # \<Gamma>) a b \<Longrightarrow> (x = a \<and> e = Var b) \<or> depRel \<Gamma> a b"
  by (induction rule:depRel.cases) (auto intro: depRel.intros)

lemma depRelTransIndirect: 
  assumes "(depRel ((x, App e y) # \<Gamma>))\<^sup>+\<^sup>+ a b"
  shows "(depRel ((n, e) # (x, App (Var n) y) # \<Gamma>))\<^sup>+\<^sup>+  a b"
using assms
proof (induction rule:tranclp_trans_induct[consumes 1, case_names base step])
  case (base a b)
  from depRelAppE[OF this]
  show ?case
  proof(elim conjE disjE)
    assume "x = a" and "e = Var b"

    have "(depRel ((n, Var b) # (a, App (Var n) y) # \<Gamma>))\<^sup>+\<^sup>+ a n"
      by (fastforce intro: DepRelApp)
    also
    have "(depRel ((n, Var b) # (a, App (Var n) y) # \<Gamma>))\<^sup>+\<^sup>+ n b"
      by (fastforce intro: DepRelVar)
    finally
    show ?thesis unfolding `x = a` `e = Var b`.
  next
    assume "depRel \<Gamma> a b" thus ?thesis by auto
  qed
  next
  case (step a b c)
    thus ?case by auto
qed

lemma validStackIndirect:
  "validStack ((x, App e y) # \<Gamma>) z S \<Longrightarrow> validStack ((n, e) # (x, App (Var n) y) # \<Gamma>) z S"
by (induction z S rule:validStack.induct)
   (auto intro: ValidStackNil ValidStackCons depRelTransIndirect)

lemma validStackPres: "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta> \<Longrightarrow> validStack \<Gamma> x S \<Longrightarrow> validStack \<Delta> x S"
proof(induction \<Gamma> i u b "x#S" \<Delta> arbitrary: x S rule:reds.induct )
  case Lambda thus ?case .
next
  case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
    have "(depRel ((n, e) # (x, App (Var n) y) # \<Gamma>))\<^sup>+\<^sup>+ x n" by (fastforce intro: DepRelApp)
    moreover
    from `validStack ((x, App e y) # \<Gamma>) x S`
    have "validStack ((n, e) # (x, App (Var n) y) # \<Gamma>) x S" by (rule validStackIndirect)
    ultimately
    have "validStack ((n, e) # (x, App (Var n) y) # \<Gamma>) n (x # S)"  by (rule ValidStackCons)
    hence "validStack ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>) n (x # S)" by (rule Application.hyps)
    hence "validStack ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>) x S" by (cases)
    hence "validStack ((x, e'[z::=y]) # \<Delta>) x S" sorry
    hence "validStack \<Theta> x S"
      by (rule Application.hyps)
oops

theorem "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta> \<Longrightarrow> validStack \<Gamma> x S \<Longrightarrow> \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
proof(induction \<Gamma> i u b "x#S" \<Delta> arbitrary: x S rule:reds.induct )
print_cases
case (Lambda x y e \<Gamma> i u b S)
  show ?case by (rule reds.Lambda)
next
case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
  from Application.IH obtain 




end

