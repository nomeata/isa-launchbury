theory LaunchburyCombinedTagged
imports Terms Heap  "~~/src/HOL/Library/Permutation"
begin

lemma perm_eqvt[eqvt]: "\<pi> \<bullet> (G <~~> G') \<longleftrightarrow> (\<pi> \<bullet> G) <~~> (\<pi> \<bullet> G')"
  by (auto intro!: perm_rel_lemma2 elim: perm.induct simp add: permute_pure)

lemma perm_supp: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> supp \<Gamma> = supp \<Gamma>'"
  by (induction rule: perm.induct) (auto simp add: supp_Cons)

lemma perm_heapVars: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> heapVars \<Gamma> = heapVars \<Gamma>'"
  by (induction rule: perm.induct) auto

lemma perm_distinctVars: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> distinctVars \<Gamma> \<longleftrightarrow> distinctVars \<Gamma>'"
  by (induction rule: perm.induct) (auto simp add: distinctVars_Cons perm_heapVars)

datatype Flag = FlagSet ("\<surd>") | FlagNotSet ("\<times>")

instantiation  Flag :: pure
begin
  definition "p \<bullet> (v::Flag) = v"
instance
  apply default
  apply (auto simp add: permute_Flag_def)
  done
end

inductive reds :: "heap \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> bool" ("_/ \<Down>\<^sup>_\<^sup>_\<^bsub>_\<^esub>/ _" [50,50,50,50,50] 50)
where
  Lambda:
    "(x, (Lam [y]. e)) # \<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>x#S\<^esub> (x, (Lam [y]. e)) # \<Gamma>" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^bsub>n#x#S\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (x, e'[z ::= y]) # \<Delta> \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x#S\<^esub> \<Theta>" 
 | ApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>n#x#S\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (z,Var y) # (x, e') # \<Delta> \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>x#S\<^esub> \<Theta>" 
 | Variable: "\<lbrakk>
      y \<notin> set (x#S);
      (x, Var y) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>y#x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
 | VariableNoUpd: "\<lbrakk>
      y \<notin> set (x#S);
      (x, Var y) # (y,e) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>y#x#S\<^esub> (y,z) # \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # (y,e) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>x#S\<^esub> (y,e) # \<Delta>"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x);
      distinctVars (asToHeap as);
      (x, body) # asToHeap as @ \<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Let as body) # \<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>x#S\<^esub> \<Delta>"
 | Permute: "\<lbrakk>
      \<Gamma> <~~> \<Gamma>';
      \<Delta> <~~> \<Delta>';
      \<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow> 
      \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta>'"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z" | ApplicationInd: "n"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)


(*
subsubsection {* Example evaluations *}

lemma eval_test:
  "y \<noteq> x \<Longrightarrow> [] : [(x, Let (ACons y (Lam [z]. Var z) ANil) (Var y))] \<Down>\<^sup>\<times>\<^sup>\<surd> [(y, Lam [z]. Var z)] : [(x, (Lam [z]. Var z))]"
by (auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def exp_assn.bn_defs fresh_at_base)

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> z \<noteq> x \<Longrightarrow> [] : [(x,  Let (ACons y (Lam [z]. Var z) ANil) (App (Var y) y))] \<Down>\<^sup>\<times>\<^sup>\<surd> [(y, Lam [z]. Var z)] : [(x, (Lam [z]. Var z))]"
  apply (rule Let)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base  fresh_Nil fresh_star_def exp_assn.bn_defs)
  apply simp
  apply (rule obtain_fresh)
  apply (erule Application[where z = z])
  defer
    apply (rule Variable, simp)
    apply (rule Lambda)
    apply simp
    apply (rule Variable, simp)
    apply simp
    apply (rule Lambda)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base fresh_Nil fresh_star_def)
  done
*)

subsubsection {* Properties of the semantics *}

text {*
This is the same semantics with additional distinctiveness requirements. This is defined in order to
obtain a more convenient induction rule.
*}

inductive distinct_reds :: "heap \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> bool" ("_/ \<Down>\<^sup>_\<^sup>_\<^sup>d\<^bsub>_\<^esub>/ _" [50,50,50,50,50] 50)
where
  DLambda: "\<lbrakk>
      distinctVars ((x, (Lam [y]. e)) # \<Gamma>);
      distinct (x#S)
  \<rbrakk> \<Longrightarrow> 
      (x, (Lam [y]. e)) # \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> (x, (Lam [y]. e)) # \<Gamma>" 
 | DApplication: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>);
      distinctVars ((x, App e y) # \<Gamma>);
      distinctVars ((n, e) # (x, App (Var n) y) # \<Gamma>);
      distinctVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>);
      distinctVars ((x, e'[z ::= y]) # \<Delta>);
      distinctVars \<Theta>;
      distinct (x#S);
      distinct (n#x#S);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^sup>d\<^bsub>n#x#S\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (x, e'[z ::= y]) # \<Delta> \<Down>\<^sup>\<times>\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Theta>" 
 | DApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>);
      distinctVars ((x, App e y) # \<Gamma>);
      distinctVars ((n, e) # (x, App (Var n) y) # \<Gamma>);
      distinctVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>);
      distinctVars ((z,Var y) # (x, e') # \<Delta>);
      distinctVars \<Theta>;
      distinct (x#S);
      distinct (n#x#S);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d\<^bsub>n#x#S\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (z,Var y) # (x, e') # \<Delta> \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Theta>" 
 | DVariable: "\<lbrakk>
      y \<notin> set (x#S);
      distinctVars ((x, Var y) # \<Gamma>);
      distinctVars \<Delta>;
      distinct (x#S);
      distinct (y#x#S);
      (x, Var y) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d\<^bsub>y#x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d\<^bsub>x#S\<^esub> \<Delta>"
 | DVariableNoUpd: "\<lbrakk>
      y \<notin> set (x#S);
      distinctVars ((x, Var y) # (y,e) # \<Gamma>);
      distinctVars ((y,z) # \<Delta>);
      distinctVars ((y,e) # \<Delta>);
      distinct (x#S);
      distinct (y#x#S);
      (x, Var y) # (y,e) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d\<^bsub>y#x#S\<^esub> (y,z) # \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # (y,e) # \<Gamma> \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d\<^bsub>x#S\<^esub> (y,e) # \<Delta>"
 | DLet: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x);
      distinctVars (asToHeap as);
      distinctVars ((x, Let as body) # \<Gamma>);
      distinctVars ((x, body) # asToHeap as);
      distinctVars \<Delta>;
      distinct (x#S);
      (x, body) # asToHeap as @ \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Let as body) # \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Delta>"
 | DPermute: "\<lbrakk>
      \<Gamma> <~~> \<Gamma>';
      \<Delta> <~~> \<Delta>';
      distinctVars \<Gamma>;
      distinctVars \<Gamma>';
      distinctVars \<Delta>;
      distinctVars \<Delta>';
      distinct S;
      \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow> 
      \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>'"

equivariance distinct_reds

nominal_inductive distinct_reds
  avoids DApplication: "n" and "z" | DApplicationInd: "n"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)

lemma distinct_redsD1:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> \<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta>"
  by (induct rule: distinct_reds.induct) (blast intro: reds.intros)+

lemma distinct_redsD2:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> distinctVars \<Gamma>"
  by (induct rule: distinct_reds.induct) simp_all

lemma distinct_redsD3:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> distinctVars \<Delta>"
  by (induct rule: distinct_reds.induct) simp_all

  thm DApplication[no_vars]

lemma distinct_redsI:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinct S \<Longrightarrow> \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>"
proof (nominal_induct rule: reds.strong_induct)
case Lambda thus ?case by (auto intro: DLambda)
next
case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u e')
  have "atom n \<sharp> (\<Gamma>, x, e, y, S, \<Delta>, \<Theta>, z)" and "atom z \<sharp> (\<Gamma>, x, e, y, S, \<Delta>, \<Theta>)"
    using Application by simp+
  moreover

  from Application
  have "distinctVars ((n, e) # (x, App (Var n) y) # \<Gamma>)" and "distinct (n#x#S)"
    by (auto simp add: distinctVars_Cons heapVars_not_fresh set_not_fresh)
  note Application(17)[OF this]
  moreover

  from distinct_redsD3[OF this]
  have "distinctVars ((x, e'[z::=y]) # \<Delta>)"
    by (auto simp add: distinctVars_Cons heapVars_not_fresh set_not_fresh)
  note Application(19)[OF this  `distinct (x # S)`]
  moreover
  note `distinctVars ((x, App e y) # \<Gamma>)` `distinct (x#S)` `distinct (n#x#S)`
  ultimately
  show ?case
    by (auto intro: DApplication elim:  distinct_redsD2 distinct_redsD3)
next
case (ApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z u e')
  have "atom n \<sharp> (\<Gamma>, x, e, y, S, \<Delta>, \<Theta>, z)" and "atom z \<sharp> (\<Gamma>, x, e, y, S, \<Delta>)"
    using ApplicationInd by simp+
  moreover

  from ApplicationInd
  have "distinctVars ((n, e) # (x, App (Var n) y) # \<Gamma>)" and "distinct (n#x#S)"
    by (auto simp add: distinctVars_Cons heapVars_not_fresh set_not_fresh)
  note ApplicationInd(16)[OF this]
  moreover

  from distinct_redsD3[OF this] `atom z \<sharp> x` `atom z \<sharp> \<Delta>`
  have "distinctVars ((z, Var y) # (x, e') # \<Delta>)"
    by (auto simp add: distinctVars_Cons heapVars_not_fresh set_not_fresh)
  note ApplicationInd(18)[OF this  `distinct (x # S)`]
  moreover
  note `distinctVars ((x, App e y) # \<Gamma>)` `distinct (x#S)` `distinct (n#x#S)`
  ultimately
  show ?case
    by (auto intro: DApplicationInd elim:  distinct_redsD2 distinct_redsD3)
next
case Variable
  thus ?case by (auto intro: DVariable elim: distinct_redsD3)
next
case (VariableNoUpd y x S e \<Gamma> i z \<Delta>)
  hence "distinct (y # x # S)" by simp
  from VariableNoUpd(3)[OF `distinctVars ((x, Var y) # (y, e) # \<Gamma>)` this]
        `distinctVars ((x, Var y) # (y, e) # \<Gamma>)`
        `distinct (x#S)` `y \<notin> set (x # S)`
  show ?case
    by (auto intro!: DVariableNoUpd dest: distinct_redsD3 simp add: distinctVars_Cons)
next
case (Let as \<Gamma> x body i u S \<Delta>)
  moreover
  from Let(1-4,6)
  have "distinctVars ((x, body) # asToHeap as @ \<Gamma>)"
    apply (auto simp add: distinctVars_Cons distinctVars_append dest: fresh_assn_distinct)
    by (metis (hide_lams, mono_tags) IntI all_not_in_conv fresh_assn_distinct fresh_star_Pair fresh_star_list(1) fresh_star_list(2)  heapVars_from_set in_set_conv_decomp let_binders_fresh)
  moreover
  note Let(5)[OF this `distinct (x # S)`]
  ultimately
  show ?case
    by (auto intro!: DLet dest: distinct_redsD3 simp add: distinctVars_Cons fresh_star_Pair)
next
case (Permute \<Gamma> \<Gamma>' \<Delta> \<Delta>' i u S)
  thus ?case
    apply -
    apply (rule DPermute, assumption+)
    apply (auto dest: distinct_redsD3 simp add: perm_distinctVars)
    done
qed

lemma reds_pres_distinctVars:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinct S \<Longrightarrow> distinctVars \<Delta>"
by (metis distinct_redsD3 distinct_redsI)

lemmas reds_distinct_ind = distinct_reds.induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]
lemmas reds_distinct_strong_ind = distinct_reds.strong_induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]

lemma reds_doesnt_forget':
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>"
  shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
using assms
  by (induct rule: distinct_reds.induct)
     (auto simp add: perm_heapVars fresh_Pair dest: heapVars_not_fresh)

text {* Heap entries are never removed. *}

lemma reds_doesnt_forget:
 assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta>"
 assumes "distinctVars \<Gamma>"
 assumes "distinct S"
 shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
by (rule reds_doesnt_forget'[OF distinct_redsI[OF assms]])+

text {* The stack is never empty. *}

lemma stack_not_empty:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>S\<^esub> \<Delta>"
  shows "S \<noteq> []"
  using assms
  by (induct rule:reds.induct, simp_all)

text {* Evaluation does not touch the tail of the stack. *}

lemma stack_unchanged:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>"
  assumes "x \<in> set (tl S)"
  assumes "(x,e) \<in> set \<Gamma>"
  shows   "(x,e) \<in> set \<Delta>"
using assms
 by (induct arbitrary: x e rule:distinct_reds.induct)(auto simp add: perm_set_eq)


text {* 
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta>;
   atom (x::var) \<sharp> \<Gamma>
  \<rbrakk> \<Longrightarrow> atom x \<sharp> \<Delta> \<or> x \<in> heapVars \<Delta>"
proof(nominal_induct avoiding: x rule: distinct_reds.strong_induct)
case (DLambda \<Gamma> x e) thus ?case by auto
next
case (DApplication n \<Gamma> x e y S \<Delta> \<Theta> z e' u x')
  from `atom n \<sharp> x'` `atom x' \<sharp> (x, App e y) # \<Gamma>`
  have "atom x' \<sharp> (n, e) # (x, App (Var n) y) # \<Gamma>"
    by (auto simp add: fresh_Pair fresh_Cons)
  from DApplication.hyps(26)[OF this]
  show ?case
  proof
    assume "atom x' \<sharp> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>"
    with `atom z \<sharp> x'`
    have "atom x' \<sharp> (x, e'[z::=y]) # \<Delta>"
      by (simp add: fresh_Cons fresh_Pair subst_pres_fresh fresh_at_base)
    from DApplication.hyps(28)[OF this]
    show ?thesis.
  next
    assume "x' \<in> heapVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>)"
    with `atom n \<sharp> x'`
    have "x' \<in> heapVars ((x, e'[z::=y]) # \<Delta>)" by (simp add: fresh_at_base)
    with reds_doesnt_forget'[OF DApplication(27)]
    have "x' \<in> heapVars \<Theta>" by auto
    thus ?thesis..
  qed
next
case (DApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z e' u x')
  show ?case
  proof(cases "x' = z")
  case True
    with  reds_doesnt_forget'[OF DApplicationInd(25)]
    have "x' \<in> heapVars \<Theta>" by auto
    thus ?thesis..
  next
  case False
    hence "atom x' \<sharp> (n, e) # (x, App (Var n) y) # \<Gamma>"
      using DApplicationInd by (auto simp add: fresh_Pair fresh_Cons)
    from DApplicationInd.hyps(24)[OF this]
    show ?thesis
    proof
      assume "atom x' \<sharp> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>"
      with `atom n \<sharp> x'` `x' \<noteq> z`
      have "atom x' \<sharp> (z, Var y) # (x, e') # \<Delta>"
        by (simp add: fresh_Cons fresh_Pair subst_pres_fresh fresh_at_base)
      from DApplicationInd.hyps(26)[OF this]
      show ?thesis.
    next
      assume "x' \<in> heapVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>)"
      with `atom n \<sharp> x'`
      have "x' \<in> heapVars ((z,Var y) # (x, e') # \<Delta>)" by (simp add: fresh_at_base)
      with reds_doesnt_forget'[OF DApplicationInd(25)]
      have "x' \<in> heapVars \<Theta>" by auto
      thus ?thesis..
    qed
  qed
next
case (DVariable y x S \<Gamma> \<Delta> i x')
  thus ?case by auto
next 
case (DVariableNoUpd y x S e \<Gamma> z \<Delta> i x')
  thus ?case by (auto simp add: fresh_Cons)
next
case (DLet as \<Gamma> x body \<Delta> S i u x')
  show ?case
  proof(cases "x' \<in> heapVars (asToHeap as)")
    case True
    with reds_doesnt_forget'[OF DLet(8)]
    show ?thesis by auto
  next
    case False
    hence "atom x' \<notin> set (bn as)" sorry
    with `atom x' \<sharp> (x, Let as body) # \<Gamma>`
    have "atom x' \<sharp> (x, body) # asToHeap as @ \<Gamma>"
      by (auto simp add: fresh_Cons fresh_Pair fresh_append fresh_fun_eqvt_app asToHeap_eqvt)
    from DLet(9)[OF this]
    show ?thesis.
  qed
next 
case (DPermute \<Gamma> \<Gamma>' \<Delta> \<Delta>' S i u x)
  thus ?case by (auto simp add: fresh_def perm_supp perm_heapVars)
qed

end

