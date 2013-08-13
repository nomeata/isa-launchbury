theory LaunchburyAddBH
imports LaunchburyCombinedTaggedMap
begin                     

nominal_primrec varOf :: "exp \<Rightarrow> var option" where
  "varOf (Var x) = Some x" |
  "varOf (Lam [_]. _) = None" |
  "varOf (App e x) = None" |
  "varOf (Let as body) = None"
  unfolding eqvt_def varOf_graph_aux_def
  apply (rule)
  apply simp_all
  apply (metis exp_assn.exhaust(1))
  done
termination (eqvt) by lexicographic_order

nominal_primrec dep :: "exp \<Rightarrow> var option" where
  "dep (Var x) = Some x" |
  "dep (App e y) = varOf e" |
  "dep (Lam [_]. _) = None" |
  "dep (Let as body) = None"
  unfolding eqvt_def dep_graph_aux_def
  apply (rule)
  apply simp_all
  apply (metis exp_assn.exhaust(1))
  done
termination (eqvt) by lexicographic_order

lemma isLam_dep[simp]: "isLam e \<Longrightarrow> dep e = None"
  by (cases e rule: exp_assn.exhaust(1)) auto

fun depRel :: "Heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool" where
  "depRel \<Gamma> x y \<longleftrightarrow> Option.bind (lookup \<Gamma> x) dep = Some y"

lemma depRel_cong':
  "lookup \<Delta> a = lookup \<Gamma> a \<Longrightarrow> depRel \<Gamma> a b \<Longrightarrow> depRel \<Delta> a b"
  by auto

lemma depRel_cong:
  "lookup \<Gamma> a = lookup \<Delta> a \<Longrightarrow> depRel \<Gamma> a b = depRel \<Delta> a b"
  by auto

lemma depRel_fmap_upd[simp]: "depRel (\<Gamma>(x f\<mapsto>  e)) x y \<longleftrightarrow> dep e = Some y"
  by auto

lemma depRel_fmap_upd_Not[simp]: "a \<noteq> x \<Longrightarrow> depRel (\<Gamma>(x f\<mapsto> e)) a b \<longleftrightarrow> depRel \<Gamma> a b"
  by simp

lemma depRel_dom: "depRel \<Gamma> y x \<Longrightarrow> y \<in> fdom \<Gamma>"
  by (metis depRel.simps bind_lzero fdomIff option.distinct(1))

lemma depRelTransDom:
  "(depRel \<Gamma>)\<^sup>+\<^sup>+ a b \<Longrightarrow> a \<in> fdom \<Gamma>"
  by (metis (full_types) depRel_dom tranclpD)

lemma depRel_fmap_upd_trans[simp]: "lookup \<Gamma> x = Some e \<Longrightarrow> dep e = None \<Longrightarrow> (depRel \<Gamma>)\<^sup>+\<^sup>+ x y \<longleftrightarrow> False"
  by (auto elim: tranclp_induct)

definition cycle where "cycle \<Gamma> x \<longleftrightarrow> (depRel \<Gamma>)\<^sup>+\<^sup>+ x x"

lemma lookup_eq_split: "lookup (f(a f\<mapsto> b)) x = Some r \<longleftrightarrow> ((x = a \<and> r = b) \<or> (x \<noteq> a \<and> lookup f x = Some r))"
  by transfer auto

lemma varOf_Some[dest!]: "varOf e = Some b \<Longrightarrow> e = Var b"
  by (cases e rule:exp_assn.exhaust(1)) auto

lemma depRelAppE:
  "depRel (\<Gamma>(x f\<mapsto> App e y)) a b \<Longrightarrow> x = a \<and> e = Var b \<or> x \<noteq> a \<and> depRel \<Gamma> a b"
  by (cases "x=a") auto

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

    have "(depRel (\<Gamma>(a f\<mapsto> App (Var n) y)(n f\<mapsto> Var b)))\<^sup>+\<^sup>+ a n" using `n \<noteq> a` by auto
    also
    have "(depRel (\<Gamma>(a f\<mapsto> App (Var n) y)(n f\<mapsto> Var b)))\<^sup>+\<^sup>+ n b" by auto
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


lemma cycle_depRel:
  assumes "cycle \<Gamma> x"
  assumes "depRel \<Gamma> x n"
  shows "cycle \<Gamma> n"
by (metis assms depRel_via cycle_def tranclp.simps)

theorem
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta>"
  assumes "validStack \<Gamma> x S"
  shows "\<not> cycle \<Gamma> x" and  "validStack \<Delta> x S"
   and add_blackholing: "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
  (* The third conclusion does not need the others, but inductive proofs compose so badly. *)
using assms
proof(induction \<Gamma> i u b "x#S" \<Delta> arbitrary: x S rule:reds.induct )
case (Lambda \<Gamma> x y e i u b S)
  case 1 show ?case by (auto simp add: cycle_def)
  case 2 thus ?case .
  case 3 show ?case using Lambda by (rule reds.Lambda)
next
case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
  case 2
    from Application(1) have "n \<noteq> x"  "n \<notin> set S"
      by (simp_all add: fresh_Pair fresh_at_base fresh_at_base_list)
    hence "(depRel (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)))\<^sup>+\<^sup>+ x n" by auto
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
      from stack_unchanged[OF Application.hyps(7)[OF IH1]] `n \<noteq> x`
      have "lookup (\<Delta>(n f\<mapsto> Lam [z]. e')) x = Some (App (Var n) y)"  by auto
      hence "depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n" by auto

      fix x'
      assume "(depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x' x"
      moreover
      have "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ n x" by auto
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
    from Application.hyps(5)[OF IH1]
    show ?case
    proof(rule contrapos_nn)
      assume "cycle (\<Gamma>(x f\<mapsto> App e y)) x"
      hence "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x"
        by (rule cycleIndirect[OF _ `atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)`])
      thus "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n" using `n \<noteq> x`  by (auto elim!: cycle_depRel)
    qed
  case 3
    from Application.hyps(1,2,3)
         Application.hyps(7)[OF IH1]
         Application.hyps(11)[OF IH2]
    show ?case by (rule reds.Application)
next
case (ApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z u b e')
case 2
    from ApplicationInd(1) have "n \<noteq> x" by (simp add: fresh_Pair fresh_at_base)
    hence "(depRel (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)))\<^sup>+\<^sup>+ x n" by auto
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
      from stack_unchanged[OF ApplicationInd.hyps(7)[OF IH1]] `n \<noteq> x`
      have "depRel (\<Delta>(n f\<mapsto> Lam [z]. e')) x n" by auto

      fix x'
      assume as: "(depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ x' x"
      moreover
      have "\<not> (depRel (\<Delta>(n f\<mapsto> Lam [z]. e')))\<^sup>+\<^sup>+ n x" by auto
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
    from ApplicationInd.hyps(5)[OF IH1]
    show ?case
    proof(rule contrapos_nn)
      assume "cycle (\<Gamma>(x f\<mapsto> App e y)) x"
      hence "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) x"
        by (rule cycleIndirect[OF _ `atom n \<sharp> \<Gamma>(x f\<mapsto> App e y)`])
      thus "cycle (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) n" using `n \<noteq> x`
        by (auto elim!: cycle_depRel)
    qed
  case 3
    from ApplicationInd.hyps(1-3)
         ApplicationInd.hyps(7)[OF IH1]
         ApplicationInd.hyps(11)[OF IH2]
    show ?case by (rule reds.ApplicationInd)
next
case (Variable y x S \<Gamma> i \<Delta>)
  hence "y \<noteq> x" by simp

  have "(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y" by auto 
  moreover
  assume "validStack (\<Gamma>(x f\<mapsto> Var y)) x S"
  ultimately
  have "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S)"
    by (rule ValidStackCons)
  note hyps = Variable(4-6)[OF this]

  from stack_unchanged[OF hyps(3)] `y \<noteq> x`
  have "lookup \<Delta> x = Some (Var y)" by simp
  hence "depRel \<Delta> x y" by auto

  from result_evaluated[OF hyps(3)]
  have "isLam (\<Delta> f! y)" by simp
  hence "\<not> Domainp (depRel \<Delta>) y" apply auto by (metis bind_lunit bind_lzero isLam_dep not_None_eq the.simps)

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
    by (auto elim!: contrapos_nn cycle_depRel)

  from Variable(1-3) 
  show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> fmap_copy \<Delta> y x"
    by (rule reds.Variable)
next
case (VariableNoBH x \<Gamma> y i S \<Delta>)
  have "(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y" by auto 
  moreover
  assume "validStack (\<Gamma>(x f\<mapsto> Var y)) x S"
  ultimately
  have "validStack (\<Gamma>(x f\<mapsto> Var y)) y (x # S)"
    by (rule ValidStackCons)
  note hyps = VariableNoBH(3-5)[OF this]

  from hyps(1) `(depRel (\<Gamma>(x f\<mapsto> Var y)))\<^sup>+\<^sup>+ x y`
  have "y \<noteq> x" by (auto simp add: cycle_def)

  from stack_unchanged[OF hyps(3)] `y \<noteq> x`
  have "lookup \<Delta> x = Some (Var y)" by simp
  hence "depRel \<Delta> x y" by auto

  from result_evaluated[OF hyps(3)]
  have "isLam (\<Delta> f! y)" by simp
  hence "\<not> Domainp (depRel \<Delta>) y" apply auto by (metis bind_lunit bind_lzero isLam_dep not_None_eq the.simps)

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
    by (auto elim!: contrapos_nn cycle_depRel)

  from hyps(1) `validStack (\<Gamma>(x f\<mapsto> Var y)) y (x#S)`
  have "y \<notin> set (x # S)"
    by (metis validStack_cycle)

  from this VariableNoBH.hyps(1) hyps(3)
  show "\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x # S\<^esub> fmap_copy \<Delta> y x"
    by (rule reds.Variable)
next
case (Let as \<Gamma> x S body i u b \<Delta>)
  assume "validStack (\<Gamma>(x f\<mapsto> Terms.Let as body)) x S"

  hence "validStack (\<Gamma>(x f\<mapsto> body) f++ fmap_of (asToHeap as)) x S"
  proof (rule validStack_cong)
    fix x'
    assume as: "(depRel (\<Gamma>(x f\<mapsto> Terms.Let as body)))\<^sup>+\<^sup>+ x' x"
    hence "x' \<noteq> x" by auto
    with as have "x' \<in> fdom \<Gamma>"
      by (auto dest:depRelTransDom)
    with Let(1)
    have "atom x' \<notin> set (bn as)" by (auto simp add: fresh_star_def fresh_Pair)
    hence  "x' \<notin> fdom (fmap_of (asToHeap as))" 
      by (metis (full_types) fdom_fmap_of_conv_heapVars imageI set_bn_to_atom_heapVars)
    with `x' \<noteq> x`
    show "lookup (\<Gamma>(x f\<mapsto> Terms.Let as body)) x' =
        lookup (\<Gamma>(x f\<mapsto> body) f++ fmap_of (asToHeap as)) x'"
        by simp
  qed
  note hyps = Let(5-7)[OF this]

  case 1
  show ?case by (auto simp add: cycle_def)

  case 2
  from hyps(2)
  show ?case.

  case 3
  note Let(1-3) hyps(3)
  thus ?case..
qed

lemma remove_blackholing:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>S\<^esub> \<Delta>"
  shows "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta>"
using assms
apply (cases b, simp)
apply (induction \<Gamma> i u "\<surd>" S \<Delta> rule:reds.induct )
apply (blast intro:reds.intros)+
done

lemma second_stack_element_unchanged:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#y#S\<^esub> \<Delta>"
  assumes "x \<noteq> y"
  assumes "depRel \<Gamma> y x"
  shows "lookup \<Delta> y = lookup \<Gamma> y"
proof-
  from shorten_stack[OF assms(1), where n = 1]
  have "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>[x,y]\<^esub> \<Delta>" by simp
  moreover
  from assms(3)
  have "validStack \<Gamma> x [y]" by (fastforce intro: validStack.intros)
  ultimately
  have "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>[x,y]\<^esub> \<Delta>" by (rule add_blackholing)
  from stack_unchanged[OF this, where x = y] assms(2)
  show ?thesis by auto
qed


end

