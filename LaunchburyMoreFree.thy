theory LaunchburyMoreFree
imports Terms Heap Launchbury
begin

inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>*\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down>*\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    atom (n::var) \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    n \<noteq> y;
    \<Gamma> : e \<Down>*\<^bsub>n#x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>*\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>*\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>; removeAll (x, e) \<Gamma> : e \<Down>*\<^bsub>x#L\<^esub> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down>*\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | Let: "set (bn as) \<sharp>* (\<Gamma>, Let as body, L) \<Longrightarrow> distinctVars (asToHeap as) \<Longrightarrow> asToHeap as @ \<Gamma> : body \<Down>*\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : Let as body \<Down>*\<^bsub>L\<^esub> \<Delta> : z"

equivariance reds

nominal_inductive reds
  avoids Application: "y" and "n"
    by(auto simp add: fresh_star_def fresh_Pair exp_assn.fresh)

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
proof(induct rule: reds.induct)
case(Variable v e \<Gamma> L \<Delta> z)
  show ?case
  proof
    fix x
    assume "x \<in> heapVars \<Gamma>"
    show "x \<in> heapVars ((v, z) # \<Delta>)"
    proof(cases "x = v")
    case True 
      thus ?thesis by simp
    next
    case False
      with `x \<in> heapVars \<Gamma>`
      have "x \<in> heapVars (removeAll (v,e) \<Gamma>)" by (auto simp add: heapVars_def)
      hence "x \<in> heapVars \<Delta>" using Variable.hyps(3) by auto
      thus ?thesis by simp
    qed
  qed
qed (auto)


lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (heapVars \<Delta> - set L)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z n e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta> - set (n # x' # L)" by (auto simp add: exp_assn.fresh fresh_Pair)

  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    show ?thesis
    proof(cases "x = y")
    case False
      hence "atom x \<sharp> e'" using `atom x \<sharp> (\<Delta>, Lam [y]. e')`
        by (auto simp add:fresh_Pair exp_assn.fresh)
      hence "atom x \<sharp> e'[y ::= x']" using Application.prems
        by (auto intro: subst_pres_fresh[rule_format] simp add: fresh_Pair exp_assn.fresh)
      thus ?thesis using Application.hyps(7) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair exp_assn.fresh)
      thus ?thesis using Application.hyps(7) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    qed
  next
    assume "x \<in> heapVars \<Delta>  - set (n # x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(6)] by auto
  qed
next

case(Variable v e \<Gamma> L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> removeAll (v,e) \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_remove dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta> - set (v # L)"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
  thus ?case using `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Let as \<Gamma> body L \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair exp_assn.fresh)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap_induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair exp_assn.fresh)
      show ?thesis
        apply(rule Let.hyps(4))
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair exp_assn.fresh fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap_induct)(auto simp add: exp_assn.bn_defs)      
      moreover
      have "x \<notin> set L"
        using Let(1)
        by (metis True fresh_list_elem fresh_star_Pair fresh_star_def not_self_fresh)
      ultimately
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(3)] by auto
    qed
qed

lemma reds_add_var_L: "\<lbrakk> \<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e, \<Delta>, z);
   set L' = insert x (set L)
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>*\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
print_cases
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule reds.Lambda)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z n e' L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)
  
    show "atom n \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)

    show "n \<noteq> y" by fact

    have "x \<notin> heapVars \<Theta>"
      using `atom x \<sharp> (\<Gamma>, App e xa, \<Theta>, z)`
      apply (simp add: fresh_Pair)
      by (metis heapVars_not_fresh)
    hence "x \<notin> heapVars \<Delta>"
      by (metis set_mp reds_doesnt_forget[OF Application.hyps(20)])

    have "atom x \<sharp> (\<Gamma>, e)"
      using `atom x \<sharp> (\<Gamma>, App e xa, \<Theta>, z)`
      by (simp add: fresh_Pair exp_assn.fresh)
    from reds_fresh[OF Application.hyps(18) this] `x \<notin> heapVars \<Delta>`
    have "atom x \<sharp> (\<Delta>, Lam [y]. e')"
      by auto
    hence "atom x \<sharp> (\<Gamma>, e, \<Delta>, Lam [y]. e')"
      using `atom x \<sharp> (\<Gamma>, App e xa, \<Theta>, z)`
      by (simp add: fresh_Pair exp_assn.fresh)
    moreover
    have "set (n # xa # L') = insert x (set (n # xa # L))"
      using `set L' = _` by auto
    ultimately
    show "\<Gamma> : e \<Down>*\<^bsub>n # xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(19))

    have "atom x \<sharp> (\<Delta>, e'[y::=xa])"
      using `atom x \<sharp> (\<Delta>, Lam [y]. e')` `atom x \<sharp> (\<Gamma>, App e xa, \<Theta>, z)` `atom y \<sharp> xa`
      apply (auto simp add: fresh_Pair exp_assn.fresh)
      apply (rule subst_pres_fresh[rule_format])
      apply simp
      done
    from reds_fresh[OF Application.hyps(20) this] `x \<notin> heapVars \<Theta>`
    have "atom x \<sharp> (\<Theta>, z)" by auto
    hence "atom x \<sharp> (\<Delta>, e'[y::=xa], \<Theta>, z)"
      using `atom x \<sharp> (\<Delta>, e'[y::=xa])`
      by (simp add: fresh_Pair)
    then
    show "\<Delta> : e'[y::=xa] \<Down>*\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(21)[OF _ `set L' = _`])
  qed
next 
case (Variable xa e \<Gamma> L \<Delta> z L')
  have "atom x \<sharp> (removeAll (xa, e) \<Gamma>, e, \<Delta>, z)"
    using Variable.prems(1)
    by (auto simp add: fresh_Pair fresh_Cons intro: removeAll_stays_fresh fresh_heap_expr[OF _ Variable(1)])
  moreover
  have "set (xa # L') = insert x (set (xa # L))"
    using Variable.prems(2) by auto
  ultimately
  show ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (Let as \<Gamma> body L \<Delta> z L')
  have "x \<notin> heapVars \<Delta>"
    using Let.prems(1)
    apply (auto simp add: fresh_Pair)
    by (metis heapVars_not_fresh)
  hence "x \<notin> heapVars (asToHeap as @ \<Gamma>)"
      by (metis set_mp reds_doesnt_forget[OF Let.hyps(5)])
  hence "atom x \<notin> set (bn as)"
    by (auto simp add: set_bn_to_atom_heapVars)
  hence "set (bn as) \<sharp>* x"
    by (auto simp add: fresh_star_def heapVars_def image_Un fresh_at_base )
    
  hence "set (bn as) \<sharp>* set L'"
    using Let(3) Let.prems(2)
    by (auto simp add: fresh_star_def fresh_finite_insert fresh_set)
  hence "set (bn as) \<sharp>* (\<Gamma>, Terms.Let as body, L')" 
    using Let(1-4)
    by (simp add: fresh_star_Pair fresh_star_set )
  moreover
  have "atom x \<sharp> (asToHeap as @ \<Gamma>, body, \<Delta>, z)"
    using Let.prems(1) `atom x \<notin> set (bn as)`
    by (auto simp add: fresh_Pair fresh_append exp_assn.fresh fresh_fun_eqvt_app[OF asToHeap_eqvt])
  ultimately
  show ?case
    by (rule reds.Let[OF _ Let.hyps(4) Let.hyps(6)[OF _ Let.prems(2)]])
qed

lemma reds_more_free:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z"
proof(nominal_induct rule: Launchbury.reds.strong_induct)
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  obtain n :: var where
    fresh: "atom n \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z, y, Lam [y]. e')" 
    by (rule obtain_fresh)

  show ?case
  proof (rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)
    show "atom n \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z)"
      using fresh
      by (auto simp add: fresh_Pair)
   show "n \<noteq> y"
      using fresh
      by (auto simp add: fresh_Pair fresh_at_base)

    note `\<Gamma> : e \<Down>*\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. e'`
    moreover
    have "atom n \<sharp> (\<Gamma>, e, \<Delta>, Lam [y]. e')"
      using fresh by (auto simp add: fresh_Pair)
    ultimately
    show "\<Gamma> : e \<Down>*\<^bsub>n # x # L\<^esub> \<Delta> : Lam [y]. e'"
      by (rule reds_add_var_L, simp)

    show "\<Delta> : e'[y::=x] \<Down>*\<^bsub>L\<^esub> \<Theta> : z"
      by fact
  qed
qed (auto intro: reds.intros simp add: fresh_star_Pair)

lemma reds_less_free:
  "\<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
proof(induct rule: LaunchburyMoreFree.reds.induct)
case (Application y \<Gamma> e x L \<Delta> \<Theta> z n e')
  show ?case
  proof(rule Launchbury.reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z)"
      by fact
    show  "\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. e'"
      apply (rule reds_smaller_L[OF Application.hyps(5)])
      by auto
    show "\<Delta> : e'[y::=x] \<Down>\<^bsub>L\<^esub> \<Theta> : z"
      by fact
  qed
qed (auto intro: reds_smaller_L Launchbury.reds.intros simp add: fresh_star_Pair)

lemma reds_more_free_eq:
  "(\<Gamma> : e \<Down>*\<^bsub>L\<^esub> \<Delta> : z) \<longleftrightarrow> (\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z)"
  by (metis reds_less_free reds_more_free)

lemmas reds_with_n_strong_induct = LaunchburyMoreFree.reds.strong_induct[unfolded reds_more_free_eq, consumes 1, case_names Lambda Application Variable Let]
lemmas reds_with_n_induct = LaunchburyMoreFree.reds.induct[unfolded reds_more_free_eq, consumes 1, case_names Lambda Application Variable Let]

end
