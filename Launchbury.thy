theory Launchbury
imports Terms Heap
begin

inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>; delete x \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | Let: "set (bn as) \<sharp>* (\<Gamma>, Let as body, L) \<Longrightarrow> distinctVars (asToHeap as) \<Longrightarrow> asToHeap as @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : Let as body \<Down>\<^bsub>L\<^esub> \<Delta> : z"

equivariance reds

nominal_inductive reds
  avoids Application: "y"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh)
done

lemma eval_test:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>[] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by (auto intro!: Lambda Application Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def)

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
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
      have "x \<in> heapVars (delete v \<Gamma>)" by simp
      hence "x \<in> heapVars \<Delta>" using Variable.hyps(3) by auto
      thus ?thesis by simp
    qed
  qed
qed (auto)

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> heapVars \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> heapVars \<Delta>"
proof(induct rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e') thus ?case by auto
next
case (Variable  x e \<Gamma> L \<Delta> z) thus ?case
   by (auto simp add: heapVars_def, metis fst_conv imageI)
next
case (Let as \<Gamma> body L \<Delta> z)
  have "x \<notin> heapVars \<Gamma>" by fact moreover
  have "set (bn as) \<sharp>* L" using `set (bn as) \<sharp>* (\<Gamma>, Let as body, L)` by (simp add: fresh_star_Pair)
  hence "x \<notin> heapVars (asToHeap as)"
    using `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by (auto simp del:fst_set_asToHeap)  
  thus ?case
    by (rule Let.hyps(4)[OF `x \<in> set L`])
qed

lemma reds_pres_distinctVars:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta>"
proof (nominal_induct rule: reds.strong_induct)
  case (Variable x e \<Gamma> L \<Delta> z)
    have "x \<notin> heapVars \<Delta>"
      apply (rule reds_avoids_live[OF Variable(2)])
      apply (auto)
      done
    moreover
    have "distinctVars (delete x \<Gamma>)"
      by (rule distinctVars_delete[OF Variable(4)])
    hence "distinctVars \<Delta>" by (rule Variable.hyps)
    ultimately
    show ?case
      by (rule distinctVars.intros)
qed (auto intro: distinctVars_append_asToHeap)


lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (heapVars \<Delta> - set L)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta> - set (x' # L)" by (auto simp add: exp_assn.fresh fresh_Pair)

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
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair exp_assn.fresh)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    qed
  next
    assume "x \<in> heapVars \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4)] by auto
  qed
next

case(Variable v e \<Gamma> L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> delete v \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_delete dest:fresh_list_elem)
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

lemma reds_smaller_L: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   set L' \<subseteq> set L
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule reds.Lambda)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z e' L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)
  
    have "set (xa # L') \<subseteq> set (xa # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^bsub>xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(10))

    show "\<Delta> : e'[y::=xa] \<Down>\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(12)[OF Application.prems])
  qed
next 
case (Variable xa e \<Gamma> L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (Let as \<Gamma> body L \<Delta> z L')
  have "set (bn as) \<sharp>* (\<Gamma>, Terms.Let as body, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _ Let.hyps(4) Let.hyps(6)[OF Let.prems]])
qed


end

