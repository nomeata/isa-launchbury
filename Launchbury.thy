theory Launchbury
imports Terms Heap
begin

lemma fresh_remove:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (removeAll e \<Gamma>)"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_list_elem:
  assumes "atom x \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "atom x \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)


lemma
 subst_pres_fresh: "(atom x \<sharp> e \<and> atom x \<sharp> z) --> atom x \<sharp> e[y ::= z]"
and
 "(atom x \<sharp> as \<and> atom x \<sharp> z \<and> atom x \<notin> set (bn as)) --> (atom x \<sharp> (subst_assn as y z))"
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:exp_assn.fresh fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)


inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk> atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ; \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e') ; \<Delta> : e'[y ::= x] \<Down>\<^bsub>L\<^esub> \<Theta> : z\<rbrakk> \<Longrightarrow> \<Gamma> : App e x \<Down>\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk> (x,e) \<in> set \<Gamma>; removeAll (x, e) \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | Let: "set (bn as) \<sharp>* L \<Longrightarrow> asToHeap as @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : Let as body \<Down>\<^bsub>L\<^esub> \<Delta> : z"

equivariance reds

nominal_inductive reds
(*
  avoids LetACons: "v"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh exp_assn.bn_defs)
done
*)
  avoids Application: "y"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh)
done

lemma eval_test:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
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
      have "x \<in> heapVars (removeAll (v,e) \<Gamma>)" by (auto simp add: heapVars_def)
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
case (Variable  x e \<Gamma> L \<Delta> z) thus ?case by (auto simp add: heapVars_def, metis fst_conv imageI)
next
case (Let as L \<Gamma> body \<Delta> z)
  print_facts
  have "x \<notin> heapVars \<Gamma>" by fact moreover
  have "x \<notin> heapVars (asToHeap as)"
    using `set (bn as) \<sharp>* L` and `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by (auto simp del:fst_set_asToHeap)  
  thus ?case
    by (rule Let.hyps(3)[OF `x \<in> set L`])
qed


lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta>"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta>" by (auto simp add: exp_assn.fresh fresh_Pair)

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
    assume "x \<in> heapVars \<Delta>"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4)] by auto
  qed
next

case(Variable v e \<Gamma> L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> removeAll (v,e) \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_remove dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta>"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
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
        apply(rule Let.hyps(3))
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair exp_assn.fresh fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap_induct)(auto simp add: exp_assn.bn_defs)      
      thus ?thesis using reds_doesnt_forget[OF Let.hyps(2)] by auto
    qed
qed

end

