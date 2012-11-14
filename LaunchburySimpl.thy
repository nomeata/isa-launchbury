theory LaunchburySimpl
imports Terms Heap
begin

inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^bsub>_;_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>L;S\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk> atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z,S) ; \<Gamma> : e \<Down>\<^bsub>x#L;S\<^esub> \<Delta> : (Lam [y]. e') ; \<Delta> : e'[y ::= x] \<Down>\<^bsub>L;S\<^esub> \<Theta> : z\<rbrakk> \<Longrightarrow> \<Gamma> : App e x \<Down>\<^bsub>L;S\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk> (x,e) \<in> set \<Gamma>; x \<notin> set S; \<Gamma> : e \<Down>\<^bsub>L;x#S\<^esub> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down>\<^bsub>L;S\<^esub> (x, z) # removeAll (x, e) \<Delta> : z"
 | Let: "set (bn as) \<sharp>* (\<Gamma>, L) \<Longrightarrow> distinctVars (asToHeap as) \<Longrightarrow> asToHeap as @ \<Gamma> : body \<Down>\<^bsub>L;S\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : Let as body \<Down>\<^bsub>L;S\<^esub> \<Delta> : z"

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

lemma VariableI: "\<lbrakk> (x,e) \<in> set \<Gamma>; x \<notin> set S; \<Gamma> : e \<Down>\<^bsub>L;x#S\<^esub> \<Delta> : z; \<Delta>' = (x, z) # removeAll (x, e) \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down>\<^bsub>L;S\<^esub> \<Delta>' : z"
 by (metis Variable)


lemma eval_test:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[];[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application VariableI Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[];[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
by (auto intro!: Lambda Application VariableI Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def)

lemma blackholed_untouched:
  "\<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z \<Longrightarrow> x \<in> set S \<Longrightarrow> (x, e') \<in> set \<Gamma> \<Longrightarrow> (x, e') \<in> set \<Delta>"
by(induct rule: reds.induct, auto)

lemma distinctVars_append_asToHeap:
  assumes "distinctVars (asToHeap as)"
  assumes "distinctVars \<Gamma>"
  assumes "set (bn as) \<sharp>* \<Gamma>"
  shows "distinctVars (asToHeap as @ \<Gamma>)" 
proof(rule distinctVars_append[OF assms(1,2)])
  { fix x
    assume "x \<in> heapVars (asToHeap as)"
    hence "atom x \<in> set (bn as)"
      apply (induct as rule: asToHeap.induct)
      apply (auto simp add: exp_assn.bn_defs(2))
      done
    hence "atom x \<sharp> \<Gamma>"
      using `set (bn as) \<sharp>* \<Gamma>` by (auto simp add: fresh_star_def)
    moreover
    assume "x \<in> heapVars \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      apply (induct \<Gamma>)
      by (auto simp add: supp_Cons heapVars_def supp_Pair supp_at_base)
    ultimately
    have False
      by (simp add: fresh_def)
  }
  thus "heapVars (asToHeap as) \<inter> heapVars \<Gamma> = {}" by auto
qed  

lemma reds_pres_distinctVars:
  "\<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta>"
proof (nominal_induct rule: reds.strong_induct)
  case (Variable x e \<Gamma> S L \<Delta> z)
    have "(x, e) \<in> set \<Delta>"
      apply (rule blackholed_untouched[OF Variable(3) _ Variable(1)])
      by simp
    show ?case
      apply (rule distinctVars.intros)
      apply (simp add: heapVars_removeAll[OF Variable.hyps(4)[OF Variable.prems] `(x, e) \<in> set \<Delta>`])
      apply (rule distinctVars_removeAll[OF Variable.hyps(4)[OF Variable.prems] `(x, e) \<in> set \<Delta>`])
      done
qed (auto intro: distinctVars_append_asToHeap)

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
  apply(induct rule: reds.induct)
  apply (auto intro: reds_pres_distinctVars distinctVars_append_asToHeap simp add: fresh_star_Pair)
  apply (subst (asm) heapVars_removeAll)
  apply (erule (1) reds_pres_distinctVars)
  apply (erule blackholed_untouched, simp_all)[1]
  apply auto[1]
  done

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z;
   distinctVars \<Gamma>;
   x \<in> set L;
   x \<notin> heapVars \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> heapVars \<Delta>"
proof(induct rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e') thus ?case by (auto intro: reds_pres_distinctVars)
next
case (Variable x e \<Gamma> S L \<Delta> z) thus ?case by (auto  simp add: heapVars_def image_iff)
next
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> heapVars \<Gamma>" by fact
  moreover
  have "x \<notin> heapVars (asToHeap as)"
    using `set (bn as) \<sharp>* (\<Gamma>, L)` and `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)
  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by (auto simp del:fst_set_asToHeap)  
  moreover  
  have "distinctVars (asToHeap as @ \<Gamma>)"
    using Let
    by (auto intro: distinctVars_append_asToHeap simp add: fresh_star_Pair)
  ultimately
  show ?case
    by (metis Let.hyps(4)[OF _ `x \<in> set L`])
qed

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L;S\<^esub> \<Delta> : z;
   distinctVars \<Gamma>;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta>"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e L S) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z S e')
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
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` reds_pres_distinctVars[OF Application(2) Application(6)] by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair exp_assn.fresh)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` reds_pres_distinctVars[OF Application(2) Application(6)] by auto
    qed
  next
    assume "x \<in> heapVars \<Delta>"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4) reds_pres_distinctVars[OF Application(2) Application(6)]] by auto
  qed
next

case(Variable v e \<Gamma> S L \<Delta> z)  
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(2) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by (auto intro: fresh_remove dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta>"  using Variable.hyps(4) Variable.prems(1) by (auto simp add: fresh_Pair)
  moreover  
  have "(v, e) \<in> set \<Delta>" by (rule blackholed_untouched[OF Variable.hyps(3) _ Variable.hyps(1), simplified])
  hence "v \<in> heapVars \<Delta>" apply (auto simp add: heapVars_def) by (metis fst_conv imageI)
  hence "heapVars ((v, z) # removeAll (v, e) \<Delta>) = heapVars \<Delta>"
     by (auto simp add:  heapVars_removeAll[OF reds_pres_distinctVars[OF Variable.hyps(3) Variable.prems(1)] `(v, e) \<in> set \<Delta>`])
  ultimately
  show ?case using `atom x \<sharp> v`
    apply -
    apply (erule ssubst)
    apply (auto simp add: fresh_Pair fresh_Cons fresh_at_base removeAll_stays_fresh)
    done
next

case (Let as \<Gamma> L body S \<Delta> z)
  have "distinctVars (asToHeap as @ \<Gamma>)" using Let by (auto intro: distinctVars_append_asToHeap simp add: fresh_star_Pair)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      thm Let.hyps(3)
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair exp_assn.fresh)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap_induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair exp_assn.fresh)
      show ?thesis
        apply(rule Let.hyps(4)[OF `distinctVars (asToHeap as @ \<Gamma>)`])
        using Let `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair exp_assn.fresh fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap_induct)(auto simp add: exp_assn.bn_defs)      
      thus ?thesis using reds_doesnt_forget[OF Let.hyps(3) `distinctVars (asToHeap as @ \<Gamma>)`] by auto
    qed
qed

end

