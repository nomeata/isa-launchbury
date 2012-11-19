theory LaunchburyStacked
imports Terms Heap
begin

inductive reds :: "heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" ("_ : _ \<Down> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (x, (Lam [y]. e)) # \<Gamma>' \<Down> \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>'" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',x,e,y,\<Theta>,\<Theta>');
      atom z \<sharp> (\<Gamma>,\<Gamma>',x,e,y,\<Theta>,\<Theta>');
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down> \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      \<Delta> : (x, e'[z ::= y]) # \<Delta>' \<Down> \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down> \<Theta> : \<Theta>'" 
 | Variable: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      removeAll (y, e) \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down> \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down> (y, z) # \<Delta> : (x, z) # \<Delta>'"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, Let as body, \<Gamma>');
      distinctVars (asToHeap as);
      asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down> \<Delta> : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Let as body) # \<Gamma>' \<Down> \<Delta> : \<Delta>'"

equivariance reds

nominal_inductive reds
(*
  avoids LetACons: "v"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh exp_assn.bn_defs)
done
*)
  avoids Application: "n" and "z"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair exp_assn.fresh)
  done

(*
inductive reds_tree_invariant :: "(heap \<Rightarrow> heap \<Rightarrow> bool) \<Rightarrow> bool"
where
  "(\<And> \<Gamma> \<Delta> x e y \<Gamma>' n z e' \<Delta>'.  atom n \<sharp> (\<Gamma>,\<Gamma>',x,e,y) \<Longrightarrow> atom z \<sharp> (\<Gamma>,\<Gamma>',x,e,y) \<Longrightarrow>   P \<Gamma> ((x, App e y) # \<Gamma>')  \<Longrightarrow> P \<Delta> ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>')) \<Longrightarrow>
  (\<And> \<Delta> n z e' x y \<Delta>'.  atom n \<sharp> (x,y) \<Longrightarrow>  atom z \<sharp> (x,y) \<Longrightarrow>  P \<Delta> ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') \<Longrightarrow> P \<Delta> ((x, e'[z ::= y]) # \<Delta>')) \<Longrightarrow>
  (\<And> \<Gamma> x y \<Gamma>' e. (y, e) \<in> set \<Gamma> \<Longrightarrow> P \<Gamma> ((x, Var y) # \<Gamma>') \<Longrightarrow> P (removeAll (y, e) \<Gamma>) ((y, e) # (x,Var y) # \<Gamma>')) \<Longrightarrow>
  (\<And> \<Delta> x y \<Delta>' z. P \<Delta> ((y, z) # (x, Var y) # \<Delta>') \<Longrightarrow> P ((y, z) # \<Delta>)  ((x, z) # \<Delta>')) \<Longrightarrow>
  (\<And> \<Gamma> x as body \<Gamma>'. P \<Gamma> ((x, Let as body) # \<Gamma>') \<Longrightarrow> P (asToHeap as @ \<Gamma>) ((x, body) # \<Gamma>')) \<Longrightarrow>
  reds_tree_invariant P"

lemma reds_tree_invariant_preserved:
  assumes "reds_tree_invariant P"
  shows "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>' \<Longrightarrow> P \<Gamma> \<Gamma>' \<Longrightarrow> P \<Delta> \<Delta>'"
apply (induct \<Gamma> \<Gamma>' \<Delta> \<Delta>' rule: reds.induct)
apply assumption
by (metis assms reds_tree_invariant.cases fresh_Pair)+
*)

lemma eval_test:
  "y \<noteq> x \<Longrightarrow> [] : [(x, Let (ACons y (Lam [z]. Var z) ANil) (Var y))] \<Down> [(y, Lam [z]. Var z)] : [(x, (Lam [z]. Var z))]"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh fresh_star_def exp_assn.bn_defs fresh_at_base)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> z \<noteq> x \<Longrightarrow> [] : [(x,  Let (ACons y (Lam [z]. Var z) ANil) (App (Var y) y))] \<Down> [(y, Lam [z]. Var z)] : [(x, (Lam [z]. Var z))]"
  apply (rule Let)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base  fresh_Nil exp_assn.fresh fresh_star_def exp_assn.bn_defs)
  apply simp
  apply (rule obtain_fresh)
  apply (erule Application[where z = z])
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base fresh_Nil exp_assn.fresh fresh_star_def)
  apply (rule Variable, simp)
  apply (rule Lambda)
  apply simp
  apply (rule Variable, simp)
  apply simp
  apply (rule Lambda)
  done


inductive distinct_reds :: "heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" ("_ : _ \<Down>d _ : _" [50,50,50,50] 50)
where
  DLambda: "\<lbrakk>
      distinctVars ((x, (Lam [y]. e)) # \<Gamma>' @ \<Gamma>)
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>' \<Down>d \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>'" 
 | DApplication: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',x,e,y,\<Theta>,\<Theta>');
      atom z \<sharp> (\<Gamma>,\<Gamma>',x,e,y,\<Theta>,\<Theta>');
      distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, e'[z ::= y]) # \<Delta>') @ \<Delta>);
      distinctVars (\<Theta>' @ \<Theta>);
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down>d \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      \<Delta> : (x, e'[z ::= y]) # \<Delta>' \<Down>d \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down>d \<Theta> : \<Theta>'" 
 | DVariable: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((y, e) # (x,Var y) # \<Gamma>') @ removeAll (y, e) \<Gamma>);
      distinctVars (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>);
      removeAll (y, e) \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down>d \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down>d (y, z) # \<Delta> : (x, z) # \<Delta>'"
 | DLet: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, Let as body, \<Gamma>');
      distinctVars (asToHeap as);
      distinctVars (((x, Let as body) # \<Gamma>') @ \<Gamma>);
      distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>);
      distinctVars (\<Delta>' @ \<Delta>);
      asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down>d \<Delta> : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Let as body) # \<Gamma>' \<Down>d \<Delta> : \<Delta>'"

equivariance distinct_reds

nominal_inductive distinct_reds
(*
  avoids LetACons: "v"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh exp_assn.bn_defs)
done
*)
  avoids DApplication: "n" and "z"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair exp_assn.fresh)
  done

lemma distinct_redsD1:
  "\<Gamma> : \<Gamma>' \<Down>d \<Delta> : \<Delta>' \<Longrightarrow> \<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto intro!:reds.intros simp add: fresh_star_Pair)
  done

lemma distinct_redsD2:
  "\<Gamma> : \<Gamma>' \<Down>d \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>)"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto)
  done

lemma distinct_redsD3:
  "\<Gamma> : \<Gamma>' \<Down>d \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Delta>'@\<Delta>)"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto)
  done


lemma distinct_redsI:
  "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>) \<Longrightarrow> \<Gamma> : \<Gamma>' \<Down>d \<Delta> : \<Delta>'"
proof (nominal_induct rule: reds.strong_induct)
case Lambda thus ?case by (auto intro: distinct_reds.intros)
next
case (Application n \<Gamma> \<Gamma>' x e y \<Theta> \<Theta>' z \<Delta> e' \<Delta>')
  have "atom n \<sharp> (\<Gamma>, \<Gamma>', x, e, y, \<Theta>, \<Theta>')"
    using Application by simp
  moreover
  have "atom z \<sharp> (\<Gamma>, \<Gamma>', x, e, y, \<Theta>, \<Theta>')"
    using Application by simp
  moreover  
  assume "distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "atom n \<sharp> (((x, App e y) # \<Gamma>') @ \<Gamma>)"
    using Application
    by (simp add: fresh_Cons fresh_Pair fresh_append exp_assn.fresh)
  hence "n \<notin> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>)" 
    by (metis heapVars_not_fresh)
  with `distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp1 = Application.hyps(16)[OF this]
  note distinct_redsD3[OF hyp1]
  moreover
  hence "distinctVars (((x, e'[z::=y]) # \<Delta>') @ \<Delta>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp2 = Application.hyps(18)[OF this]
  note distinct_redsD3[OF hyp2]
  moreover  
  note hyp1
  moreover
  note hyp2
  ultimately
  show ?case
    by (rule DApplication[where n = n and z = z])
next

case (Variable y e \<Gamma> x \<Gamma>' \<Delta> z \<Delta>')
  have [simp]:"heapVars (removeAll (y, e) \<Gamma>) = heapVars \<Gamma> - {y}"
    using Variable(1,4)
    by (metis append_Cons distinctVars_ConsD(2) distinctVars_appendD2 heapVars_removeAll[OF _ `(y, e) \<in> set \<Gamma>`])
  
  assume "(y, e) \<in> set \<Gamma>"
  moreover  
  assume "distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "y \<in> heapVars \<Gamma>"
    using Variable(1)
    by (metis member_remove removeAll_no_there remove_code(1))
    with Variable(1,4)
  have "distinctVars (((y, e) # (x, Var y) # \<Gamma>') @ removeAll (y, e) \<Gamma>)"
    by (auto simp add: distinctVars_append distinctVars_Cons intro: distinctVars_removeAll)
  moreover
  note hyp = Variable.hyps(3)[OF this]
  note distinct_redsD3[OF hyp]
  moreover
  hence "distinctVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>)"
    by (auto simp add: distinctVars_append distinctVars_Cons)
  moreover 
  note hyp
  ultimately
  show ?case
    by (rule DVariable)
next
case (Let as \<Gamma> x body \<Gamma>' \<Delta> \<Delta>')
  hence "set (bn as) \<sharp>* (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
    by (auto simp add: fresh_star_Pair fresh_star_list)
  hence "heapVars (asToHeap as) \<inter> heapVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>) = {}"
    by (rule fresh_assn_distinct)
  
  have "set (bn as) \<sharp>* (\<Gamma>, x, Terms.Let as body, \<Gamma>')"
    using Let by (simp add: fresh_star_Pair fresh_star_list)
  moreover
  assume "distinctVars (asToHeap as)"
  moreover
  assume "distinctVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
  moreover  
  hence "distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    using `distinctVars (asToHeap as)` `_ = {}`
    by (auto simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp = Let.hyps(7)[OF this]
  note distinct_redsD3[OF hyp]
  moreover  
  note hyp
  ultimately
  show ?case
    by (rule DLet)
qed

lemma reds_pres_distinctVars:
  "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>) \<Longrightarrow> distinctVars (\<Delta>'@\<Delta>)"
by (metis distinct_redsD3 distinct_redsI)

thm reds.induct
lemmas reds_distinct_ind = distinct_reds.induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]

lemma reds_doesnt_forget:
  "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>) \<Longrightarrow> heapVars (\<Gamma>' @ \<Gamma>) \<subseteq> heapVars (\<Delta>' @ \<Delta>)"
proof(induct rule: reds_distinct_ind)
case Lambda thus ?case by simp
next
case (Application n \<Gamma> \<Gamma>' x e y \<Theta> \<Theta>' z e' \<Delta>' \<Delta>)
  show ?case
  proof
    fix v
    assume "v \<in> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>)"
    hence "\<not>( atom v \<sharp> ((x, App e y) # \<Gamma>') @ \<Gamma>)"
      by (rule heapVars_not_fresh)
    hence "v \<noteq> n"
      by (metis Application(1) exp_assn.fresh(2) fresh_Cons fresh_Pair fresh_append)

    assume "v \<in> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>)"
    hence "v \<in> heapVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)" by simp
    hence "v \<in> heapVars (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>)"
      by (rule set_mp[OF Application(9)])
    hence "v \<in> heapVars (((x, e'[z::=y]) # \<Delta>') @ \<Delta>)"
      using `v \<noteq> n` by simp
    thus "v \<in> heapVars (\<Theta>' @ \<Theta>)" 
      by (rule set_mp[OF Application(11)])
  qed
next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have [simp]:"heapVars (removeAll (y, e) \<Gamma>) = heapVars \<Gamma> - {y}"
    by (rule heapVars_removeAll[OF distinctVars_appendD2[OF Variable(2)] Variable(1)])

  assume "(y, e) \<in> set \<Gamma>"
  hence "y \<in> heapVars \<Gamma>" by (metis member_remove removeAll_no_there remove_code(1))
  hence "heapVars (((x, Var y) # \<Gamma>') @ \<Gamma>) = heapVars (((y, e) # (x, Var y) # \<Gamma>') @ removeAll (y, e) \<Gamma>)"
    by auto
  also have "... \<subseteq> heapVars (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>)"
    by (rule Variable(7))
  also have "... =  heapVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>)"
    by auto
  finally
  show ?case.
next
case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  (* Begin copy *)
  hence "set (bn as) \<sharp>* (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
    by (auto simp add: fresh_star_Pair fresh_star_list)
  hence "heapVars (asToHeap as) \<inter> heapVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>) = {}"
    by (rule fresh_assn_distinct)
  moreover
  assume "distinctVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
  ultimately
  have prems1: "distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    using `distinctVars (asToHeap as)`
    by (auto simp add: distinctVars_append distinctVars_Cons)
  (* End copy *)

  have "heapVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>) \<subseteq> heapVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    by auto
  also
  have "... \<subseteq> heapVars (\<Delta>' @ \<Delta>)"
    by (rule Let.hyps(7))
  finally show ?case.
qed

(*
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
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> heapVars \<Gamma>" by fact moreover
  have "x \<notin> heapVars (asToHeap as)"
    using `set (bn as) \<sharp>* (\<Gamma>, L)` and `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by (auto simp del:fst_set_asToHeap)  
  thus ?case
    by (rule Let.hyps(4)[OF `x \<in> set L`])
qed
*)

lemma reds_fresh:" \<lbrakk> \<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>';
   atom (x::var) \<sharp> (\<Gamma>, \<Gamma>')
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, \<Delta>') \<or> x \<in> heapVars \<Delta>"
sorry
(*
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
        apply(rule Let.hyps(4))
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair exp_assn.fresh fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap_induct)(auto simp add: exp_assn.bn_defs)      
      thus ?thesis using reds_doesnt_forget[OF Let.hyps(3)] by auto
    qed
qed
*)

end

