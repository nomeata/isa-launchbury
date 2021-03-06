theory LaunchburyCombinedStacked
imports Terms Heap
begin

datatype Flag = FlagSet ("\<surd>") | FlagNotSet ("\<times>")

instantiation  Flag :: pure
begin
  definition "p \<bullet> (v::Flag) = v"
instance
  apply default
  apply (auto simp add: permute_Flag_def)
  done
end

inductive reds :: "heap \<Rightarrow> heap \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" ("_ : _/ \<Down>\<^sup>_\<^sup>_/ _ : _" [50,50,50,50,50,50] 50)
where
  Lambda:
    "\<Gamma> : (x, (Lam [y]. e)) # \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>'" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>',z);
      atom z \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>');
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down>\<^sup>\<times>\<^sup>u \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      \<Delta> : (x, e'[z ::= y]) # \<Delta>' \<Down>\<^sup>\<times>\<^sup>u \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down>\<^sup>\<times>\<^sup>u \<Theta> : \<Theta>'" 
 | ApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>',z);
      atom z \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y);
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      (z,Var y) # \<Delta> : (x, e') # \<Delta>' \<Down>\<^sup>\<surd>\<^sup>u \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u \<Theta> : \<Theta>'" 
 | Variable: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      delete y \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<surd> \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<surd> (y, z) # \<Delta> : (x, z) # \<Delta>'"
 | VariableNoUpd: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      delete y \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<times> \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<times> (y, e) # \<Delta> : (x, z) # \<Delta>'"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, \<Gamma>');
      distinctVars (asToHeap as);
      asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Let as body) # \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)

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

subsubsection {* Properties of the semantics *}

text {*
This is the same semantics with additional distinctiveness requirements. This is defined in order to
obtain a more convenient induction rule.
*}

inductive distinct_reds :: "heap \<Rightarrow> heap \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" ("_ : _/ \<Down>\<^sup>_\<^sup>_\<^sup>d/ _ : _" [50,50,50,50] 50)
where
  DLambda: "\<lbrakk>
      distinctVars ((x, (Lam [y]. e)) # \<Gamma>' @ \<Gamma>)
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Gamma> : (x, (Lam [y]. e)) # \<Gamma>'" 
 | DApplication: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>',z);
      atom z \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>');
      distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, e'[z ::= y]) # \<Delta>') @ \<Delta>);
      distinctVars (\<Theta>' @ \<Theta>);
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down>\<^sup>\<times>\<^sup>u\<^sup>d \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      \<Delta> : (x, e'[z ::= y]) # \<Delta>' \<Down>\<^sup>\<times>\<^sup>u\<^sup>d \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down>\<^sup>\<times>\<^sup>u\<^sup>d \<Theta> : \<Theta>'" 
 | DApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y,\<Theta>,\<Theta>',z);
      atom z \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,\<Delta>',x,e,y);
      distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, e') # \<Delta>') @ (z, Var y) # \<Delta>);
      distinctVars (\<Theta>' @ \<Theta>);
      \<Gamma> : (n, e) # (x, App (Var n) y) # \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>';
      (z, Var y) # \<Delta> : (x, e') # \<Delta>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Theta> : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, App e y) # \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Theta> : \<Theta>'" 
 | DVariable: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((y, e) # (x,Var y) # \<Gamma>') @ delete y \<Gamma>);
      distinctVars (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>);
      delete y \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<surd>\<^sup>d (y, z) # \<Delta> : (x, z) # \<Delta>'"
 | DVariableNoUpd: "\<lbrakk>
      (y, e) \<in> set \<Gamma>;
      distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>);
      distinctVars (((y, e) # (x,Var y) # \<Gamma>') @ delete y \<Gamma>);
      distinctVars (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>);
      distinctVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>);
      delete y \<Gamma> : (y, e) # (x,Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<times>\<^sup>d \<Delta> : (y, z) # (x, Var y) # \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Var y) # \<Gamma>' \<Down>\<^sup>i\<^sup>\<times>\<^sup>d (y, e) # \<Delta> : (x, z) # \<Delta>'"
 | DLet: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, \<Gamma>');
      distinctVars (asToHeap as);
      distinctVars (((x, Let as body) # \<Gamma>') @ \<Gamma>);
      distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>);
      distinctVars (\<Delta>' @ \<Delta>);
      asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : (x, Let as body) # \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>'"

equivariance distinct_reds

nominal_inductive distinct_reds
  avoids DApplication: "n" and "z"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)
  done

lemma distinct_redsD1:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> \<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto intro:reds.intros simp add: fresh_star_Pair fresh_Pair)
  done

lemma distinct_redsD2:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>)"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto)
  done

lemma distinct_redsD3:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Delta>'@\<Delta>)"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto simp add: distinctVars_Cons distinctVars_append)
  done


lemma distinct_redsI:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>) \<Longrightarrow> \<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>'"
proof (nominal_induct rule: reds.strong_induct)
case Lambda thus ?case by (auto intro: distinct_reds.intros)
next
case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z u e')
  have "atom n \<sharp> (\<Gamma>, \<Gamma>',\<Delta>,\<Delta>',x, e, y, \<Theta>, \<Theta>',z)"
    using Application by simp
  moreover
  have "atom z \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Delta>', x, e, y, \<Theta>, \<Theta>')"
    using Application by simp
  moreover  
  assume "distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "atom n \<sharp> (((x, App e y) # \<Gamma>') @ \<Gamma>)"
    using Application
    by (simp add: fresh_Cons fresh_Pair fresh_append)
  hence "n \<notin> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>)" 
    by (metis heapVars_not_fresh)
  with `distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp1 = Application.hyps(21)[OF this]
  note distinct_redsD3[OF hyp1]
  moreover
  hence "distinctVars (((x, e'[z::=y]) # \<Delta>') @ \<Delta>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp2 = Application.hyps(23)[OF this]
  note distinct_redsD3[OF hyp2]
  moreover  
  note hyp1
  moreover
  note hyp2
  ultimately
  show ?case
    by (rule DApplication[where n = n and z = z])
next
case (ApplicationInd n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z u e')
  have "atom n \<sharp> (\<Gamma>, \<Gamma>',\<Delta>,\<Delta>',x, e, y, \<Theta>, \<Theta>',z)"
    using ApplicationInd by simp
  moreover
  have "atom z \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Delta>', x, e, y)"
    using ApplicationInd by simp
  moreover  
  assume "distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "atom n \<sharp> (((x, App e y) # \<Gamma>') @ \<Gamma>)"
    using `atom n \<sharp> (\<Gamma>, \<Gamma>',\<Delta>,\<Delta>',x, e, y, \<Theta>, \<Theta>',z)`
    by (simp add: fresh_Cons fresh_Pair fresh_append)
  hence "n \<notin> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>)" 
    by (metis heapVars_not_fresh)
  with `distinctVars (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "distinctVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  moreover
  note hyp1 = ApplicationInd.hyps(19)[OF this]
  note distinct_redsD3[OF hyp1]
  moreover
  with `atom z \<sharp> x` `atom z \<sharp> \<Delta>`  `atom z \<sharp> \<Delta>'` 
  have "distinctVars (((x, e') # \<Delta>') @ (z, Var y) # \<Delta>)"
    apply (simp add: distinctVars_append distinctVars_Cons )
    by (metis  `atom z \<sharp> \<Delta>`  `atom z \<sharp> \<Delta>'` heapVars_not_fresh)
  moreover
  note hyp2 = ApplicationInd.hyps(21)[OF this]
  note distinct_redsD3[OF hyp2]
  moreover  
  note hyp1
  moreover
  note hyp2
  ultimately
  show ?case
    by (rule DApplicationInd[where n = n and z = z])
next

case (Variable y e \<Gamma> x \<Gamma>' i \<Delta> z \<Delta>')  
  assume "(y, e) \<in> set \<Gamma>"
  moreover  
  assume "distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "distinctVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)"
    using Variable(1,4)
    by (auto simp add: distinctVars_append distinctVars_Cons intro: distinctVars_delete heapVars_from_set)
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

case (VariableNoUpd y e \<Gamma> x \<Gamma>' i \<Delta> z \<Delta>')  
  assume "(y, e) \<in> set \<Gamma>"
  moreover  
  assume "distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>)"
  moreover
  have "distinctVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)"
    using VariableNoUpd(1,4)
    by (auto simp add: distinctVars_append distinctVars_Cons intro: distinctVars_delete heapVars_from_set)
  moreover
  note hyp = VariableNoUpd.hyps(3)[OF this]
  note distinct_redsD3[OF hyp]
  moreover
  hence "distinctVars (((x, z) # \<Delta>') @ (y, z) # \<Delta>)"
    by (auto simp add: distinctVars_append distinctVars_Cons)
  moreover 
  note hyp
  ultimately
  show ?case
    by (rule DVariableNoUpd)
next

case (Let as \<Gamma> x \<Gamma>' body \<Delta> \<Delta>')
  hence "set (bn as) \<sharp>* (((x, Let as body) # \<Gamma>') @ \<Gamma>)"
    by (auto simp add: fresh_star_Pair fresh_star_list)
  hence "heapVars (asToHeap as) \<inter> heapVars (((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>) = {}"
    by (rule fresh_assn_distinct)
  
  have "set (bn as) \<sharp>* (\<Gamma>, x, \<Gamma>')"
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
  note hyp = Let.hyps(6)[OF this]
  note distinct_redsD3[OF hyp]
  moreover  
  note hyp
  ultimately
  show ?case
    by (rule DLet)
qed

lemma reds_pres_distinctVars:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>'@\<Gamma>) \<Longrightarrow> distinctVars (\<Delta>'@\<Delta>)"
by (metis distinct_redsD3 distinct_redsI)

lemmas reds_distinct_ind = distinct_reds.induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]
lemmas reds_distinct_strong_ind = distinct_reds.strong_induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]

lemma reds_doesnt_forget':
  assumes "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>'"
  shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>" and "heapVars \<Gamma>' \<subseteq> heapVars \<Delta>'"
using assms
proof(induct rule: distinct_reds.induct)
case DLambda
  case 1 show ?case by simp
  case 2 show ?case by simp
next
case (DApplication n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e' u)
  case 1
  show ?case
    using DApplication by simp
  case 2
  show ?case
  proof
    fix v
    assume "v \<in> heapVars ((x, App e y) # \<Gamma>')"
    hence "\<not>( atom v \<sharp> (x, App e y) # \<Gamma>')"
      by (rule heapVars_not_fresh)
    hence "v \<noteq> n"
      by (metis DApplication(1) exp_assn.fresh(2) fresh_Cons fresh_Pair)

    assume "v \<in> heapVars ((x, App e y) # \<Gamma>')"
    hence "v \<in> heapVars ((n, e) # (x, App (Var n) y) # \<Gamma>')" by simp
    hence "v \<in> heapVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>')"
      by (rule set_mp[OF DApplication(10)])
    hence "v \<in> heapVars ((x, e'[z::=y]) # \<Delta>')"
      using `v \<noteq> n` by simp
    thus "v \<in> heapVars \<Theta>'" 
      by (rule set_mp[OF DApplication(13)])
  qed
next
case (DApplicationInd n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e' u)
  case 1
  show ?case
    using DApplicationInd by auto
  case 2
  show ?case
  proof
    fix v
    assume "v \<in> heapVars ((x, App e y) # \<Gamma>')"
    hence "\<not>( atom v \<sharp> (x, App e y) # \<Gamma>')"
      by (rule heapVars_not_fresh)
    hence "v \<noteq> n"
      by (metis DApplicationInd(1) exp_assn.fresh(2) fresh_Cons fresh_Pair)

    assume "v \<in> heapVars ((x, App e y) # \<Gamma>')"
    hence "v \<in> heapVars ((n, e) # (x, App (Var n) y) # \<Gamma>')" by simp
    hence "v \<in> heapVars ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>')"
      by (rule set_mp[OF DApplicationInd(10)])
    hence "v \<in> heapVars ((x, e') # \<Delta>')"
      using `v \<noteq> n` by simp
    thus "v \<in> heapVars \<Theta>'" 
      by (rule set_mp[OF DApplicationInd(13)])
  qed
next
case (DVariable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> i)
  case 1
  from DVariable(7)
  show ?case  by auto
  case 2
  from DVariable(3)
  have "y \<notin> heapVars ((x, Var y) # \<Gamma>')"
    by (metis distinctVars_ConsD(1) distinctVars_appendD1)
  with DVariable(8)
  show ?case
    by auto
next
case (DVariableNoUpd y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> i)
  case 1
  from DVariableNoUpd(7)
  show ?case  by auto
  case 2
  from DVariableNoUpd(3)
  have "y \<notin> heapVars ((x, Var y) # \<Gamma>')"
    by (metis distinctVars_ConsD(1) distinctVars_appendD1)
  with DVariableNoUpd(8)
  show ?case
    by auto
next
case (DLet as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  case 1 show ?case using DLet by simp
  case 2 show ?case using DLet by simp
qed

text {* Heap entries are never removed. *}

lemma reds_doesnt_forget:
 assumes "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'"
 assumes "distinctVars (\<Gamma>'@\<Gamma>)"
 shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>" and "heapVars \<Gamma>' \<subseteq> heapVars \<Delta>'"
by (rule reds_doesnt_forget'[OF distinct_redsI[OF assms]])+

text {* The stack is never empty. *}

lemma stack_not_empty:
  assumes "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'"
  shows "\<Delta>' \<noteq> []"
  using assms
  by (induct rule:reds.induct, simp_all)

text {* Evaluation does not change the name of the evaluation variable. *}

lemma stack_same_head:
  assumes "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>'"
  shows "fst (hd \<Delta>') = fst (hd \<Gamma>')"
  using assms
  by (induct rule:reds.induct, simp_all)

text {* Evaluation does not touch the tail of the stack. *}

lemma stack_unchanged:
  assumes "\<Gamma> : (x, e) # \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : (x, e') # \<Delta>'"
  shows "\<Delta>' = \<Gamma>'"
proof-
  {fix \<Gamma>' \<Delta>'
  have "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u \<Delta> : \<Delta>' \<Longrightarrow> tl \<Delta>' = tl \<Gamma>'"
    by (induct rule:reds.induct, simp_all)
  }
  from this[OF assms]
  show ?thesis by simp
qed


text {* 
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh':" \<lbrakk> \<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : \<Delta>';
   atom (x::var) \<sharp> (\<Gamma> , snd (hd \<Gamma>'))
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, snd (hd \<Delta>')) \<or> x \<in> heapVars \<Delta>"
proof(nominal_induct avoiding: x rule: distinct_reds.strong_induct)
case (DLambda \<Gamma> x e) thus ?case by auto
next
case (DApplication n \<Gamma> \<Gamma>' \<Delta> \<Delta>' xa e y \<Theta> \<Theta>' z e' u x)
  from DApplication have [simp]:"atom x \<sharp> \<Gamma>" "atom x \<sharp> e" "atom x \<sharp> y" by (simp add: fresh_Pair)+
  from `atom n \<sharp> x` have [simp]:"atom x \<sharp> n" by (metis fresh_at_base(2)) 
  have [simp]:"atom z \<sharp> y" by fact

  have "atom x \<sharp> (\<Gamma>, snd (hd ((n, e) # (xa, App (Var n) y) # \<Gamma>')))"
    by simp 
  from DApplication.hyps(28)[OF this, simplified]
  have "atom x \<sharp> (\<Delta>, Lam [z]. e') \<or> x \<in> heapVars \<Delta>".
  thus ?case
  proof
    assume "atom x \<sharp> (\<Delta>, Lam [z]. e')"
    hence [simp]:"atom x \<sharp> \<Delta>" by simp
    assume "atom x \<sharp> (\<Delta>, Lam [z]. e')"
    hence "atom x \<sharp> e' \<or> x = z"
      by (simp add: fresh_Pair)+
    hence "atom x \<sharp> (\<Delta>, snd (hd ((xa, e'[z::=y]) # \<Delta>')))"
    proof
      assume "atom x \<sharp> e'"
      thus ?thesis
        by (simp add: fresh_Pair subst_pres_fresh[rule_format])
    next
      assume "x = z"
      hence "z = x" by (rule sym)
      thus ?thesis
        by (auto intro!:subst_is_fresh simp add: fresh_Pair)
    qed
    thus ?thesis
      by (rule DApplication)
  next
    assume "x \<in> heapVars \<Delta>"
    thus ?thesis
    using reds_doesnt_forget'(1)[OF DApplication.hyps(29)]
    by auto
  qed
next
case (DApplicationInd n \<Gamma> \<Gamma>' \<Delta> \<Delta>' xa e y \<Theta> \<Theta>' z e' u x)
  from DApplicationInd have [simp]:"atom x \<sharp> \<Gamma>" "atom x \<sharp> e" "atom x \<sharp> y" by (simp add: fresh_Pair)+
  have [simp]:"atom z \<sharp> y" by fact

  have "atom x \<sharp> (\<Gamma>, snd (hd ((n, e) # (xa, App (Var n) y) # \<Gamma>')))"
    by simp 
  from DApplicationInd.hyps(24)[OF this, simplified]
  have "(x \<noteq> z \<and> atom x \<sharp> (\<Delta>, Lam [z]. e')) \<or> (x \<in> heapVars ((z, Var y) # \<Delta>))" by auto
  thus ?case
  proof(elim conjE disjE)
    assume "atom x \<sharp> (\<Delta>, Lam [z]. e')"
    hence [simp]:"atom x \<sharp> \<Delta>" by simp
    assume "atom x \<sharp> (\<Delta>, Lam [z]. e')" and "x \<noteq> z"
    hence "atom x \<sharp> e'"
      by (auto simp add: fresh_Pair)+
    note `atom x \<sharp> e'` and `x \<noteq> z`
    with `atom x \<sharp> y` 
    have "atom x \<sharp> ((z, Var y)#\<Delta>, snd (hd ((xa, e') # \<Delta>')))"
      by (simp add: fresh_Pair subst_pres_fresh[rule_format] fresh_Cons fresh_at_base)
    thus ?thesis
      by (rule DApplicationInd.hyps(26))
  next
    assume "x \<in> heapVars ((z, Var y) # \<Delta>)"
    thus ?thesis
    using reds_doesnt_forget'(1)[OF DApplicationInd.hyps(25)]
    by auto
  qed
next
case(DVariable y e \<Gamma> xa \<Gamma>' z \<Delta>' \<Delta> x)
  from `atom x \<sharp> _` ` (y, e) \<in> set \<Gamma>`
  have "atom x \<sharp> delete y \<Gamma>" and "atom x \<sharp> e"
    by (auto intro: fresh_delete dest:fresh_list_elem simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, snd (hd ((y, z) # (xa, Var y) # \<Delta>'))) \<or> x \<in> heapVars \<Delta>"
    by -(rule DVariable, simp add: fresh_Pair)
  thus ?case
    by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next
case(DVariableNoUpd y e \<Gamma> xa \<Gamma>' z \<Delta>' \<Delta> i x)
  from `atom x \<sharp> _` ` (y, e) \<in> set \<Gamma>`
  have "atom x \<sharp> delete y \<Gamma>" and "atom x \<sharp> e"
    by (auto intro: fresh_delete dest:fresh_list_elem simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, snd (hd ((y, z) # (xa, Var y) # \<Delta>'))) \<or> x \<in> heapVars \<Delta>"
    by -(rule DVariableNoUpd, simp add: fresh_Pair)
  with `atom x \<sharp> e`
  show ?case
    by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next
case (DLet as \<Gamma> xa body \<Gamma>' \<Delta>' \<Delta> x)
  show ?case
    proof (cases "atom x \<in> set (bn as)")
    case False
      hence "atom x \<sharp> as" using DLet.prems by(auto simp add: fresh_Pair)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap.induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair)
      show ?thesis
        apply(rule DLet.hyps(9))
        using DLet.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap.induct)(auto simp add: exp_assn.bn_defs)      
      thus ?thesis using reds_doesnt_forget'[OF DLet.hyps(8)] by auto
    qed
qed

lemma reds_fresh: " \<lbrakk> \<Gamma> : (y, e) # \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^sup>d \<Delta> : (y, z) # \<Delta>';
   atom (x::var) \<sharp> (\<Gamma> , e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta>"
by (metis (hide_lams, no_types) hd.simps reds_fresh' snd_conv)

end

