theory LaunchburyCombined
imports Terms Heap
begin

subsubsection {* The natural semantics, all variants at once*}


inductive
  reds :: "heap \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool"
  ("(4_ : _/ \<Down>\<^sup>_\<^sup>_\<^bsub>_\<^esub>/ _ : _)" [50,50,50,50,50,50] 50)
where
  Lambda: "atom x \<sharp> (\<Gamma>, L)
    \<Longrightarrow> \<Gamma> : Lam [x]. e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Gamma> : Lam [x]. e"
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^sup>False\<^sup>u\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^sup>False\<^sup>u\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>False\<^sup>u\<^bsub>L\<^esub> \<Theta> : z" 
 | ApplicationInd: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,z) ;
    \<Gamma> : e \<Down>\<^sup>True\<^sup>u\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    (y, Var x) # \<Delta> : e' \<Down>\<^sup>True\<^sup>u \<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>True\<^sup>u\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>; delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>True\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>True\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | VariableNoUpd: "\<lbrakk>
    (x,e) \<in> set \<Gamma>; delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>False\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>False\<^bsub>L\<^esub> (x, e) # \<Delta> : z"
 | Let: "\<lbrakk>
    set (bn as) \<sharp>* (\<Gamma>, L);
    distinctVars (asToHeap as);
    asToHeap as @ \<Gamma> : body \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Let as body \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z"

equivariance reds

nominal_inductive reds
avoids Lambda: "x" | Application: "y"
apply (auto simp add: fresh_star_def fresh_Pair pure_fresh)
done

lemma LambdaI: "\<Gamma> : Lam [x]. e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Gamma> : Lam [x]. e"
proof-
  obtain x' :: var where "atom x' \<sharp> (\<Gamma>, L, e)"  by (rule obtain_fresh)
  hence "atom x' \<sharp> (\<Gamma>, L)" and [simp]:"atom x' \<sharp> e" by (simp_all add: fresh_Pair)

  
  have "(x \<leftrightarrow> x') \<bullet> Lam [x]. e = Lam [x]. e"
    by (rule flip_fresh_fresh) simp+
  moreover
  have "(x \<leftrightarrow> x') \<bullet> Lam [x]. e = Lam [x']. ((x \<leftrightarrow> x') \<bullet> e)" by simp
  moreover
  from `atom x' \<sharp> (\<Gamma>, L)`
  have "\<Gamma> : Lam [x']. ((x \<leftrightarrow> x') \<bullet> e) \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Gamma> : Lam [x']. ((x \<leftrightarrow> x') \<bullet> e)"
    by (rule Lambda)
  ultimately
  show ?thesis by metis
qed

subsubsection {* Specializations*}

abbreviation
  reds_NS :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<equiv> \<Gamma> : e \<Down>\<^sup>False\<^sup>True\<^bsub>L\<^esub> \<Delta> : z"

lemma eval_test_NS:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by(auto intro!: LambdaI Variable Let simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)

schematic_lemma eval_test2_NS:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>
  [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : Lam [y]. Var y"
  by (auto intro!: LambdaI Application Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)

abbreviation
  reds_INS :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^sup>I\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  "\<Gamma> : e \<Down>\<^sup>I\<^bsub>L\<^esub> \<Delta> : z \<equiv> \<Gamma> : e \<Down>\<^sup>True\<^sup>True\<^bsub>L\<^esub> \<Delta> : z"

lemma eval_test_INS:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^sup>I\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by(auto intro!: LambdaI Variable Let simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)

schematic_lemma eval_test2_INS:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>
  [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^sup>I\<^bsub>[]\<^esub> [(y, Lam [y]. Var y), (x, Lam [y]. Var y)] : Lam [y]. Var y"
  by (auto intro!: LambdaI ApplicationInd Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)

abbreviation
  reds_NNS :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^sup>N\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  "\<Gamma> : e \<Down>\<^sup>N\<^bsub>L\<^esub> \<Delta> : z \<equiv> \<Gamma> : e \<Down>\<^sup>False\<^sup>False\<^bsub>L\<^esub> \<Delta> : z"

lemma eval_test_NNS:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^sup>N\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by(auto intro!: LambdaI VariableNoUpd Let simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)

schematic_lemma eval_test2_NNS:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>
  [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^sup>N\<^bsub>[]\<^esub> [ (x, Lam [y]. Var y)] : Lam [y]. Var y"
  by (auto intro!: LambdaI Application VariableNoUpd Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)

abbreviation
  reds_ANS :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^sup>A\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  "\<Gamma> : e \<Down>\<^sup>A\<^bsub>L\<^esub> \<Delta> : z \<equiv> \<Gamma> : e \<Down>\<^sup>True\<^sup>False\<^bsub>L\<^esub> \<Delta> : z"

lemma eval_test_A:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^sup>A\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by(auto intro!: LambdaI  VariableNoUpd Let simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)

schematic_lemma eval_test2_A:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>
  [] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^sup>A\<^bsub>[]\<^esub> [(y, Var x), (x, Lam [y]. Var y)] : Lam [y]. Var y"
  by (auto intro!: LambdaI ApplicationInd VariableNoUpd Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)

subsubsection {* Properties of the semantics *}

text {*
Heap entries are never removed.
*}

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
  by(induct rule: reds.induct) auto

text {*
Live variables are not added to the heap.
*}

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> heapVars \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> heapVars \<Delta>"
proof(induction rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> z \<Theta> u e')
  thus ?case by (auto simp add: fresh_Pair dest: fresh_list_elem)
next
case (ApplicationInd y \<Gamma> e x' L \<Delta> z u e' \<Theta>)
  thus ?case by (auto simp add: fresh_Pair dest: fresh_list_elem)
next
case (Variable  x e \<Gamma> L \<Delta> z) thus ?case
   using heapVars_from_set[OF Variable(1)] by auto
next
case (VariableNoUpd  x e \<Gamma> L \<Delta> z) thus ?case
   using heapVars_from_set[OF VariableNoUpd(1)] by auto
next
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> heapVars \<Gamma>" by fact moreover
  have "set (bn as) \<sharp>* L" using `set (bn as) \<sharp>* (\<Gamma>, L)` by (simp add: fresh_star_Pair)
  hence "x \<notin> heapVars (asToHeap as)"
    using `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by auto  
  thus ?case
    by (rule Let.IH[OF `x \<in> set L`])
qed

text {*
This is the same semantics with additional distinctiveness requirements. This
is defined in order to obtain a more convenient induction rule.
*}

inductive
  distinct_reds :: "heap \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool"
  ("_ : _ \<Down>\<^sup>_\<^sup>_\<^sup>d\<^bsub>_\<^esub> _ : _" [50,50,50,50,50,50] 50)
where
  DLambda: "\<lbrakk>
    atom x \<sharp> (\<Gamma>, L);
    distinctVars \<Gamma>
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : (Lam [x]. e) \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | DApplication: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^sup>False\<^sup>u\<^sup>d\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^sup>False\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Theta> : z;
    distinctVars \<Gamma>;
    distinctVars \<Theta>
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>False\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Theta> : z" 
 | DApplicationInd: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,z) ;
    \<Gamma> : e \<Down>\<^sup>True\<^sup>u\<^sup>d\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    (y, Var x) # \<Delta> : e' \<Down>\<^sup>True\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Theta> : z;
    distinctVars \<Gamma>;
    distinctVars \<Theta>
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>True\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Theta> : z" 
 | DVariable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>;
    delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>True\<^sup>d\<^bsub>x#L\<^esub> \<Delta> : z;
    distinctVars \<Gamma>;
    distinctVars ((x,z) # \<Delta>)
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>True\<^sup>d\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | DVariableNoUpd: "\<lbrakk>
    (x,e) \<in> set \<Gamma>;
    delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>False\<^sup>d\<^bsub>x#L\<^esub> \<Delta> : z;
    distinctVars \<Gamma>;
    distinctVars ((x,e) # \<Delta>)
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>False\<^sup>d\<^bsub>L\<^esub> (x, e) # \<Delta> : z"
 | DLet: "\<lbrakk>
    set (bn as) \<sharp>* (\<Gamma>, L);
    distinctVars (asToHeap as);
    asToHeap as @ \<Gamma> : body \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z;
    distinctVars \<Gamma>;
    distinctVars \<Delta>
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Let as body \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z"

equivariance distinct_reds

nominal_inductive distinct_reds
  avoids DLambda: "x" | DApplication: "y"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)
  done

lemma distinct_redsD1:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z"
  apply (induct rule:distinct_reds.induct)
  apply (auto intro:reds.intros simp add: fresh_star_Pair fresh_Pair)
  done

lemma distinct_redsD2:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma>"
  apply (induct rule: distinct_reds.induct)
  apply (auto)
  done

lemma distinct_redsD3:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Delta>"
  apply (induct rule: distinct_reds.induct)
  apply (auto simp add: distinctVars_Cons)
  done


lemma distinct_redsI:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>L\<^esub> \<Delta> : z"
proof (nominal_induct rule: reds.strong_induct)
  case (Variable x e \<Gamma> i L \<Delta> z)
    have "x \<notin> heapVars \<Delta>"
      apply (rule reds_avoids_live[OF Variable(2)])
      apply (auto)
      done
    moreover
    have "distinctVars (delete x \<Gamma>)"
      by (rule distinctVars_delete[OF Variable(4)])
    hence "delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>True\<^sup>d\<^bsub>x # L\<^esub> \<Delta> : z" by (rule Variable.hyps)
    moreover
    hence "distinctVars \<Delta>" by (rule distinct_redsD3)
    hence "distinctVars ((x, z) # \<Delta>)"
      using `x \<notin> heapVars \<Delta>` by (simp add: distinctVars_Cons)
    ultimately
    show ?case
      using Variable
      by (metis distinct_reds.DVariable)
next
  case (VariableNoUpd x e \<Gamma> i L \<Delta> z)
    have "x \<notin> heapVars \<Delta>"
      apply (rule reds_avoids_live[OF VariableNoUpd(2)])
      apply (auto)
      done
    moreover
    have "distinctVars (delete x \<Gamma>)"
      by (rule distinctVars_delete[OF VariableNoUpd(4)])
    hence "delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>False\<^sup>d\<^bsub>x # L\<^esub> \<Delta> : z" by (rule VariableNoUpd.hyps)
    moreover
    hence "distinctVars \<Delta>" by (rule distinct_redsD3)
    hence "distinctVars ((x, e) # \<Delta>)"
      using `x \<notin> heapVars \<Delta>` by (simp add: distinctVars_Cons)
    ultimately
    show ?case
      using VariableNoUpd
      by (metis distinct_reds.DVariableNoUpd)
qed (auto intro: distinctVars_append_asToHeap
          dest: distinct_redsD3 heapVars_not_fresh
          intro!: distinct_reds.intros
          simp add: fresh_star_Pair distinctVars_Cons)

lemma reds_pres_distinctVars:
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta>"
by (metis distinct_redsD3 distinct_redsI)

lemmas reds_distinct_ind = distinct_reds.induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]
(* lemmas reds_distinct_strong_ind = distinct_reds.strong_induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let] *)

text {*
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (heapVars \<Delta> - set L)"
proof(induction rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z u e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta> - set (x' # L)" by (auto simp add: fresh_Pair)

  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    moreover
    have "atom x \<sharp> e'[y ::= x']" 
    proof(cases "x = y")
    case False
      hence "atom x \<sharp> e'" using `atom x \<sharp> (\<Delta>, Lam [y]. e')`
        by (auto simp add:fresh_Pair)
      thus ?thesis using Application.prems
        by (auto intro: subst_pres_fresh[rule_format] simp add: fresh_Pair)
    next
    case True
      thus ?thesis using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair)
    qed
    ultimately
    have "atom x \<sharp> (\<Delta>, e'[y::=x'])" by simp
    thus ?thesis by (rule Application.IH(2))
  next
    assume "x \<in> heapVars \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(3)] by auto
  qed
next
case (ApplicationInd y \<Gamma> e x' L \<Delta> z u e' \<Theta>)
  hence "atom x \<sharp> (\<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta> - set (x' # L)" 
    by (rule ApplicationInd.IH(1))
  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    show ?thesis
    proof(cases "x = y")
    case False
      from ApplicationInd.prems `atom x \<sharp> (\<Delta>, Lam [y]. e')` False
      have "atom x \<sharp> ((y, Var x') # \<Delta>, e')" by (simp add: fresh_Pair fresh_Cons)
      thus ?thesis by (rule ApplicationInd.IH(2))
    next
    case True
      hence "x \<in> heapVars ((y, Var x') # \<Delta>)" by simp
      hence "x \<in> heapVars \<Theta>" by (rule set_mp[OF reds_doesnt_forget[OF ApplicationInd.hyps(3)]])
      moreover
      have "atom x \<sharp> L" using True ApplicationInd by (simp add: fresh_Pair)
      hence "x \<notin> set L" by (metis fresh_list_elem not_self_fresh)
      ultimately
      show ?thesis by simp
    qed
  next
    assume "x \<in> heapVars \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF ApplicationInd.hyps(3)] by auto
  qed
next

case(Variable v e \<Gamma> i L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair)
  hence "atom x \<sharp> delete v \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_delete dest:fresh_list_elem)
  hence "atom x \<sharp> (delete v \<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta> - set (v # L)"  by (rule Variable.IH)
  thus ?case using `atom x \<sharp> e` `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case(VariableNoUpd v e \<Gamma> i L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using VariableNoUpd.prems(1) by (auto simp add: fresh_Pair)
  hence "atom x \<sharp> delete v \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_delete dest:fresh_list_elem)
  hence "atom x \<sharp> (delete v \<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta> - set (v # L)"  by (rule VariableNoUpd.IH)
  thus ?case using `atom x \<sharp> e` `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Let as \<Gamma> L body \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap.induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair)
      show ?thesis
        apply(rule Let.IH)
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap.induct)(auto simp add: exp_assn.bn_defs)      
      moreover
      have "x \<notin> set L"
        using Let(1)
        by (metis True fresh_list_elem fresh_star_Pair fresh_star_def not_self_fresh)
      ultimately
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(3)] by auto
    qed
qed

text {*
Reducing the set of variables to avoid is always possible.
*} 


lemma fresh_set_subset: "x \<sharp> L \<Longrightarrow> set L' \<subseteq> set L \<Longrightarrow> x \<sharp> L'"
  by (induction L') (auto simp add: fresh_Cons fresh_Nil dest: fresh_list_elem)

lemma reds_smaller_L: "\<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z;
   set L' \<subseteq> set L
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule LambdaI)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z u e' L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair dest: fresh_set_subset)
  
    have "set (xa # L') \<subseteq> set (xa # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^sup>False\<^sup>u\<^bsub>xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(10))

    show "\<Delta> : e'[y ::= xa] \<Down>\<^sup>False\<^sup>u\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(12)[OF Application.prems])
  qed
next 
case (ApplicationInd y \<Gamma> e xa L \<Delta> z u e' \<Theta> L')
  show ?case
  proof(rule reds.ApplicationInd)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, z)"
      using ApplicationInd
      by (auto simp add: fresh_Pair dest: fresh_set_subset)
  
    have "set (xa # L') \<subseteq> set (xa # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^sup>True\<^sup>u\<^bsub>xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule ApplicationInd.hyps(8))

    show "(y, Var xa) # \<Delta> : e' \<Down>\<^sup>True\<^sup>u\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule ApplicationInd.hyps(10)[OF ApplicationInd.prems])
  qed
next 
case (Variable xa e \<Gamma> i L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (VariableNoUpd xa e \<Gamma> i L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using VariableNoUpd.prems by auto
  thus ?case
    by (rule reds.VariableNoUpd[OF VariableNoUpd(1) VariableNoUpd.hyps(3)])
next
case (Let as \<Gamma>  L body \<Delta> z L')
  have "set (bn as) \<sharp>* (\<Gamma>, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _ Let.hyps(3) Let.hyps(5)[OF Let.prems]])
qed
end

