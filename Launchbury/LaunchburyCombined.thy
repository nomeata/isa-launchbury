theory LaunchburyCombined
imports Terms Heap "FMap-Heap" "FMap-Nominal" Flag
begin

lemma fdom_fmap_of_conv_heapVars: "fdom (fmap_of (asToHeap as)) = heapVars (asToHeap as)"
  by (metis dom_map_of_conv_heapVars fdom.rep_eq fmap_of.rep_eq)

lemma set_bn_to_atom_fdom: "set (bn as) = atom ` fdom (fmap_of (asToHeap as))"
  by (metis fdom_fmap_of_conv_heapVars set_bn_to_atom_heapVars)

lemma fresh_at_base_list: "atom (x::'a::at_base) \<sharp> l \<longleftrightarrow> x \<notin> set l"
  by (metis List.finite_set fresh_finite_set_at_base fresh_set)

lemma fresh_star_list_distinct:  "atom ` (S::var set) \<sharp>* (l::var list) \<longleftrightarrow> (set l \<inter> S = {})"
  by (auto simp add: fresh_star_def set_not_fresh fresh_at_base_list dest:bspec)

subsubsection {* The natural semantics, all variants at once*}

inductive
  reds :: "Heap \<Rightarrow> exp \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> var list \<Rightarrow> Heap \<Rightarrow> exp \<Rightarrow> bool"
  ("(4_ : _/ \<Down>\<^sup>_\<^sup>_\<^bsub>_\<^esub>/ _ : _)" [50,50,50,50,50,50] 50)
where
  Lambda: "atom x \<sharp> (\<Gamma>, L)
    \<Longrightarrow> \<Gamma> : Lam [x]. e \<Down>\<^sup>i\<^sup>b\<^bsub>L\<^esub> \<Gamma> : Lam [x]. e"
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^sup>\<times>\<^sup>b\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>\<times>\<^sup>b\<^bsub>L\<^esub> \<Theta> : z" 
 | ApplicationInd: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L);
    \<Gamma> : e \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>y#x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta>(y f\<mapsto> Var x) : e' \<Down>\<^sup>\<surd>\<^sup>u \<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    lookup \<Gamma> x = Some e; fmap_delete x \<Gamma> : e \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>\<surd>\<^bsub>L\<^esub> \<Delta>(x f\<mapsto> z) : z"
 | VariableNoBH: "\<lbrakk>
    lookup \<Gamma> x = Some e;  \<Gamma> : e \<Down>\<^sup>i\<^sup>\<times>\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^sup>i\<^sup>\<times>\<^bsub>L\<^esub> \<Delta>(x f\<mapsto> z) : z"
 | Let: "\<lbrakk>
    set (bn as) \<sharp>* (\<Gamma>, L);
    \<Gamma> f++ (fmap_of (asToHeap as)) : body \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z
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
  reds_NS :: "Heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> Heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<equiv> \<Gamma> : e \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>L\<^esub> \<Delta> : z"

lemma eval_test_NS:
  "f\<emptyset> : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[]\<^esub> f\<emptyset>(x f\<mapsto> Lam [y]. Var y) : (Lam [y]. Var y)"
  by (auto intro!: LambdaI Variable Let simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)
  

lemma eval_test2_NS:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>
  f\<emptyset> : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> f\<emptyset>(x f\<mapsto> Lam [y]. Var y) : Lam [y]. Var y"
  by (auto intro!: LambdaI Application Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh fresh_fmap_upd_eq)

text {* This lemma shows that variables not free in the initial expression can still become 
new names on the heap. *}
lemma eval_test3_NS:
  "y \<noteq> x \<Longrightarrow> f\<emptyset> : (App (Lam [y]. let x be Var x in (Lam [z].Var z))) x \<Down>\<^bsub>[]\<^esub> f\<emptyset>(x f\<mapsto> Var x) : Lam [z]. Var z"
apply (rule Application[where y = y, rotated])
  apply (rule LambdaI)
 apply (simp add: subst_fresh_noop fresh_at_base)
 apply (rule Let)
   apply (simp add: fresh_star_Pair fresh_star_def fresh_Nil)
  apply simp
 apply (rule LambdaI)
 apply (simp add: fresh_Pair fresh_Nil fresh_Cons fresh_at_base fresh_fmap_upd_eq)
done

subsubsection {* Properties of the semantics *}

text {*
Heap entries are never removed.
*}

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>b\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> fdom \<Gamma> \<subseteq> fdom \<Delta>"
  by(induct rule: reds.induct) auto

text {*
Live variables are not added to the heap.
*}

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>b\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> fdom \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> fdom \<Delta>"
proof(induction rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> z \<Theta> u e')
  thus ?case by (auto simp add: fresh_Pair dest: fresh_list_elem)
next
case (ApplicationInd y \<Gamma> e x' L \<Delta> z u e' \<Theta>)
  thus ?case by (auto simp add: fresh_Pair dest: fresh_list_elem)
next
case (Variable  x e \<Gamma> L \<Delta> z) thus ?case by auto
next
case (VariableNoBH  x e \<Gamma> L \<Delta> z) thus ?case by auto
next
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> fdom \<Gamma>" by fact moreover
  have "set (bn as) \<sharp>* L" using `set (bn as) \<sharp>* (\<Gamma>, L)` by (simp add: fresh_star_Pair)
  hence "x \<notin> fdom (fmap_of (asToHeap as))"
    using `x \<in> set L`
    apply (auto simp add: fdom_fmap_of_conv_heapVars set_bn_to_atom_fdom)
    by (metis disjoint_iff_not_equal fresh_star_list_distinct)
  ultimately
  have"x \<notin> fdom (\<Gamma> f++ fmap_of (asToHeap as))" by auto
  thus ?case
    by (rule Let.IH[OF `x \<in> set L`])
qed

text {*
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>b\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (fdom \<Delta> - set L)"
proof(induction rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z u e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> fdom \<Delta> - set (x' # L)" by (auto simp add: fresh_Pair)

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
    assume "x \<in> fdom \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(3)] by auto
  qed
next
case (ApplicationInd y \<Gamma> e x' L u \<Delta> e' \<Theta> z)
  hence "atom x \<sharp> (\<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> fdom \<Delta> - set (y # x' # L)" 
    by (rule ApplicationInd.IH(1))
  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    show ?thesis
    proof(cases "x = y")
    case False
      from ApplicationInd.prems `atom x \<sharp> (\<Delta>, Lam [y]. e')` False
      have "atom x \<sharp> (\<Delta>(y f\<mapsto>  Var x') , e')" by (simp add: fresh_Pair fresh_Cons fresh_fmap_upd_eq fresh_fmap_delete_subset)
      thus ?thesis by (rule ApplicationInd.IH(2))
    next
    case True
      hence "x \<in> fdom (\<Delta>(y f\<mapsto>  Var x'))" by simp
      hence "x \<in> fdom \<Theta>" by (rule set_mp[OF reds_doesnt_forget[OF ApplicationInd.hyps(3)]])
      moreover
      have "atom x \<sharp> L" using True ApplicationInd by (simp add: fresh_Pair)
      hence "x \<notin> set L" by (metis fresh_list_elem not_self_fresh)
      ultimately
      show ?thesis by simp
    qed
  next
    assume "x \<in> fdom \<Delta>  - set (y # x' # L)"
    thus ?thesis using reds_doesnt_forget[OF ApplicationInd.hyps(3)] by auto
  qed
next

case(Variable \<Gamma> v e i L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair)
  hence "atom x \<sharp> fmap_delete v \<Gamma>" and "atom x \<sharp> e" using `lookup \<Gamma> v = Some e`
    apply (auto intro: fresh_fmap_delete_subset dest:fresh_list_elem)
    by (metis fmap_upd_noop fresh_fmap_upd_eq lookup_fdom the.simps)
  hence "atom x \<sharp> (fmap_delete v \<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> fdom \<Delta> - set (v # L)"  by (rule Variable.IH)
  thus ?case using `atom x \<sharp> e` `atom x \<sharp> v`
    by (auto simp add: fresh_Pair fresh_Cons fresh_at_base fresh_fmap_upd_eq fresh_fmap_delete_subset)
next

case(VariableNoBH \<Gamma> v e i L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using VariableNoBH.prems(1) by (auto simp add: fresh_Pair)
  hence "atom x \<sharp> \<Gamma>" and "atom x \<sharp> e" using `lookup \<Gamma> v = Some e`
    apply (auto) by (metis fmap_upd_noop fresh_fmap_upd_eq lookup_fdom the.simps)
  hence "atom x \<sharp> (\<Gamma>, e)" by (simp add: fresh_Pair)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> fdom \<Delta> - set (v # L)"  by (rule VariableNoBH.IH)
  thus ?case using `atom x \<sharp> e` `atom x \<sharp> v`
    by (auto simp add: fresh_Pair fresh_Cons fresh_at_base fresh_fmap_upd_eq fresh_fmap_delete_subset)
next

case (Let as \<Gamma> L body \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair)      
      hence "atom x \<sharp> asToHeap as"
        by (rule fresh_fun_eqvt_app[OF asToHeap_eqvt])
      show ?thesis
        apply(rule Let.IH)
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair fresh_append fresh_fmap_add_subset eqvt_fresh_cong1[OF fmap_of_eqvt])
    next
    case True
      hence "x \<in> fdom (fmap_of (asToHeap as))" 
        by (simp add: fdom_fmap_of_conv_heapVars image_iff set_bn_to_atom_heapVars)
      moreover
      have "x \<notin> set L"
        using Let(1)
        by (metis True fresh_list_elem fresh_star_Pair fresh_star_def not_self_fresh)
      ultimately
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(2)] by auto
    qed
qed

lemma reds_fresh_L:" \<lbrakk> \<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e) ; x \<in> set L
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z)"
  by (metis reds_fresh Diff_iff)


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
case (Application y \<Gamma> e x L \<Delta> \<Theta> z u e' b L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, x, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair dest: fresh_set_subset)
  
    have "set (x # L') \<subseteq> set (x # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(10))

    show "\<Delta> : e'[y ::= x] \<Down>\<^sup>\<times>\<^sup>b\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(12)[OF Application.prems])
  qed
next 
case (ApplicationInd y \<Gamma> e x L u \<Delta> e' \<Theta> z L')
  show ?case
  proof(rule reds.ApplicationInd)
    show "atom y \<sharp> (\<Gamma>, e, x, L')"
      using ApplicationInd
      by (auto simp add: fresh_Pair dest: fresh_set_subset)
  
    have "set (y # x # L') \<subseteq> set (y # x # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>y # x # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule ApplicationInd.hyps(6))

    show "\<Delta>(y f\<mapsto> Var x) : e' \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule ApplicationInd.hyps(8)[OF ApplicationInd.prems])
  qed
next 
case (Variable \<Gamma> x e i L \<Delta> z L')
  have "set (x # L') \<subseteq> set (x # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (VariableNoBH \<Gamma> x e i L \<Delta> z L')
  have "set (x # L') \<subseteq> set (x # L)"
    using VariableNoBH.prems by auto
  thus ?case
    by (rule reds.VariableNoBH[OF VariableNoBH(1) VariableNoBH.hyps(3)])
next
case (Let as \<Gamma>  L body \<Delta> z L')
  have "set (bn as) \<sharp>* (\<Gamma>, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _  Let.hyps(4)[OF Let.prems]])
qed

end

