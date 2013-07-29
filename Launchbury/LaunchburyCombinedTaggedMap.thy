theory LaunchburyCombinedTaggedMap
imports Terms Heap "FMap-Nominal"
begin

lemma fdom_fmap_of_conv_heapVars: "fdom (fmap_of (asToHeap as)) = heapVars (asToHeap as)"
  by (metis dom_map_of_conv_heapVars fdom.rep_eq fmap_of.rep_eq)

datatype Flag = FlagSet ("\<surd>") | FlagNotSet ("\<times>")

instantiation  Flag :: pure
begin
  definition "p \<bullet> (v::Flag) = v"
instance
  apply default
  apply (auto simp add: permute_Flag_def)
  done
end

type_synonym Heap = "var f\<rightharpoonup> exp"


inductive reds :: "Heap \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> Flag \<Rightarrow> var list \<Rightarrow> Heap \<Rightarrow> bool" ("_/ \<Down>\<^sup>_\<^sup>_\<^sup>_\<^bsub>_\<^esub>/ _" [50,50,50,50,50] 50)
where
  Lambda:
    "\<Gamma>(x f\<mapsto> Lam [y]. e) \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Gamma>(x f\<mapsto> Lam [y]. e) " 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>);
      \<Gamma> (x f\<mapsto> App (Var n) y) (n f\<mapsto> e ) \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>n#x#S\<^esub> (\<Delta>::Heap) (n f\<mapsto> (Lam [z]. e'));
      \<Delta> (x f\<mapsto> e'[z ::= y]) \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      \<Gamma> ( x f\<mapsto> App e y ) \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Theta>" 
 | ApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,S,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,S,\<Delta>);
      \<Gamma> (x f\<mapsto> App (Var n) y) (n f\<mapsto> e ) \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>n#x#S\<^esub> (\<Delta>::Heap) (n f\<mapsto> (Lam [z]. e'));
      \<Delta> (z f\<mapsto> Var y) (x f\<mapsto> e') \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      \<Gamma> ( x f\<mapsto> App e y ) \<Down>\<^sup>\<times>\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Theta>" 
 | Variable: "\<lbrakk>
      y \<notin> set (x#S);
      \<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>y#x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      \<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<surd>\<^bsub>x#S\<^esub> fmap_copy \<Delta> y x"
 | VariableNoBH: "\<lbrakk>
      \<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<times>\<^bsub>y#x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      \<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>i\<^sup>\<surd>\<^sup>\<times>\<^bsub>x#S\<^esub> fmap_copy \<Delta> y x"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, S);
      distinctVars (asToHeap as);
      \<Gamma>(x f\<mapsto> body) f++ fmap_of (asToHeap as) \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      \<Gamma>(x f\<mapsto> Let as body) \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>x#S\<^esub> \<Delta>"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z" | ApplicationInd: "n"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh
      eqvt_fresh_cong3[where f = fmap_upd, OF fmap_upd_eqvt])
  done


subsubsection {* Properties of the semantics *}

lemma stack_head_there:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta> \<Longrightarrow> hd S \<in> fdom \<Gamma>"
  by (induct rule: reds.induct) auto

text {* Heap entries are never removed. *}

lemma
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta>"
  shows reds_doesnt_forget: "fdom \<Gamma> \<subseteq> fdom \<Delta>" and stack_bound: "hd S \<in> fdom \<Delta>"
using assms
  by (induct rule: reds.induct)
     (auto simp add: fresh_Pair fresh_at_base dest: heapVars_not_fresh)

text {* Things are evaluated to a lambda expression. *}

lemma
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta>"
  shows result_evaluated: "isLam (\<Delta> f! (hd S))"
using assms
 by (induct \<Gamma> i u b S \<Delta> rule:reds.induct) (auto dest: reds_doesnt_forget)

  
text {* The stack is never empty. *}

lemma stack_not_empty:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta>"
  shows "S \<noteq> []"
  using assms
  by (induct rule:reds.induct, simp_all)

text {* Evaluation does not touch the tail of the stack. *}

lemma set_bn_to_atom_fdom: "set (bn as) = atom ` fdom (fmap_of (asToHeap as))"
  by (metis fdom_fmap_of_conv_heapVars set_bn_to_atom_heapVars)

lemma fresh_at_base_list: "atom (x::'a::at_base) \<sharp> l \<longleftrightarrow> x \<notin> set l"
  by (metis List.finite_set fresh_finite_set_at_base fresh_set)

lemma fresh_star_list_distinct:  "atom ` (S::var set) \<sharp>* (l::var list) \<longleftrightarrow> (set l \<inter> S = {})"
  by (auto simp add: fresh_star_def set_not_fresh fresh_at_base_list dest:bspec)

lemma stack_unchanged:
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>\<surd>\<^bsub>S\<^esub> \<Delta>"
  assumes "x \<noteq> hd S"
  assumes "x \<in> set (tl S)"
  shows   "lookup \<Delta> x = lookup \<Gamma> x"
using assms
 apply (induct \<Gamma> i u \<surd> S \<Delta> arbitrary: x rule:reds.induct)
 apply (auto simp add: fresh_Pair fresh_star_Pair set_bn_to_atom_fdom fresh_star_list_distinct fresh_at_base_list)
 apply (metis lookup_fmap_upd_other)
 apply (metis lookup_fmap_upd_other)
 apply (metis lookup_fmap_upd_other)
 apply (metis Int_iff empty_iff lookup_fmap_add2 lookup_fmap_upd_other)
 done

  
text {* 
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>b\<^bsub>S\<^esub> \<Delta>;
   atom (x::var) \<sharp> \<Gamma>
  \<rbrakk> \<Longrightarrow> atom x \<sharp> \<Delta> \<or> x \<in> fdom \<Delta>"
proof(nominal_induct avoiding: x rule: reds.strong_induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application n \<Gamma> x e y S \<Delta> \<Theta> z u b e' x')
  from `atom n \<sharp> x'` `atom x' \<sharp> \<Gamma>(x f\<mapsto> App e y)`
  have "atom x' \<sharp> \<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)"
    by (auto simp add: fresh_Pair fresh_fmap_upd_eq eqvt_fresh_cong2[where f = fmap_delete, OF fmap_delete_eqvt])
  from Application.hyps(19)[OF this]
  show ?case
  proof
    assume "atom x' \<sharp> \<Delta>(n f\<mapsto> Lam [z]. e')"
    with `atom n \<sharp> \<Delta>` `atom x' \<sharp> \<Gamma>(x f\<mapsto> App e y)`
    have "atom x' \<sharp> \<Delta>(x f\<mapsto> e'[z::=y])"
      by (auto simp add: subst_pres_fresh  fresh_fmap_upd_eq fresh_fmap_delete_subset)
    from Application.hyps(21)[OF this]
    show ?thesis.
  next
    assume "x' \<in> fdom (\<Delta>(n f\<mapsto> Lam [z]. e'))"
    with `atom n \<sharp> x'`
    have "x' \<in> fdom (\<Delta>(x f\<mapsto> e'[z::=y]))" by (simp add: fresh_at_base)
    with reds_doesnt_forget[OF Application(20)]
    have "x' \<in> fdom \<Theta>" by auto
    thus ?thesis..
  qed
next
case (ApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z u b e' x')
  show ?case
  proof(cases "x' = z")
  case True
    with  reds_doesnt_forget[OF ApplicationInd(18)]
    have "x' \<in> fdom \<Theta>" by auto
    thus ?thesis..
  next
  case False
    from `atom n \<sharp> x'` `atom x' \<sharp> \<Gamma>(x f\<mapsto> App e y)`
    have "atom x' \<sharp> \<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)"
      by (auto simp add: fresh_Pair fresh_fmap_upd_eq fresh_fmap_delete_subset)
    from ApplicationInd.hyps(17)[OF this]
    show ?thesis
    proof
      assume "atom x' \<sharp> \<Delta>(n f\<mapsto> Lam [z]. e')"
      with `atom n \<sharp> \<Delta>` `atom x' \<sharp> \<Gamma>(x f\<mapsto> App e y)` False
      have "atom x' \<sharp> \<Delta> (z f\<mapsto> Var y)(x f\<mapsto> e')"
        by (auto simp add:  fresh_fmap_upd_eq fresh_fmap_delete_subset fresh_at_base)
      from ApplicationInd.hyps(19)[OF this]
      show ?thesis.
    next
      assume "x' \<in> fdom (\<Delta>(n f\<mapsto> Lam [z]. e'))"
      with `atom n \<sharp> x'`
      have "x' \<in> fdom (\<Delta> (z f\<mapsto> Var y)(x f\<mapsto> e'))" by (simp add: fresh_at_base)
      with reds_doesnt_forget[OF ApplicationInd(18)]
      have "x' \<in> fdom \<Theta>" by auto
      thus ?thesis..
    qed
  qed
next
case Variable
thus ?case
    apply (auto simp add: fresh_Pair fresh_at_base fresh_fmap_copy_subset)
    apply (metis atom_eq_iff fresh_at_base(2) fresh_fmap_copy_subset)
    apply (metis fresh_fmap_copy_subset fresh_fmap_upd_eq)
    apply (metis fresh_fmap_upd_eq not_self_fresh)
    done
next 
case VariableNoBH
  thus ?case
    apply (auto simp add: fresh_Pair fresh_at_base fresh_fmap_copy_subset)
    apply (metis atom_eq_iff fresh_at_base(2) fresh_fmap_copy_subset)
    apply (metis fresh_fmap_copy_subset fresh_fmap_upd_eq)
    apply (metis fresh_fmap_upd_eq not_self_fresh)
    done
next
case (Let as \<Gamma> x S body i u b \<Delta> x')
  show ?case
  proof(cases "x' \<in> fdom (fmap_of (asToHeap as))")
    case True
    with reds_doesnt_forget[OF Let(5)]
    show ?thesis by auto
  next
    case False
    hence "atom x' \<notin> set (bn as)" by (auto simp add: set_bn_to_atom_fdom)
    with `atom x' \<sharp> \<Gamma>(x f\<mapsto> Terms.Let as body)`
    have "atom x' \<sharp> \<Gamma>(x f\<mapsto> body) f++ fmap_of (asToHeap as)"
      by (simp add: fresh_fmap_upd_eq fresh_fmap_add_subset
              eqvt_fresh_cong1[where f = fmap_of, OF fmap_of_eqvt]
              fresh_fun_eqvt_app[OF asToHeap_eqvt])
    from Let(6)[OF this]
    show ?thesis.
  qed
qed

end

