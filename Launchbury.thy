theory Launchbury
imports Terms
begin

type_synonym heap = "(var \<times> exp) list"

lemma fresh_delete:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> \<Gamma>(y := None)"
apply (simp add: fresh_def)
apply (simp add: supp_def)
oops

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

lemma subst_is_fresh:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "set (bn as) \<sharp>* (y, z) \<Longrightarrow> atom y \<sharp> (subst_assn as y z)"
thm subst_subst_assn.induct
using assms
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:exp_assn.fresh fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

lemma
 subst_pres_fresh: "(atom x \<sharp> e \<and> atom x \<sharp> z) --> atom x \<sharp> e[y ::= z]"
and
 "(atom x \<sharp> as \<and> atom x \<sharp> z \<and> atom x \<notin> set (bn as)) --> (atom x \<sharp> (subst_assn as y z))"
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:exp_assn.fresh fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

nominal_primrec  asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # asToHeap as"
unfolding eqvt_def asToHeap_graph_def
apply rule
apply perm_simp
apply rule
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
termination(eqvt) by lexicographic_order

lemmas asToHeap_induct = asToHeap.induct[case_names ANilToHeap AConsToHeap]

lemma asToHeap_eqvt[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (asToHeap as) = asToHeap (\<pi> \<bullet> as)"
by(induct as rule:asToHeap.induct) (auto simp add:asToHeap.simps)

inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>  \<Gamma> : e \<Down> \<Delta> : (Lam [y]. e') ; \<Delta> : e'[y ::= x] \<Down> \<Theta> : z\<rbrakk> \<Longrightarrow> \<Gamma> : App e x \<Down> \<Theta> : z" 
 | Variable: "\<lbrakk> (x,e) \<in> set \<Gamma>; removeAll (x, e) \<Gamma> : e \<Down> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down> (x, z) # \<Delta> : z"
 | Let: "asToHeap as @ \<Gamma> : body \<Down> \<Delta> : z \<Longrightarrow> \<Gamma> : Let as body \<Down> \<Delta> : z"

equivariance reds

nominal_inductive reds.
(*
  avoids LetACons: "v"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh exp_assn.bn_defs)
done
*)
(*
  avoids Application: "y"
apply (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh)
*)

lemma eval_test:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh)
done

lemma eval_test2:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
by (auto intro!: Lambda Application Variable Let)

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down> \<Delta> : z \<Longrightarrow> fst ` set \<Gamma> \<subseteq> fst ` set \<Delta>"
proof(induct rule: reds.induct)
case(Variable v e \<Gamma> \<Delta> z)
  show ?case
  proof
    fix x
    assume "x \<in> fst ` set \<Gamma>"
    then obtain "e'" where "(x, e') \<in> set \<Gamma>" by auto
    show "x \<in> fst ` set ((v, z) # \<Delta>)"
    proof(cases "x = v")
    case True 
      thus ?thesis by simp
    next
    case False
      print_facts
      with `x \<in> fst \` set \<Gamma>`
      have "x \<in> fst ` set (removeAll (v,e) \<Gamma>)" by auto
      hence "x \<in> fst ` set \<Delta>" using Variable.hyps(3) by auto
      thus ?thesis by simp
    qed
  qed
qed (auto)


lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> fst ` (set \<Delta>)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application \<Gamma> e \<Delta> y e' x' \<Theta> z)
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> fst ` (set \<Delta>)" by (auto simp add: exp_assn.fresh fresh_Pair)

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
      thus ?thesis using Application.hyps(4) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair exp_assn.fresh)
      thus ?thesis using Application.hyps(4) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    qed
  next
    assume "x \<in> fst ` (set \<Delta>)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(3)] by auto
  qed
next

case(Variable v e \<Gamma> \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> removeAll (v,e) \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_remove dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> fst ` set \<Delta>"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
  thus ?case using `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Let as \<Gamma> body \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair exp_assn.fresh)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap_induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair exp_assn.fresh)
      show ?thesis
        apply(rule Let.hyps(2))
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair exp_assn.fresh fresh_append)
    next
    case True
      hence "x \<in> fst ` set(asToHeap as)" 
        by(induct as rule:asToHeap_induct)(auto simp add: exp_assn.bn_defs)      
      thus ?thesis using reds_doesnt_forget[OF Let.hyps(1)] by auto
    qed
qed

end

