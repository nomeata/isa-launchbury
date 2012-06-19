theory Launchbury
imports Terms
begin

type_synonym heap = "(var \<times> exp) list"


lemma fun_upd[eqvt]: "p \<bullet> (fun_upd f x y) = fun_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
by  (auto simp add:permute_fun_def fun_eq_iff)

lemma fresh_upd[intro]:
  assumes "atom x \<sharp> \<Gamma>(y := None)" and "atom x \<sharp> e"
  shows "atom x \<sharp> \<Gamma>(y \<mapsto> e)"
sorry

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


inductive reds :: "heap \<Rightarrow> exp \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" ("_ : _ \<Down> _ : _" [50,50,50,50] 50)
where
  Lambda: "\<Gamma> : (Lam [x]. e) \<Down> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>  \<Gamma> : e \<Down> \<Delta> : (Lam [y]. e') ; \<Delta> : e'[y ::= x] \<Down> \<Theta> : z\<rbrakk> \<Longrightarrow> \<Gamma> : App e x \<Down> \<Theta> : z" 
 | Variable: "\<lbrakk> (x,e) \<in> set \<Gamma>; removeAll (x, e) \<Gamma> : e \<Down> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : Var x \<Down> (x, z) # \<Delta> : z"
 | LetANil: "\<Gamma> : body \<Down> \<Delta> : z \<Longrightarrow> \<Gamma> : (Let ANil body) \<Down> \<Delta> : z"
 | LetACons: "\<lbrakk>  (v, e) # \<Gamma> : Let as body \<Down> \<Delta> : z \<rbrakk> \<Longrightarrow> \<Gamma> : (Let (ACons v e as) body) \<Down> \<Delta> : z"

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
apply(auto intro!: Lambda Application Variable LetANil LetACons
 simp add: fresh_Pair fresh_Cons fresh_Nil exp_assn.fresh)
done

lemma eval_test2:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
by (auto intro!: Lambda Application Variable LetANil LetACons)

lemma reds_fresh:"
  \<lbrakk> \<Gamma> : e \<Down> \<Delta> : z;
  atom (x::var) \<sharp> (\<Gamma>, e);
  x \<notin> fst ` (set \<Gamma>)
  \<rbrakk> \<Longrightarrow> (atom x \<sharp> (\<Delta>, z) \<and> x \<notin> fst ` (set \<Delta>))"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case ..
next
case (Application \<Gamma> e \<Delta> y e' x' \<Theta> z)
  have "atom x \<sharp> \<Gamma>" "atom x \<sharp> e" "atom x \<sharp> x'" using Application.prems(1) by (auto simp add: exp_assn.fresh fresh_Pair)  
  hence "atom x \<sharp> \<Delta>" "atom x \<sharp> (Lam [y]. e')" "x \<notin> fst ` (set \<Delta>) " using Application.hyps(2) Application.prems(2) by auto
  show ?case
  proof(cases "x = y")
    case False
      (* Can be solved directly:
      show "atom x \<sharp> (\<Theta>, z)" using Application False by (auto simp add:exp_assn.fresh fresh_Pair  subst_pres_fresh[rule_format])
      *)
      hence "atom x \<sharp> e'" using `atom x \<sharp> (Lam [y]. e')` by (auto simp add: exp_assn.fresh)
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> x'` by (auto intro: subst_pres_fresh[rule_format])
      thus ?thesis using Application.hyps(4) `atom x \<sharp> \<Delta>` `x \<notin> fst \` (set \<Delta>)` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using  `atom x \<sharp> x'` by (auto intro: subst_is_fresh)
      thus ?thesis using Application.hyps(4) `atom x \<sharp> \<Delta>` `x \<notin> fst \` (set \<Delta>)` by auto
  qed
next

case(Variable v e \<Gamma> \<Delta> z)
  print_facts
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair exp_assn.fresh)
  hence "atom x \<sharp> removeAll (v,e) \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_remove dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z)" and "x \<notin> fst ` (set \<Delta>)" using Variable.hyps(3) Variable.prems(2) by (auto simp add: fresh_Pair)
  thus ?case using `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case(LetANil \<Gamma> body \<Delta> z)
  thus ?case by (auto simp add: exp_assn.fresh fresh_Pair exp_assn.bn_defs)

next
case(LetACons v e \<Gamma> as body \<Delta> z)
  hence  "atom x \<sharp> \<Gamma>" and "atom x \<sharp> Let (ACons v e as) body" by (auto simp add: fresh_Pair)
  
  show ?case
  proof(cases "atom x \<in> set (bn (ACons v e as))")
    thm exp_assn.fresh
    case False
      hence "atom x \<sharp> v" and "atom x \<sharp> e" and "atom x \<sharp> as" and "atom x \<sharp> body"
        using `atom x \<sharp> Let (ACons v e as) body`
        by (auto simp add: exp_assn.fresh exp_assn.bn_defs)
      thus ?thesis
        apply -
        apply (rule LetACons.hyps(2))
        using `atom x \<sharp> \<Gamma>` and LetACons.prems(2)
        by (auto simp add: fresh_Pair fresh_Cons  exp_assn.fresh fresh_at_base)
    next
    case True
      print_facts
      show ?thesis sorry
    qed
qed

end

