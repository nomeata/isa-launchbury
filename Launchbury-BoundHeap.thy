theory "Launchbury-BoundHeap"
imports Terms
begin

(* type_synonym heap = "(var \<times> exp) list" *)

nominal_datatype 
heapexp = Heap heap::heap body::exp binds "hbn heap" in heap body  (infix ".:." 60) 
and
heap =  HNil | HCons var exp heap ("'(_ \<mapsto> _') ## _" [65,65,65] 65)
binder
  hbn
where "hbn HNil = []" | "hbn (HCons x t h) = (atom x) # (hbn h)"

function elemLookup :: "heap \<Rightarrow> var \<Rightarrow> exp option" (infix "\<cdot>" 62)
  where
    "HNil \<cdot> x = None"
    | "(v \<mapsto> e) ## h \<cdot> x = (if x = v then Some e else h \<cdot> x)"
apply(case_tac x)
apply(case_tac a rule: heapexp_heap.exhaust(2))
apply auto
done
termination by lexicographic_order

lemma elemLookup_eqvt[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (h \<cdot> x) = (\<pi> \<bullet> h) \<cdot> (\<pi> \<bullet> x)"
by(induct h x rule:elemLookup.induct) (auto simp add:elemLookup.simps)


function removeHeap :: "heap \<Rightarrow> var \<Rightarrow> heap" ("_ with _ removed" [80,80] 80)
where "HNil with x removed = HNil"
| "((v \<mapsto> e) ## h) with x removed = (if v = x then h with x removed else (v \<mapsto> e) ## h with x removed)"
apply(case_tac x)
apply(case_tac a rule: heapexp_heap.exhaust(2))
apply auto
done
termination by lexicographic_order

lemma removeHeap_eqvt[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (removeHeap x y) = removeHeap (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
by(induct x y rule:removeHeap.induct) (auto simp add:removeHeap.simps)

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

lemma fresh_removeHeap:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> \<Gamma> with v removed"
using assms
by(induct \<Gamma> v rule:removeHeap.induct)(auto simp add: heapexp_heap.fresh)

lemma fresh_list_elem:
  assumes "atom x \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "atom x \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_heap_elem:
  assumes "atom x \<sharp> \<Gamma>"
  and "\<Gamma> \<cdot> v = Some e"
  shows "atom x \<sharp> e"
using assms
by(induct \<Gamma> v rule:elemLookup.induct)(auto simp add: heapexp_heap.fresh split_if_eq1)

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


inductive reds :: "heapexp \<Rightarrow> heapexp \<Rightarrow> bool" ("_ \<Down> _" [50,50] 50)
where
  Lambda: "\<Gamma> .:. (Lam [x]. e) \<Down> \<Gamma> .:. (Lam [x]. e)" 
 | Application: "\<lbrakk> atom y \<sharp> \<Gamma> .:. App e x; \<Gamma> .:. e \<Down> \<Delta> .:. (Lam [y]. e') ; \<Delta> .:. e'[y ::= x] \<Down> \<Theta> .:. z; atom y \<sharp> \<Theta> .:. z\<rbrakk> \<Longrightarrow> \<Gamma> .:. App e x \<Down> \<Theta> .:. z" 
 | Variable: "\<lbrakk>\<Gamma> \<cdot> x = Some e; \<Gamma> with x removed .:. e \<Down> \<Delta> .:. z \<rbrakk> \<Longrightarrow> \<Gamma> .:. Var x \<Down> (x \<mapsto> z) ## \<Delta> .:. z"
 | LetANil: "\<Gamma> .:. body \<Down> \<Delta> .:. z \<Longrightarrow> \<Gamma> .:. (Let ANil body) \<Down> \<Delta> .:. z"
 | LetACons: "(v \<mapsto> e) ## \<Gamma> .:. Let as body \<Down> \<Delta> .:. z \<Longrightarrow> \<Gamma> .:. (Let (ACons v e as) body) \<Down> \<Delta> .:. z"

equivariance reds

nominal_inductive reds
  avoids Application: "y"
  by (auto simp add: fresh_star_def fresh_Pair exp_assn.fresh)

thm reds2.strong_induct

lemma eval_test1:
  "HNil .:. (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down> (x \<mapsto> Lam [y]. Var y) ## HNil .:. (Lam [y]. Var y)"
by (auto intro!: Lambda Application Variable LetANil LetACons)

lemma eval_test2:
  "HNil .:. (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down> (x \<mapsto> Lam [y]. Var y) ## HNil .:. (Lam [y]. Var y)"
by (auto intro!: Lambda Application Variable LetANil LetACons
         simp add:heapexp_heap.fresh heapexp_heap.bn_defs exp_assn.fresh fresh_at_base)

(*
lemma red_doesn_forget:"\<Gamma> .:. e \<Down>2 \<Delta> .:. z  \<Longrightarrow> set (hbn \<Gamma>) \<subseteq> set (hbn \<Delta>)"
thm reds2.induct
thm reds2.strong_induct
proof(induct "(\<Gamma> .:. e)" "(\<Delta> .:. z)" rule:reds2.induct)
case (Lambda2 \<Gamma>' x e')
  thus ?case 
  apply simp

case (Application2 \<Gamma> e \<Delta> y e' x' \<Theta> z)
  
  thus ?case by auto

apply_end(auto)

qed
*)

lemma reds2_fresh:"\<lbrakk> he1 \<Down> he2 ; atom (x::var) \<sharp> he1 \<rbrakk> \<Longrightarrow> atom x \<sharp> he2"
proof(nominal_induct he1 he2 avoiding: x rule: reds.strong_induct)
case (Application y \<Gamma> e x' \<Delta> e' \<Theta> z x)
  show ?case
  proof(cases "atom x \<sharp> x'")
    case True 
      have "atom x \<sharp> \<Gamma> .:. e"
      proof(cases "atom x \<in> set (hbn \<Gamma>)")
        case False
          hence "atom x \<sharp> \<Gamma>" "atom x \<sharp> e"  "atom x \<sharp> x'" using `atom x \<sharp> \<Gamma> .:. App e x'` 
            by (auto simp add: exp_assn.fresh fresh_Pair heapexp_heap.fresh)
          thus ?thesis by (auto simp add: heapexp_heap.fresh)
        next
        case True thus ?thesis by (auto simp add: heapexp_heap.fresh)
      qed
      hence "atom x \<sharp> \<Delta> .:. Lam [y]. e'" using Application.hyps(4) by auto
    
      have "atom x \<sharp> \<Delta> .:. e'[y ::= x']"
      proof(cases "atom x \<in> set (hbn \<Delta>)")
        case False
          hence "atom x \<sharp> \<Delta>" and "atom x \<sharp> (Lam [y]. e')" using `atom x \<sharp> \<Delta> .:. _` by (auto simp add: heapexp_heap.fresh)   
          hence "atom x \<sharp> e'" using `atom y \<sharp> x`  by (auto simp add: exp_assn.fresh fresh_at_base)
          hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> x'` by (auto intro: subst_pres_fresh[rule_format])
          thus ?thesis using `atom x \<sharp> \<Delta>` by (auto simp add: heapexp_heap.fresh)
        next
        case True thus ?thesis by (auto simp add: heapexp_heap.fresh)
      qed
    thus "atom x \<sharp> \<Theta> .:. z" using Application.hyps(6) by auto
  next
  case False 
    hence "x = x'" by (simp add:fresh_at_base)
    hence "atom x \<in> set (hbn \<Gamma>)" using `atom x \<sharp> \<Gamma> .:. App e x'`  False
      by (auto simp add: exp_assn.fresh fresh_Pair heapexp_heap.fresh)
    hence "atom x \<sharp> \<Gamma> .:. e"  by (auto simp add: heapexp_heap.fresh)
    hence "atom x \<sharp> \<Delta> .:. Lam [y]. e'" using Application.hyps(4) by auto

    (* Hier ists kaputt *)
    thus ?thesis sorry
  qed
next

oops

end

