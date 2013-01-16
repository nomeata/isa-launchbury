theory Terms
  imports Main  "./Nominal/Nominal/Nominal2" 
begin

subsubsection {* Variables (names) and expressions *}

text {*
The type of variables is abstract and provided by the Nominal package. All we know is that it is countable.
*}

atom_decl var

nominal_datatype exp =
  Var "var"
| App "exp" "var"
| Let as::"assn" body::"exp" binds "bn as" in "body" "as"
| Lam x::"var" body::"exp" binds x in body  ("Lam [_]. _" [100, 100] 100)
and assn =
  ANil | ACons "var" "exp" "assn" 
binder
  bn
where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

notation (latex output) Terms.Var ("_")
notation (latex output) Terms.App ("_ _")
notation (latex output) Terms.Let ("\<^raw:\textrm{\textsf{let}}> _ \<^raw:\textrm{\textsf{in}}> _")
notation (latex output) Terms.Lam ("\<lambda>_. _")

abbreviation
  LetBe :: "var\<Rightarrow>exp\<Rightarrow>exp\<Rightarrow>exp" ("let _ be _ in _ " [100,100,100] 100)
where
  "let x be t1 in t2 \<equiv> Let (ACons x t1 ANil) t2"

type_synonym heap = "(var \<times> exp) list"

subsubsection {* Testing alpha equivalence *}
              
lemma alpha_test:
  shows "Lam [x]. (Var x) = Lam [y]. (Var y)"
  by (simp add: Abs1_eq_iff exp_assn.fresh fresh_at_base)

lemma alpha_test2:
  shows "let x be (Var x) in (Var x) = let y be (Var y) in (Var y)"
  by (simp add: exp_assn.bn_defs Abs1_eq_iff fresh_Pair add:exp_assn.fresh fresh_at_base)

lemma alpha_test3:
  shows "
    Let (ACons x (Var y) (ACons y (Var x) ANil)) (Var x)
    =
    Let (ACons y (Var x) (ACons x (Var y) ANil)) (Var y)" (is "Let ?la ?lb = _")
  apply (simp add: exp_assn.bn_defs Abs1_eq_iff fresh_Pair add:exp_assn.fresh fresh_at_base)
  apply (simp add: Abs_swap2[of "atom x" "(?lb,?la)" "[atom x, atom y]" "atom y"])
done

subsubsection {* Substitution *}

fun subst_var :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" ("_[_::v=_]" [1000,100,100] 1000)
where "x[y ::v= z] = (if x = y then z else x)"

lemma subst_var_eqvts[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (subst_var x y z) = subst_var (\<pi> \<bullet> x) (\<pi> \<bullet> y) (\<pi> \<bullet> z)"
by auto

type_synonym sum_type = "exp \<times> var \<times> var + assn \<times> var \<times> var \<Rightarrow> exp + assn"

text {* The Nominal has some issues with mutually recursive definitions and equivariance that we
work around here in a very ugly way, hoping that in later versions of Nominal, this works automatically. *}

definition f1 ::
    "(exp \<times> var \<times> var + assn \<times> var \<times> var \<Rightarrow> exp + assn \<Rightarrow> bool)
 \<Rightarrow> (exp \<times> var \<times> var + assn \<times> var \<times> var \<Rightarrow> exp + assn \<Rightarrow> bool)"
 where "f1 \<equiv>
 (\<lambda>p x1 x2.
                (\<exists> (subst_subst_assn_sum :: sum_type)  x y z. x1 = Inl (Var x, y, z) \<and> x2 = Inl (Var x[y::v=z])) \<or>
                (\<exists>(subst_subst_assn_sum :: sum_type) e v y z.
                    x1 = Inl (App e v, y, z) \<and>
                    x2 = Inl (App (Sum_Type.Projl (subst_subst_assn_sum (Inl (e, y, z)))) (v[y::v=z])) \<and>
                    p (Inl (e, y, z)) (subst_subst_assn_sum (Inl (e, y, z)))) \<or>
                (\<exists> (subst_subst_assn_sum :: sum_type)  as y z body.
                    x1 = Inl (Let as body, y, z) \<and>
                    x2 = Inl (Let (Sum_Type.Projr (subst_subst_assn_sum (Inr (as, y, z))))
                               (Sum_Type.Projl (subst_subst_assn_sum (Inl (body, y, z))))) \<and>
                    set (bn as) \<sharp>* (y, z) \<and>
                    p (Inr (as, y, z)) (subst_subst_assn_sum (Inr (as, y, z))) \<and>
                    p (Inl (body, y, z)) (subst_subst_assn_sum (Inl (body, y, z)))) \<or>
                (\<exists>(subst_subst_assn_sum :: sum_type) x y z e.
                    x1 = Inl (Lam [x]. e, y, z) \<and>
                    x2 = Inl (Lam [x]. Sum_Type.Projl (subst_subst_assn_sum (Inl (e, y, z)))) \<and>
                    atom x \<sharp> (y, z) \<and> p (Inl (e, y, z)) (subst_subst_assn_sum (Inl (e, y, z)))) \<or>
                (\<exists>(subst_subst_assn_sum :: sum_type) y z. x1 = Inr (ANil, y, z) \<and> x2 = Inr ANil) \<or>
                (\<exists>(subst_subst_assn_sum :: sum_type) v e as y z.
                    x1 = Inr (ACons v e as, y, z) \<and>
                    x2 = Inr (ACons v (Sum_Type.Projl (subst_subst_assn_sum (Inl (e, y, z))))
                               (Sum_Type.Projr (subst_subst_assn_sum (Inr (as, y, z))))) \<and>
                    p (Inl (e, y, z)) (subst_subst_assn_sum (Inl (e, y, z))) \<and> p (Inr (as, y, z)) (subst_subst_assn_sum (Inr (as, y, z)))))"

definition f2 ::
  "(exp \<times> var \<times> var + assn \<times> var \<times> var \<Rightarrow> exp + assn \<Rightarrow> bool)
 \<Rightarrow> (exp \<times> var \<times> var + assn \<times> var \<times> var \<Rightarrow> exp + assn \<Rightarrow> bool)"
where "f2 \<equiv>
(\<lambda>p x1 x2.
                    (\<exists> x y z.
                        x1 = Inl (Var x, y, z) \<and> x2 = Inl (Var (x[y::v=z]))) \<or>
                    (\<exists>subst e v y z.
                        x1 = Inl (App e v, y, z) \<and>
                        x2 = Inl (App (subst (e, y, z)) (v[y::v=z])) \<and>
                        p (Inl (e, y, z)) (Inl (subst (e, y, z)))) \<or>
                    (\<exists>subst subst_assn as y z body.
                        x1 = Inl (Let as body, y, z) \<and>
                        x2 =
                        Inl (Let
                              (subst_assn (as, y, z))
                              (subst (body, y, z))) \<and>
                        set (bn as) \<sharp>* (y, z) \<and>
                        p (Inr (as, y, z)) (Inr (subst_assn (as, y, z))) \<and>
                        p (Inl (body, y, z)) (Inl (subst (body, y, z)))) \<or>
                    (\<exists>subst x y z e.
                        x1 = Inl (Lam [x]. e, y, z) \<and>
                        x2 = Inl (Lam [x]. (subst (e, y, z))) \<and>
                        atom x \<sharp> (y, z) \<and>
                        p (Inl (e, y, z)) (Inl (subst (e, y, z)))) \<or>
                    (\<exists> y z. x1 = Inr (ANil, y, z) \<and> x2 = Inr ANil) \<or>
                    (\<exists>subst subst_assn as y z v e.
                        x1 = Inr (ACons v e as, y, z) \<and>
                        x2 =
                        Inr (ACons v (subst (e, y, z))
                              (subst_assn (as, y, z))) \<and>
                        p (Inl (e, y, z)) (Inl (subst (e, y, z))) \<and>
                        p (Inr (as, y, z)) (Inr (subst_assn (as, y, z)))))"


ML {*
fun mono_tac ctxt n =
 EVERY [rtac @{thm monoI} n,
        REPEAT (resolve_tac [@{thm le_funI}, @{thm le_boolI'}] n),
        REPEAT (FIRST
         [atac n,
          resolve_tac (Inductive.get_monos ctxt) n,
          etac @{thm le_funE} n, 
          dtac @{thm le_boolD} n])]
*}

lemma substAltDef:
shows "lfp f1 = lfp f2"
proof-

have "mono f1" unfolding f1_def by (tactic {* mono_tac @{context} 1 *})
have "mono f2" unfolding f2_def by (tactic {* mono_tac @{context} 1 *})

show "lfp f1 = lfp f2"
proof(rule antisym)
  show "lfp f1 \<le> lfp f2"
   apply(rule lfp_induct[OF `mono f1`])
   apply(subst f1_def)
   apply safe
   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]

   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst (asm) lfp_unfold[OF `mono f1`])
   apply (subst f2_def)
   apply (subst (asm) f1_def)
   apply auto[1]

   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]
   apply (rule_tac x = "\<lambda>x . Sum_Type.Projl (subst_subst_assn_sum (Inl x))" in exI)
   apply (rule_tac x = "\<lambda>x . Sum_Type.Projr (subst_subst_assn_sum (Inr x))" in exI)
   apply (rule_tac x = "as" in exI)
   apply (rule_tac x = "body" in exI)
   apply auto[1]
   apply (subst (asm) lfp_unfold[OF `mono f2`])
   apply (subst (asm) f2_def)
   apply auto[1]
   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]
   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]
   apply (subst (asm) (2) lfp_unfold[OF `mono f1`])
   apply (subst (asm) (2) f1_def)
   apply auto[1]

   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]
   apply (rule_tac x = "\<lambda>x . Sum_Type.Projl (subst_subst_assn_sum (Inl x))" in exI)
   apply (rule_tac x = "xa" in exI)
   apply (rule_tac x = "e" in exI)
   apply auto[1]
   apply (subst (asm) lfp_unfold[OF `mono f1`])
   apply (subst (asm) f1_def)
   apply auto[1]

   
   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]

   apply (subst lfp_unfold[OF `mono f2`])
   apply (subst f2_def)
   apply auto[1]
   apply (rule_tac x = "\<lambda>x . Sum_Type.Projl (subst_subst_assn_sum (Inl x))" in exI)
   apply auto[1]
   apply (rule_tac x = "\<lambda>x . Sum_Type.Projr (subst_subst_assn_sum (Inr x))" in exI)
   apply auto[1]
   apply (subst (asm) lfp_unfold[OF `mono f1`])
   apply (subst (asm) f1_def)
   apply auto[1]
   apply (subst (asm) (2) lfp_unfold[OF `mono f1`])
   apply (subst (asm) (2) f1_def)
   apply auto[1]
   done
next
  show "lfp f2 \<le> lfp f1"
  proof(rule lfp_mono)
    fix p
    show "f2 p \<le> f1 p"
      unfolding f2_def f1_def
      apply auto
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "sum_case (Inl \<circ> subst) (Inr \<circ> subst_assn)" in allE, auto)
      apply (erule_tac x = "sum_case (Inl \<circ> subst) (Inr \<circ> subst_assn)" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "Inl \<circ> subst \<circ> Sum_Type.Projl" in allE, auto)
      apply (erule_tac x = "sum_case (Inl \<circ> subst) (Inr \<circ> subst_assn)" in allE, auto)
      apply (erule_tac x = "sum_case (Inl \<circ> subst) (Inr \<circ> subst_assn)" in allE, auto)
      done
  qed
qed
qed

(* Helper lemmas provided by Christian Urban *)

lemma Projl_permute:
  assumes a: "\<exists>y. f = Inl y"
  shows "(p \<bullet> (Sum_Type.Projl f)) = Sum_Type.Projl (p \<bullet> f)"
using a by auto

lemma Projr_permute:
  assumes a: "\<exists>y. f = Inr y"
  shows "(p \<bullet> (Sum_Type.Projr f)) = Sum_Type.Projr (p \<bullet> f)"
using a by auto

nominal_primrec  (default "sum_case (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)",
                  invariant "\<lambda> a r . (\<forall> as y z . ((a = Inr (as, y, z) \<and> set (bn as) \<sharp>* (y, z)) \<longrightarrow> bn (Sum_Type.Projr r) = bn as))")
  subst :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_::=_]" [1000,100,100] 1000)
and
  subst_assn :: "assn \<Rightarrow> var \<Rightarrow> var \<Rightarrow> assn" ("_[_::a=_]" [1000,100,100] 1000)
where
  "(Var x)[y ::= z] = (Var (x[y ::v= z]))"
 |"(App e v)[y ::= z] = (App (e[y ::= z]) (v[y ::v= z]))"
 |"(set (bn as)) \<sharp>* (y,z) \<Longrightarrow> (Let as body)[y ::= z] = Let (subst_assn as y z) (body[y ::= z])" 
 |"(atom x \<sharp> (y,z)) \<Longrightarrow> (Lam [x].e)[y ::= z] = Lam [x].(e[y::=z])"
 |"subst_assn ANil y z = ANil"
 |"subst_assn (ACons v e as) y z = ACons v (e[y ::= z]) (subst_assn as y z)"
proof-

have eqvt_at_subst: "\<And> e y z . eqvt_at subst_subst_assn_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst a b c) (e, y, z)"
  apply(simp add: eqvt_at_def subst_def)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_assn_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_assn_graph (Inl (e, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_assn_graph.cases)
  apply(assumption)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply (metis Inr_not_Inl)
  apply (metis Inr_not_Inl)
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

have eqvt_at_subst_assn: "\<And> as y z . eqvt_at subst_subst_assn_sumC (Inr (as, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_assn a b c) (as, y, z)"
  apply(simp add: eqvt_at_def subst_assn_def)
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_assn_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_assn_graph (Inr (as, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_assn_graph.cases)
  apply(assumption)
  apply (metis Inr_not_Inl)+
  apply(rule_tac x="Sum_Type.Projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: Projr.simps)
  
  apply(rule_tac x="Sum_Type.Projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: Projr.simps)
  
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

{
(* Equivariance of the graph *)
case goal1 thus ?case
  unfolding eqvt_def subst_subst_assn_graph_def
  apply(subst (1 2) substAltDef[unfolded f1_def f2_def]) 
  apply(rule)
  apply perm_simp
  apply rule
done

(* The invariant *)
next case goal2 thus ?case
  by (induct rule: subst_subst_assn_graph.induct)(auto simp add: exp_assn.bn_defs fresh_star_insert)

(* Exhaustiveness *)
next case (goal3 P x) show ?case
  proof(cases x)
  case (Inl a) thus P
    proof(cases a)
    case (fields a1 a2 a3)
    thus P using Inl goal3
      apply (rule_tac y ="a1" and c ="(a2, a3)" in exp_assn.strong_exhaust(1))
      apply (auto simp add: fresh_star_def)
    done
  qed
  next
  case (Inr a) thus P
    proof (cases a)
    case (fields a1 a2 a3)
    thus P using Inr goal3
      apply (rule_tac ya ="a1" in exp_assn.strong_exhaust(2))
      apply (auto)
      apply blast+
    done
  qed
qed

next case (goal15 e y2 z2 as e2 y z as2) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (drule eqvt_at_subst_assn)+
  apply (simp only: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff]
    meta_eq_to_obj_eq[OF subst_assn_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto simp add: Abs_fresh_iff)
  apply (drule_tac
    c = "(y, z)" and
    as = "(bn e)" and
    bs = "(bn e2)" and
    f = "\<lambda> a b c . [a]lst. (subst (fst b) y z, subst_assn (snd b) y z )" in Abs_lst_fcb2)
  apply (auto simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff eqvt_at_def)
  done

next case (goal19 x2 y2 z2 e2 x y z e) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (simp only: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto)
  apply (erule_tac c = "(y, z)" in Abs_lst_fcb2)
  apply (auto simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff eqvt_at_def)
  done
}
qed(auto)

termination (eqvt) by lexicographic_order

lemma shows
  True and bn_subst[simp]: "set (bn as) \<sharp>* (y, z) \<Longrightarrow> bn (subst_assn as y z) = bn as"
by(induct rule:subst_subst_assn.induct)
  (auto simp add: exp_assn.bn_defs fresh_star_insert)


lemma subst_is_fresh[simp]:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "set (bn as) \<sharp>* (y, z) \<Longrightarrow> atom y \<sharp> (subst_assn as y z)"
using assms
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:exp_assn.fresh fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

lemma
 subst_pres_fresh: "(atom x \<sharp> e \<and> atom x \<sharp> z) --> atom x \<sharp> e[y ::= z]"
and
 "(atom x \<sharp> as \<and> atom x \<sharp> z \<and> atom x \<notin> set (bn as)) --> (atom x \<sharp> (subst_assn as y z))"
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:exp_assn.fresh fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

lemma let_binders_fresh[simp]: "set (bn as) \<sharp>* Terms.Let as body"
  by (metis Diff_iff exp_assn.supp(3) finite_supp fresh_finite_atom_set fresh_star_def fresh_star_set fresh_star_supp_conv supp_of_atom_list)

end
