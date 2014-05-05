theory Terms
  imports "Nominal-Utils" Vars  "AList-Utils-Nominal"
begin

subsubsection {* Expressions *}

nominal_datatype exp =
  Var "var"
| App "exp" "var"
| LetA as::"assn" body::"exp" binds "bn as" in "body" "as"
| Lam x::"var" body::"exp" binds x in body  ("Lam [_]. _" [100, 100] 100)
and assn =
  ANil | ACons "var" "exp" "assn" 
binder
  bn
where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

notation (latex output) Terms.Var ("_")
notation (latex output) Terms.App ("_ _")
notation (latex output) Terms.LetA ("\<^raw:\textrm{\textsf{let}}> _ \<^raw:\textrm{\textsf{in}}> _")
notation (latex output) Terms.Lam ("\<lambda>_. _"  [100, 100] 100)

abbreviation
  LetBe :: "var\<Rightarrow>exp\<Rightarrow>exp\<Rightarrow>exp" ("let _ be _ in _ " [100,100,100] 100)
where
  "let x be t1 in t2 \<equiv> LetA (ACons x t1 ANil) t2"

type_synonym heap = "(var \<times> exp) list"

subsubsection {* Rewriting in terms of heaps *}

text {*
The nominal package does not allow nested data types, hence the type @{type assn} above. But
@{type assn} is isomorphic to @{type heap}, so at least now it should be possible to re-proof
all resulting lemmas in terms of {@type heap}.
*}

subsubsection {* Conversion from assignments to heaps *}

text {* The type @{typ assn} is the data type used in the let expression. It 
is isomorphic to @{typ "(var \<times> exp) list"}, but since Nominal does not
support nested data type, this redundancy was introduced. The following
function converts between them. Once Nominal supports nested data types, this
could be simplified. *}

text {*
Conversion from @{typ assn} to @{typ heap}.
*}

nominal_primrec asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # asToHeap as"
unfolding eqvt_def asToHeap_graph_aux_def
apply rule
apply simp
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
termination(eqvt) by lexicographic_order
print_theorems

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

text {* The other direction. *}

fun heapToAssn :: "heap \<Rightarrow> assn"
  where "heapToAssn [] = ANil" 
  | "heapToAssn ((v,e)#\<Gamma>) = ACons v e (heapToAssn \<Gamma>)"
declare heapToAssn.simps[simp del]

lemma heapToAssn_eqvt[simp,eqvt]: "p \<bullet> heapToAssn \<Gamma> =  heapToAssn (p \<bullet> \<Gamma>)"
  by (induct \<Gamma> rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma bn_heapToAssn: "bn (heapToAssn \<Gamma>) = map (\<lambda>x. atom (fst x)) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps exp_assn.bn_defs)

lemma set_bn_to_atom_domA:
  "set (bn as) = atom ` domA (asToHeap as)"
   by (induct as rule: asToHeap.induct)
      (auto simp add: exp_assn.bn_defs)

text {*
They are inverse to each other.
*}

lemma heapToAssn_asToHeap[simp]:
  "heapToAssn (asToHeap as) = as"
  by (induct  rule: exp_assn.inducts(2)[of "\<lambda> _ . True"])
     (auto simp add: heapToAssn.simps)

lemma asToHeap_heapToAssn[simp]:
  "asToHeap (heapToAssn as) = as"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma heapToAssn_inject[simp]:
  "heapToAssn x = heapToAssn y \<longleftrightarrow> x = y"
  by (metis asToHeap_heapToAssn)

lemma supp_heapToAssn: "supp (heapToAssn \<Gamma>) = supp \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma supp_asToHeap: "supp (asToHeap as) = supp as"
   by (induct as rule: asToHeap.induct)
      (simp_all add:  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma fv_asToHeap: "fv (asToHeap \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_asToHeap)

lemma fv_heapToAssn: "fv (heapToAssn \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_heapToAssn)

lemma [simp]: "size (heapToAssn \<Gamma>) = list_size (\<lambda> (v,e) . size e) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps)

text {* The Let constructor that we are interested in. *}

definition Let where "Let \<Gamma> e = LetA (heapToAssn \<Gamma>) e"
notation (latex output) Terms.Let ("\<^raw:\textrm{\textsf{let}}> _ \<^raw:\textrm{\textsf{in}}> _")

lemma size_Let[simp]: "size (Let \<Gamma> e) = list_size (\<lambda>p. size (snd p)) \<Gamma> + size e + Suc 0"
  unfolding Let_def by (auto simp add: split_beta')

text {*
Now rewrite all (relevant) lemmas about @{term LetA} in terms of @{term LetB}.
*}
lemma Let_distinct[simp]:
  "Var v \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Var v"
  "App e v \<noteq> Let \<Gamma> e'"
  "Lam [v]. e' \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Lam [v]. e'"
  "Let \<Gamma> e' \<noteq> App e v"
  unfolding Let_def by simp_all

lemma Let_perm_simps[simp,eqvt]:
  "p \<bullet> Let \<Gamma> e = Let (p \<bullet> \<Gamma>) (p \<bullet> e)"
  unfolding Let_def by simp

lemma Let_supp:
  "supp (Let \<Gamma> e) = (supp e \<union> supp \<Gamma>) - atom ` (domA \<Gamma>)"
  unfolding Let_def by (simp add: exp_assn.supp supp_heapToAssn bn_heapToAssn domA_def image_image)

lemma Let_fresh[simp]:
  "a \<sharp> Let \<Gamma> e = (a \<sharp> e \<and> a \<sharp> \<Gamma> \<or> a \<in> atom ` domA \<Gamma>)"
  unfolding fresh_def by (auto simp add: Let_supp)

lemma Abs_eq_cong:
  assumes "\<And> p. (p \<bullet> x = x') \<longleftrightarrow> (p \<bullet> y = y')"
  assumes "supp y = supp x"
  assumes "supp y' = supp x'"
  shows "([a]lst. x = [a']lst. x') \<longleftrightarrow> ([a]lst. y = [a']lst. y')"
  by (simp add: Abs_eq_iff alpha_lst assms)


lemma Let_eq_iff[simp]:
  "(Let \<Gamma> e = Let \<Gamma>' e') = ([map (\<lambda>x. atom (fst x)) \<Gamma> ]lst. (e, \<Gamma>) = [map (\<lambda>x. atom (fst x)) \<Gamma>']lst. (e',\<Gamma>'))"
  unfolding Let_def 
  apply (simp add: bn_heapToAssn)
  apply (rule Abs_eq_cong)
  apply (simp_all add: supp_Pair supp_heapToAssn)
  done

lemma exp_strong_exhaust:
  fixes c :: "'a :: fs"
  assumes "(\<And>var. y = Var var \<Longrightarrow> P)"
  assumes "\<And>exp var. y = App exp var \<Longrightarrow> P"
  assumes "\<And>\<Gamma> exp. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> y = Let \<Gamma> exp \<Longrightarrow> P"
  assumes "\<And>var exp. {atom var} \<sharp>* c \<Longrightarrow> y = Lam [var]. exp \<Longrightarrow> P"
  shows P
  apply (rule  exp_assn.strong_exhaust(1)[where y = y and c = c])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap)
  apply (metis assms(4))
  done

text {*
And finally the induction rules with @{term Let}.
*}

lemma exp_heap_induct[case_names Var App Let Lam Nil Cons]:
  assumes "\<And>var. P1 (Var var)"
  assumes "\<And>exp var. P1 exp \<Longrightarrow> P1 (App exp var)"
  assumes "\<And>\<Gamma> exp. P2 \<Gamma> \<Longrightarrow> P1 exp \<Longrightarrow> P1 (Let \<Gamma> exp)"
  assumes "\<And>var exp. P1 exp \<Longrightarrow> P1 (Lam [var]. exp)"
  assumes "P2 []"
  assumes "\<And>var exp \<Gamma>. P1 exp \<Longrightarrow> P2 \<Gamma> \<Longrightarrow> P2 ((var, exp)#\<Gamma>)"
  shows "P1 e" and "P2 \<Gamma>"
proof-
  have "P1 e" and "P2 (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.inducts[of P1 "\<lambda> assn. P2 (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5) asToHeap.simps(1))
    apply (metis assms(6) asToHeap.simps(2))
    done
  thus "P1 e" and "P2 \<Gamma>" unfolding asToHeap_heapToAssn.
qed

lemma exp_heap_strong_induct[case_names Var App Let Lam Nil Cons]:
  assumes "\<And>var c. P1 c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P1 c exp) \<Longrightarrow> P1 c (App exp var)"
  assumes "\<And>\<Gamma> exp c. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Lam [var]. exp)"
  assumes "\<And>c. P2 c []"
  assumes "\<And>var exp \<Gamma> c. (\<And>c. P1 c exp) \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> P2 c ((var,exp)#\<Gamma>)"
  fixes c :: "'a :: fs"
  shows "P1 c e" and "P2 c \<Gamma>"
proof-
  have "P1 c e" and "P2 c (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.strong_induct[of P1 "\<lambda> c assn. P2 c (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5) asToHeap.simps(1))
    apply (metis assms(6) asToHeap.simps(2))
    done
  thus "P1 c e" and "P2 c \<Gamma>" unfolding asToHeap_heapToAssn.
qed

subsubsection {* Nice induction rules *}

text {*
These rules can be used instead of the original induction rules, which require a separate
goal for @{typ assn}.
*}

lemma exp_induct[case_names Var App Let Lam]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>\<Gamma> exp. (\<And> x. x \<in> domA \<Gamma> \<Longrightarrow>  P (the (map_of \<Gamma> x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let \<Gamma> exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  shows "P  exp"
  apply (rule exp_heap_induct[of P "\<lambda> \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

lemma  exp_strong_induct[case_names Var App Let Lam]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> domA \<Gamma> \<Longrightarrow>  P c (the (map_of \<Gamma> x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_heap_strong_induct(1)[of P "\<lambda> c \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P c (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

subsubsection {* Testing alpha equivalence *}
              
lemma alpha_test:
  shows "Lam [x]. (Var x) = Lam [y]. (Var y)"
  by (simp add: Abs1_eq_iff fresh_at_base)

lemma alpha_test2:
  shows "let x be (Var x) in (Var x) = let y be (Var y) in (Var y)"
  by (simp add: exp_assn.bn_defs Abs1_eq_iff fresh_Pair add: fresh_at_base)

lemma alpha_test3:
  shows "
    Let [(x, Var y), (y, Var x)] (Var x)
    =
    Let [(y, Var x), (x, Var y)] (Var y)" (is "Let ?la ?lb = _")
  apply (simp add: bn_heapToAssn Abs1_eq_iff fresh_Pair fresh_at_base)
  apply (simp add: Abs_swap2[of "atom x" "(?lb, [(x, Var y), (y, Var x)])" "[atom x, atom y]" "atom y"])
done

subsubsection {* Free variables *}

lemma fv_supp_exp: "supp e = atom ` (fv (e::exp) :: var set)" and fv_supp_as: "supp as = atom ` (fv (as::assn) :: var set)"
  by (induction e and as rule:exp_assn.inducts)
     (auto simp add: fv_def exp_assn.supp supp_at_base)

lemma fv_supp_heap: "supp (\<Gamma>::heap) = atom ` (fv \<Gamma> :: var set)"
  by (metis fv_def fv_supp_as supp_heapToAssn)

lemma fv_Lam[simp]: "fv (Lam [x]. e) = fv e - {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp)
lemma fv_Var[simp]: "fv (Var x) = {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_App[simp]: "fv (App e x) = insert x (fv e)"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_Let[simp]: "fv (Let \<Gamma> e) = (fv \<Gamma> \<union> fv e) - domA \<Gamma>"
  unfolding fv_def by (auto simp add: Let_supp exp_assn.supp supp_at_base set_bn_to_atom_domA)

lemma finite_fv_exp[simp]: "finite (fv (e::exp) :: var set)"
  and finite_fv_heap[simp]: "finite (fv (\<Gamma> :: heap) :: var set)"
  by (induction e rule:exp_heap_induct) auto

lemma fv_not_fresh: "atom x \<sharp> e \<longleftrightarrow> x \<notin> fv e"
  unfolding fv_def fresh_def by blast

lemma fv_delete_heap:
  assumes "map_of \<Gamma> x = Some e"
  shows "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> (fv (\<Gamma>, Var x) :: var set)"
proof-
  have "fv (delete x \<Gamma>) \<subseteq> fv \<Gamma>" by (metis fv_delete_subset)
  moreover
  have "(x,e) \<in> set \<Gamma>" by (metis assms map_of_is_SomeD)
  hence "fv e \<subseteq> fv \<Gamma>" by (metis assms domA_from_set map_of_fv_subset the.simps)
  moreover
  have "x \<in> fv (Var x)" by simp
  ultimately show ?thesis by auto
qed

subsubsection {* Substitution *}

fun subst_var :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" ("_[_::v=_]" [1000,100,100] 1000)
where "x[y ::v= z] = (if x = y then z else x)"

lemma subst_var_eqvts[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (subst_var x y z) = subst_var (\<pi> \<bullet> x) (\<pi> \<bullet> y) (\<pi> \<bullet> z)"
by auto


lemma set_delete_subset: "set (delete x l) \<subseteq> set l"
  by (induction l) auto

(*
lemma [simp]:"(a, b) \<in> set (\<Gamma>::heap) \<Longrightarrow> size b < Suc (list_size size \<Gamma> + size body)"
  apply (induct \<Gamma> rule:heapToAssn.induct)
  apply (auto simp add: exp_assn.bn_defs fresh_star_insert dest: set_mp[OF set_delete_subset])
*)

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
                  invariant "\<lambda> a r . (\<forall> as y z . ((a = Inr (as, y, z) \<and> atom ` domA as \<sharp>* (y, z)) \<longrightarrow> map (\<lambda>x . atom (fst x))  (Sum_Type.Projr r) = map (\<lambda>x . atom (fst x)) as))")
  subst :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_::=_]" [1000,100,100] 1000)
and
  subst_heap :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> heap" ("_[_::h=_]" [1000,100,100] 1000)
where
  "(Var x)[y ::= z] = Var (x[y ::v= z])"
 |"(App e v)[y ::= z] = App (e[y ::= z]) (v[y ::v= z])"
 |"atom ` domA as \<sharp>* (y,z) \<Longrightarrow> (Let as body)[y ::= z] = Let (as[y ::h= z]) (body[y ::= z])" 
 |"atom x \<sharp> (y,z) \<Longrightarrow> (Lam [x].e)[y ::= z] = Lam [x].(e[y::=z])"
 |"[][y ::h= z] = []"
 |"((v,e)# as)[y ::h= z] = (v, e[y ::= z])# (as[y ::h= z])"
proof-

have eqvt_at_subst: "\<And> e y z . eqvt_at subst_subst_heap_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst a b c) (e, y, z)"
  apply(simp add: eqvt_at_def subst_def)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inl (e, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
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

have eqvt_at_subst_heap: "\<And> as y z . eqvt_at subst_subst_heap_sumC (Inr (as, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_heap a b c) (as, y, z)"
  apply(simp add: eqvt_at_def subst_heap_def)
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inr (as, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
  apply(assumption)
  apply (metis (mono_tags) Inr_not_Inl)+
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
  unfolding eqvt_def subst_subst_heap_graph_aux_def
  by simp

(* The invariant *)
next case goal2 thus ?case
  by (induct rule: subst_subst_heap_graph.induct)(auto simp add: exp_assn.bn_defs fresh_star_insert)

(* Exhaustiveness *)
next case (goal3 P x) show ?case
  proof(cases x)
  case (Inl a) thus P
    proof(cases a)
    case (fields a1 a2 a3)
    thus P using Inl goal3
      apply (rule_tac y ="a1" and c ="(a2, a3)" in exp_strong_exhaust)
      apply (auto simp add: fresh_star_def)
      apply metis
    done
  qed
  next
  case (Inr a) thus P
    proof (cases a)
    case (fields a1 a2 a3)
    thus P using Inr goal3
      by (metis heapToAssn.cases)
  qed
qed

next case (goal15 e y2 z2 as e2 y z as2) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (drule eqvt_at_subst_heap)+
  apply (simp only: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff]
    meta_eq_to_obj_eq[OF subst_heap_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto simp add: Abs_fresh_iff)
  apply (drule_tac
    c = "(y, z)" and
    as = "(map (\<lambda>x. atom (fst x)) e)" and
    bs = "(map (\<lambda>x. atom (fst x)) e2)" and
    f = "\<lambda> a b c . [a]lst. (subst (fst b) y z, subst_heap (snd b) y z )" in Abs_lst_fcb2)
  apply (simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff)
  apply (metis domA_def image_image image_set)
  apply (metis domA_def image_image image_set)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def)
  done

next case (goal19 x2 y2 z2 e2 x y z e) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (simp only: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (simp add: eqvt_at_def)
  apply rule
  apply (erule_tac x = "(x2 \<leftrightarrow> c)" in allE)
  apply (erule_tac x = "(x \<leftrightarrow> c)" in allE)
  apply auto
  done
}
qed(auto)

termination (eqvt) by lexicographic_order

lemma shows
  True and bn_subst[simp]: "domA (subst_heap as y z) = domA as"
by(induct rule:subst_subst_heap.induct)
  (auto simp add: exp_assn.bn_defs fresh_star_insert)

lemma subst_noop[simp]:
shows "e[y ::= y] = e" and "as[y::h=y]= as"
by(induct e y y and as y y rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs)

lemma subst_is_fresh[simp]:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "atom ` domA as \<sharp>* y \<Longrightarrow> atom y \<sharp> as[y::h=z]"
using assms
by(induct e y z and as y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_at_base fresh_star_Pair fresh_star_insert fresh_Nil fresh_Cons)

lemma
 subst_pres_fresh: "x \<sharp> e \<Longrightarrow> x \<sharp> z \<Longrightarrow> x \<sharp> e[y ::= z]"
and
 "x \<sharp> \<Gamma> \<Longrightarrow> x \<sharp> z \<Longrightarrow> x \<notin> atom ` domA \<Gamma> \<Longrightarrow> x \<sharp> (\<Gamma>[y ::h= z])"
by(induct e y z and \<Gamma> y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs fresh_Cons)

lemma subst_fresh_noop: "atom x \<sharp> e \<Longrightarrow> e[x ::= y] = e"
  and subst_heap_fresh_noop: "atom x \<sharp> \<Gamma> \<Longrightarrow>  \<Gamma>[x ::h= y] = \<Gamma>"
by (nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_def fresh_Pair fresh_at_base fresh_Cons simp del: exp_assn.eq_iff)

lemma supp_subst: "supp (e[y::=x]) \<subseteq> (supp e - {atom y}) \<union> supp x"
proof-
  have "\<And> a. (a \<sharp> e \<or> a = atom y) \<Longrightarrow> a \<sharp> x \<Longrightarrow> a \<sharp> e[y::=x]"
    by (auto intro: subst_pres_fresh)
  thus ?thesis by (auto simp add: fresh_def)
qed

lemma fv_subst_subset: "fv (e[y ::= x]) \<subseteq> (fv e - {y}) \<union> {x}"
proof-
  have "fv (e[y ::= x]) = {v. atom v \<in> supp (e[y ::= x])}" unfolding fv_def..
  also have "\<dots> \<subseteq> {v. atom v \<in> ((supp e - {atom y}) \<union> supp x)}"
    using supp_subst by auto
  also have "\<dots> = (fv e - {y}) \<union> {x}"
    using supp_subst by (auto simp add: fv_def supp_at_base)
  finally show ?thesis.
qed

lemma fresh_star_at_base:
  fixes x :: "'a :: at_base"
  shows "S \<sharp>* x \<longleftrightarrow> atom x \<notin> S"
  by (metis fresh_at_base(2) fresh_star_def)

lemma subst_swap_same: "atom x \<sharp> e \<Longrightarrow>  (x \<leftrightarrow> y) \<bullet> e = e[y ::=x]"
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> \<Gamma> = \<Gamma>[y ::h= x]"
by(nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_Pair fresh_star_at_base fresh_Cons simp del: exp_assn.eq_iff)

lemma subst_subst_back: "atom x \<sharp> e \<Longrightarrow>  e[y::=x][x::=y] = e" 
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y  \<Longrightarrow> \<Gamma>[y::h=x][x::h=y] = \<Gamma>"
by(nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_Pair fresh_star_at_base fresh_star_Cons fresh_Cons  exp_assn.bn_defs simp del: exp_assn.eq_iff)

end
