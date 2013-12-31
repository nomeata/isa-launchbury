theory Heap
imports Terms "AList-Utils-Nominal" "Nominal-Utils"
begin

subsubsection {* Conversion from assignments to heaps *}

text {* The type @{typ assn} is the data type used in the let expression. It 
is isomorphic to @{typ "(var \<times> exp) list"}, but since Nominal does not
support nested data type, this redundancy was introduced. The following
function converts between them. Once Nominal supports nested data types, this
could be simplified. *}

nominal_primrec asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # delete v (asToHeap as)"
unfolding eqvt_def asToHeap_graph_aux_def
apply rule
apply simp
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
termination(eqvt) by lexicographic_order

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

lemma set_bn_to_atom_domA:
  "set (bn as) = atom ` domA (asToHeap as)"
   apply (induct as rule: asToHeap.induct)
   apply (auto simp add: exp_assn.bn_defs)
   done

lemma set_delete_subset: "set (delete x l) \<subseteq> set l"
  by (induction l) auto

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

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by (induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert dest: set_mp[OF set_delete_subset])

lemma True and fv_asToHeap: "fv (asToHeap as) \<subseteq> fv as"
  apply (induct and as rule:exp_assn.inducts)
  apply (auto simp add: fv_def exp_assn.supp supp_Nil supp_at_base supp_Cons supp_Pair)
  by (metis (lifting) mem_Collect_eq set_delete_subset set_supp_mono subsetD)

lemma fv_Let[simp]: "fv (Let as e) = (fv as \<union> fv e) - domA (asToHeap as)"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base set_bn_to_atom_domA)

lemma fv_ANil[simp]: "fv ANil = {}"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_ACons[simp]: "fv (ACons x e as) = insert x (fv e \<union> fv as)"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)

lemma finite_fv_exp[simp]: "finite (fv (e::exp) :: var set)" and finite_fv_as[simp]: "finite (fv (as::assn) :: var set)"
  by (induction e and as rule:exp_assn.inducts) auto

lemma finite_fv_heap[simp]: "finite (fv (\<Gamma>::heap) :: var set)"
  by (induction \<Gamma>) auto

subsubsection {* Nicer induction rule for expressions *}

lemma exp_induct[case_names Var App Let Lam]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>assn exp. (\<And> x. x \<in> domA (asToHeap assn) \<Longrightarrow>  P (the (map_of (asToHeap assn) x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let assn exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  shows "P  exp"
  apply (rule exp_assn.inducts(1)[of P "\<lambda> assn. (\<forall>x \<in> domA (asToHeap assn). P (the (map_of (asToHeap assn) x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

lemma  exp_strong_induct[case_names Var App Let Lam]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>assn exp c.
    set (bn assn) \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> domA (asToHeap assn) \<Longrightarrow>  P c (the (map_of (asToHeap assn) x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Terms.Let assn exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_assn.strong_induct(1)[of P "\<lambda> c assn. (\<forall>x \<in> domA (asToHeap assn). P c (the (map_of (asToHeap assn) x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

end
