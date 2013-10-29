theory Heap
imports Terms "DistinctVars-Nominal" "Nominal-Utils"
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

lemma set_bn_to_atom_heapVars:
  "set (bn as) = atom ` heapVars (asToHeap as)"
   apply (induct as rule: asToHeap.induct)
   apply (auto simp add: exp_assn.bn_defs)
   done

lemma fresh_assn_distinct:
 assumes "set (bn as) \<sharp>* \<Gamma>"
 shows "heapVars (asToHeap as) \<inter> heapVars \<Gamma> = {}"
 using assms
by (metis set_bn_to_atom_heapVars fresh_heapVars_distinct)

lemma distinctVars_asToHeap[simp]: "distinctVars (asToHeap as)"
   by (induct as rule: asToHeap.induct)(auto simp add: distinctVars_Cons distinctVars_delete)

lemma distinctVars_append_asToHeap:
  assumes "distinctVars \<Gamma>"
  assumes "set (bn as) \<sharp>* \<Gamma>"
  shows "distinctVars (asToHeap as @ \<Gamma>)" 
by(rule distinctVars_appendI[OF distinctVars_asToHeap assms(1) fresh_assn_distinct[OF assms(2)]])

lemma set_delete_subset: "set (delete x l) \<subseteq> set l"
  by (induction l) auto

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by (induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert dest: set_mp[OF set_delete_subset])

subsubsection {* Nicer induction rule for expressions *}

lemma exp_induct[case_names Var App Let Lam]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>assn exp. (\<And> x. x \<in> heapVars (asToHeap assn) \<Longrightarrow>  P (the (map_of (asToHeap assn) x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let assn exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  shows "P  exp"
  apply (rule exp_assn.inducts(1)[of P "\<lambda> assn. (\<forall>x \<in> heapVars (asToHeap assn). P (the (map_of (asToHeap assn) x)))"])
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
    set (bn assn) \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> heapVars (asToHeap assn) \<Longrightarrow>  P c (the (map_of (asToHeap assn) x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Terms.Let assn exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_assn.strong_induct(1)[of P "\<lambda> c assn. (\<forall>x \<in> heapVars (asToHeap assn). P c (the (map_of (asToHeap assn) x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

end
