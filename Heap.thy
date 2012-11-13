theory Heap
imports Terms
begin

type_synonym heap = "(var \<times> exp) list"

definition heapVars
  where "heapVars h = fst ` set h"

lemma [simp]:"heapVars (a @ b) = heapVars a \<union> heapVars b"
  and [simp]:"heapVars ((v,e) # h) = insert v (heapVars h)"
  and [simp]:"heapVars [] = {}"
  by (auto simp add: heapVars_def)

function asToHeap_raw :: "assn_raw \<Rightarrow> (var \<times> exp_raw) list"
where ANilToHeap_raw: "asToHeap_raw ANil_raw = []"
 | AConsToHeap_raw: "asToHeap_raw (ACons_raw v e as) = (v, e) # asToHeap_raw as"
 by (pat_completeness, auto)

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

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

lemma fst_set_asToHeap[simp]: "fst ` set (asToHeap as) = assn_vars as"
  by (induct as rule:asToHeap.induct, auto)


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



end
