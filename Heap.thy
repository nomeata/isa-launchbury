theory Heap
imports Terms
begin

type_synonym heap = "(var \<times> exp) list"

definition heapVars
  where "heapVars h = fst ` set h"

lemma [simp]:"heapVars (a @ b) = heapVars a \<union> heapVars b"
  and [simp]:"heapVars ((v,e) # h) = insert v (heapVars h)"
  by (auto simp add: heapVars_def)

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
by(induct as rule:asToHeap.induct) (auto)

end
