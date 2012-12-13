theory Heap
imports Terms DistinctVars "Nominal-Utils" "~~/src/HOL/Library/AList"
begin


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

lemma heapVars_asToHeap[simp]: "heapVars (asToHeap as) = assn_vars as"
  by (induct as rule:asToHeap.induct, auto)

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

lemma distinctVars_append_asToHeap:
  assumes "distinctVars (asToHeap as)"
  assumes "distinctVars \<Gamma>"
  assumes "set (bn as) \<sharp>* \<Gamma>"
  shows "distinctVars (asToHeap as @ \<Gamma>)" 
by(rule distinctVars_appendI[OF assms(1,2) fresh_assn_distinct[OF assms(3)]])


end
