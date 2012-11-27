theory Heap
imports Terms "Nominal-Utils" "~~/src/HOL/Library/AList"
begin

abbreviation delete where "delete \<equiv> AList.delete"

type_synonym heap = "(var \<times> exp) list"

definition heapVars
  where "heapVars h = fst ` set h"

lemma heapVarsAppend[simp]:"heapVars (a @ b) = heapVars a \<union> heapVars b"
  and [simp]:"heapVars ((v,e) # h) = insert v (heapVars h)"
  and [simp]:"heapVars (p # h) = insert (fst p) (heapVars h)"
  and [simp]:"heapVars [] = {}"
  by (auto simp add: heapVars_def)

lemma heapVars_from_set:
  "(x, e) \<in> set h \<Longrightarrow> x \<in> heapVars h"
by (induct h, auto)

lemma heapVars_not_fresh:
  "x \<in> heapVars \<Gamma> \<Longrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma finite_heapVars[simp]:
  "finite (heapVars \<Gamma>)"
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

lemma fresh_delete:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (delete v \<Gamma>)"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_heap_expr:
  assumes "a \<sharp> \<Gamma>"
  and "(x,e) \<in> set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (metis fresh_list_elem fresh_Pair)

lemma fresh_heap_expr':
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> snd` set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (induct \<Gamma>, auto simp add: fresh_Cons)

lemma fresh_star_heap_expr:
  assumes "S \<sharp>* \<Gamma>"
  and "(x,e) \<in> set \<Gamma>"
  shows "S \<sharp>* e"
  using assms
  by (metis fresh_star_def fresh_heap_expr)

lemma fresh_star_heap_expr':
  assumes "S \<sharp>* \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "S \<sharp>* e"
  using assms
  by (metis fresh_star_def fresh_heap_expr')


inductive distinctVars  where
  [simp]: "distinctVars []" |
  [intro]:"x \<notin> heapVars \<Gamma> \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars ((x, e)  # \<Gamma>)"

lemma [simp]: "distinctVars [x]"
  by (cases x, auto)

lemma heapVars[eqvt]:
  "\<pi> \<bullet> heapVars \<Gamma> = heapVars (\<pi> \<bullet> \<Gamma>)"
  apply (simp add: heapVars_def)
  apply perm_simp
  apply rule
  done

lemma distinctVars_eqvt[eqvt]:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (\<pi> \<bullet> \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply (auto simp add: heapVars[symmetric] mem_permute_iff)
  done

lemma distinctVars_appendI:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta> \<Longrightarrow> heapVars \<Gamma> \<inter> heapVars \<Delta> = {} \<Longrightarrow> distinctVars (\<Gamma> @ \<Delta>)"
  by (induct \<Gamma> rule:distinctVars.induct, auto)


lemma distinctVars_ConsD:
  assumes "distinctVars ((x,e) # \<Gamma>)"
  shows "x \<notin> heapVars \<Gamma>" and "distinctVars \<Gamma>"
  by (rule distinctVars.cases[OF assms], simp_all)+

lemma distinctVars_appendD:
  assumes "distinctVars (\<Gamma> @ \<Delta>)"
  shows distinctVars_appendD1: "distinctVars \<Gamma>"
  and distinctVars_appendD2: "distinctVars \<Delta>"
  and distinctVars_appendD3: "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}"
proof-
  from assms
  have "distinctVars \<Gamma> \<and> distinctVars \<Delta> \<and> heapVars \<Gamma> \<inter> heapVars \<Delta> = {}"
  proof (induct \<Gamma> )
  case Nil thus ?case by simp
  next
  case (Cons p \<Gamma>)
    obtain x e where "p = (x,e)" by (metis PairE)
    with Cons have "distinctVars ((x,e) # (\<Gamma>@ \<Delta>))" by simp
    hence "x \<notin> heapVars (\<Gamma>@ \<Delta>)" and "distinctVars (\<Gamma> @ \<Delta>)" by (rule distinctVars_ConsD)+

    from `x \<notin> heapVars (\<Gamma>@ \<Delta>)` have  "x \<notin> heapVars \<Gamma>"  and "x \<notin> heapVars \<Delta>" by auto

    from Cons(1)[OF `distinctVars (\<Gamma> @ \<Delta>)`]
    have "distinctVars \<Gamma>" and "distinctVars \<Delta>" and "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}" by auto
    have "distinctVars (p # \<Gamma>)"
      using `p = _` `x \<notin> heapVars \<Gamma>` `distinctVars \<Gamma>` by auto
    moreover
    have "heapVars (p # \<Gamma>) \<inter> heapVars \<Delta> = {}" 
      using `p = _` `x \<notin> heapVars \<Delta>` `heapVars \<Gamma> \<inter> heapVars \<Delta> = {}` by auto
    ultimately
    show ?case using `distinctVars \<Delta>` by auto
  qed
  thus "distinctVars \<Gamma>" and "distinctVars \<Delta>" and "heapVars \<Gamma> \<inter> heapVars \<Delta> = {}" by auto
qed

lemma distinctVars_Cons:
  "distinctVars (x # \<Gamma>) \<longleftrightarrow> (fst x \<notin> heapVars \<Gamma> \<and> distinctVars \<Gamma>)"
  by (metis PairE distinctVars.intros(2) distinctVars_ConsD fst_conv)

lemma distinctVars_append:
  "distinctVars (\<Gamma> @ \<Delta>) \<longleftrightarrow> (distinctVars \<Gamma> \<and> distinctVars \<Delta> \<and> heapVars \<Gamma> \<inter> heapVars \<Delta> = {})"
  by (metis distinctVars_appendD distinctVars_appendI)

lemma distinctVars_Cons_subset:
  assumes "heapVars ((x,e)#\<Gamma>) \<subseteq> heapVars ((x,e')#\<Delta>)"
  assumes "distinctVars ((x,e)#\<Gamma>)"
  assumes "distinctVars ((x,e')#\<Delta>)"
  shows "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
proof-
  have "x \<notin> heapVars \<Gamma>" and "x \<notin> heapVars \<Delta>"
    using assms(2,3) by (metis distinctVars_ConsD(1))+
  thus ?thesis using assms(1)
    by auto
qed


lemma delete_no_there:
  "x \<notin> heapVars \<Gamma> \<Longrightarrow> delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_delete_subset:
  "heapVars (delete x \<Gamma>) \<subseteq> heapVars \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_delete[simp]:
  "heapVars (delete x \<Gamma>) = heapVars \<Gamma> - {x}"
  by (induct \<Gamma>, auto)

lemmas fst_set_delete[simp] = heapVars_delete[unfolded heapVars_def]

lemma distinctVars_delete:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (delete x \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply (auto simp add: distinctVars_Cons)
  done

lemma set_bn_to_atom_heapVars:
  "set (bn as) = atom ` heapVars (asToHeap as)"
   apply (induct as rule: asToHeap.induct)
   apply (auto simp add: exp_assn.bn_defs)
   done

lemma fresh_heapVars_distinct:
 assumes "atom ` heapVars \<Delta> \<sharp>* \<Gamma>"
 shows "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> heapVars \<Delta>"
    moreover
    assume "x \<in> heapVars \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      apply (induct \<Gamma>)
      by (auto simp add: supp_Cons heapVars_def supp_Pair supp_at_base)
    ultimately
    have False
      using assms
      by (simp add: fresh_star_def fresh_def)
  }
  thus "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}" by auto
qed

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

lemma the_map_of_snd:
  "x\<in> fst ` set \<Gamma> \<Longrightarrow> the (map_of \<Gamma> x) \<in> snd ` set \<Gamma>"
by (induct \<Gamma>, auto)

end
