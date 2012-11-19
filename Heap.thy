theory Heap
imports Terms "Nominal-Utils"
begin

type_synonym heap = "(var \<times> exp) list"

definition heapVars
  where "heapVars h = fst ` set h"

lemma heapVarsAppend[simp]:"heapVars (a @ b) = heapVars a \<union> heapVars b"
  and [simp]:"heapVars ((v,e) # h) = insert v (heapVars h)"
  and [simp]:"heapVars (p # h) = insert (fst p) (heapVars h)"
  and [simp]:"heapVars [] = {}"
  by (auto simp add: heapVars_def)

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

lemma distinctVars[eqvt]:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (\<pi> \<bullet> \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply (auto simp add: heapVars[symmetric] mem_permute_iff)
  done

lemma removeAll_no_there:
  "x \<notin> heapVars \<Gamma> \<Longrightarrow> removeAll (x,e) \<Gamma> = \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_removeAll_subset:
  "heapVars (removeAll (x,e) \<Gamma>) \<subseteq> heapVars \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_removeAll:
  "distinctVars \<Gamma> \<Longrightarrow> (x,e) \<in> set \<Gamma> \<Longrightarrow> heapVars (removeAll (x,e) \<Gamma>) = heapVars \<Gamma> - {x}"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply auto[1]
  apply (case_tac "(x,e) = (xa,ea)")
  apply (auto simp add: removeAll_no_there intro: set_mp[OF heapVars_removeAll_subset])
  by (metis member_remove removeAll_no_there remove_code(1))

lemma distinctVars_removeAll:
  "distinctVars \<Gamma> \<Longrightarrow> (x,e) \<in> set \<Gamma> \<Longrightarrow> distinctVars (removeAll (x,e) \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply auto[1]
  apply (case_tac "(x,e) = (xa,ea)")
  by (auto simp add: removeAll_no_there heapVars_removeAll)

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

lemma removeAll_stays_fresh:
  "atom x \<sharp> \<Delta> \<Longrightarrow> atom x \<sharp> removeAll (v, e) \<Delta>"
  by (induct \<Delta>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_assn_distinct:
 assumes "set (bn as) \<sharp>* \<Gamma>"
 shows "heapVars (asToHeap as) \<inter> heapVars \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> heapVars (asToHeap as)"
    hence "atom x \<in> set (bn as)"
      apply (induct as rule: asToHeap.induct)
      apply (auto simp add: exp_assn.bn_defs(2))
      done
    hence "atom x \<sharp> \<Gamma>"
      using `set (bn as) \<sharp>* \<Gamma>` by (auto simp add: fresh_star_def)
    moreover
    assume "x \<in> heapVars \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      apply (induct \<Gamma>)
      by (auto simp add: supp_Cons heapVars_def supp_Pair supp_at_base)
    ultimately
    have False
      by (simp add: fresh_def)
  }
  thus "heapVars (asToHeap as) \<inter> heapVars \<Gamma> = {}" by auto
qed

lemma distinctVars_append_asToHeap:
  assumes "distinctVars (asToHeap as)"
  assumes "distinctVars \<Gamma>"
  assumes "set (bn as) \<sharp>* \<Gamma>"
  shows "distinctVars (asToHeap as @ \<Gamma>)" 
by(rule distinctVars_appendI[OF assms(1,2) fresh_assn_distinct[OF assms(3)]])


end
