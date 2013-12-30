theory DistinctVars
imports Main "~~/src/HOL/Library/AList"
begin

abbreviation delete where "delete \<equiv> AList.delete"
abbreviation update where "update \<equiv> AList.update"

lemma delete_append[simp]: "delete x (l1 @ l2) = delete x l1 @ delete x l2"
  unfolding AList.delete_eq by simp

subsubsection {* The domain of a associative list *}

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

lemma finite_heapVars[simp]:
  "finite (heapVars \<Gamma>)"
  by (auto simp add: heapVars_def)

lemma delete_no_there:
  "x \<notin> heapVars \<Gamma> \<Longrightarrow> delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>, auto)

lemma heapVars_delete[simp]:
  "heapVars (delete x \<Gamma>) = heapVars \<Gamma> - {x}"
  by (induct \<Gamma>, auto)


lemma dom_map_of_conv_heapVars:
  "dom (map_of xys) = heapVars xys"
  by (induct xys) (auto simp add: dom_if)


lemma map_of_delete_insert:
  assumes "map_of \<Gamma> x = Some e"
  shows "map_of ((x,e) # delete x \<Gamma>) = map_of \<Gamma>"
  using assms by (induct \<Gamma>) (auto split:prod.split)

lemma map_add_heapVars[simp]: 
  "x \<in> heapVars \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Gamma> x"
  "x \<notin> heapVars \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Delta> x"
    apply (metis dom_map_of_conv_heapVars map_add_dom_app_simps(1))
    apply (metis dom_map_of_conv_heapVars map_add_dom_app_simps(3))
    done

lemma the_map_of_snd:
  "x\<in> heapVars \<Gamma> \<Longrightarrow> the (map_of \<Gamma> x) \<in> snd ` set \<Gamma>"
by (induct \<Gamma>, auto)
end
