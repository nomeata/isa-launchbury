theory DistinctVars
imports Main "~~/src/HOL/Library/AList"
begin

text {* We want to have @{text delete} and @{text update} back in the namespace. *}

abbreviation delete where "delete \<equiv> AList.delete"
abbreviation update where "update \<equiv> AList.update"

subsubsection {* The domain of an associative list *}

definition domA
  where "domA h = fst ` set h"

lemma domA_append[simp]:"domA (a @ b) = domA a \<union> domA b"
  and [simp]:"domA ((v,e) # h) = insert v (domA h)"
  and [simp]:"domA (p # h) = insert (fst p) (domA h)"
  and [simp]:"domA [] = {}"
  by (auto simp add: domA_def)

lemma domA_from_set:
  "(x, e) \<in> set h \<Longrightarrow> x \<in> domA h"
by (induct h, auto)

lemma finite_domA[simp]:
  "finite (domA \<Gamma>)"
  by (auto simp add: domA_def)

lemma domA_delete[simp]:
  "domA (delete x \<Gamma>) = domA \<Gamma> - {x}"
  by (induct \<Gamma>, auto)

lemma dom_map_of_conv_domA:
  "dom (map_of \<Gamma>) = domA \<Gamma>"
  by (induct \<Gamma>) (auto simp add: dom_if)

subsubsection {* Other lemmas about associative lists *}

lemma delete_append[simp]: "delete x (l1 @ l2) = delete x l1 @ delete x l2"
  unfolding AList.delete_eq by simp

lemma map_of_delete_insert:
  assumes "map_of \<Gamma> x = Some e"
  shows "map_of ((x,e) # delete x \<Gamma>) = map_of \<Gamma>"
  using assms by (induct \<Gamma>) (auto split:prod.split)

lemma map_add_domA[simp]: 
  "x \<in> domA \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Gamma> x"
  "x \<notin> domA \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Delta> x"
    apply (metis dom_map_of_conv_domA map_add_dom_app_simps(1))
    apply (metis dom_map_of_conv_domA map_add_dom_app_simps(3))
    done

end
