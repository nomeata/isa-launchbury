theory "AList-Utils"
imports Main "Library/AList"
begin

text {* We want to have @{text delete} and @{text update} back in the namespace. *}

abbreviation delete where "delete \<equiv> AList.delete"
abbreviation update where "update \<equiv> AList.update"
abbreviation restrictA where "restrictA \<equiv> AList.restrict"
abbreviation clearjunk where "clearjunk \<equiv> AList.clearjunk"

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
  by (induct \<Gamma>) auto

lemma domA_restrictA[simp]:
  "domA (restrictA S \<Gamma>) = domA \<Gamma> \<inter> S"
  by (induct \<Gamma>) auto

lemma delete_not_domA[simp]:
  "x \<notin> domA \<Gamma> \<Longrightarrow>  delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>) auto

lemma dom_map_of_conv_domA:
  "dom (map_of \<Gamma>) = domA \<Gamma>"
  by (induct \<Gamma>) (auto simp add: dom_if)

lemma domA_map_of_Some_the:
  "x \<in> domA \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some (the (map_of \<Gamma> x))"
  by (induct \<Gamma>) (auto simp add: dom_if)

lemma domA_clearjunk[simp]: "domA (clearjunk \<Gamma>) = domA \<Gamma>"
  unfolding domA_def using dom_clearjunk.

subsubsection {* Other lemmas about associative lists *}

lemma delete_set_none: "(map_of l)(x := None) = map_of (delete x l)"
proof (induct l)
  case Nil thus ?case by simp
  case (Cons l ls)
  from this[symmetric]
  show ?case
  by (cases "fst l = x") auto
qed

lemma list_size_delete[simp]: "size_list size (delete x l) < Suc (size_list size l)"
  by (induct l) auto

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

lemma map_of_empty[simp]:
  "Map.empty = map_of \<Delta> \<longleftrightarrow> \<Delta> = []"
  apply (cases \<Delta>)
  apply auto
  by (metis fun_upd_same option.distinct(1))

lemma dom_delete_subset: "snd ` set (delete k al) \<subseteq> snd ` set al"
  by (auto simp add: delete_eq)

(*
lemma ran_map_cong[fundef_cong]:
  "\<lbrakk> list_all2 (\<lambda> x y. fst x = fst y \<and> f1 (fst x) (snd x) = f2 (fst y) (snd y)) m1 m2 \<rbrakk>
      \<Longrightarrow> map_ran f1 m1 = map_ran f2 m2"    
  by (induction rule: list_all2_induct) auto
*)
lemma ran_map_cong[fundef_cong]:
  "\<lbrakk> \<And> x . x \<in> set m1 \<Longrightarrow> f1 (fst x) (snd x) = f2 (fst x) (snd x) ; m1 = m2 \<rbrakk>
      \<Longrightarrow> map_ran f1 m1 = map_ran f2 m2"    
  by (induction m1 arbitrary: m2) auto

lemma domA_map_ran[simp]: "domA (map_ran f m) = domA m"
  unfolding domA_def by (rule dom_map_ran)

end
