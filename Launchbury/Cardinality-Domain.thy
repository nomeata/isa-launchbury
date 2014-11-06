theory "Cardinality-Domain"
imports "HOLCF-Utils"
begin

type_synonym oneShot = "one"
abbreviation notOneShot :: oneShot where "notOneShot \<equiv> ONE"
abbreviation oneShot :: oneShot where "oneShot \<equiv> \<bottom>"

type_synonym two = "oneShot\<^sub>\<bottom>"
abbreviation many :: two where "many \<equiv> up\<cdot>notOneShot"
abbreviation once :: two where "once \<equiv> up\<cdot>oneShot"
abbreviation none :: two where "none \<equiv> \<bottom>"

lemma two_conj: "c = many \<or> c = once \<or> c = none" by (metis Exh_Up one_neq_iffs(1))

lemma two_cases[case_names many once none]:
  obtains "c = many" | "c = once" | "c = none" using two_conj by metis

definition two_pred where "two_pred = (\<Lambda> x. if x \<sqsubseteq> once then \<bottom> else x)"

lemma two_pred_simp: "two_pred\<cdot>c = (if c \<sqsubseteq> once then \<bottom> else c)"
  unfolding two_pred_def
  apply (rule beta_cfun)
  apply (rule cont_if_else_above)
  apply (auto elim: below_trans)
  done

lemma two_pred_below_arg: "two_pred \<cdot> f \<sqsubseteq> f"
  by (auto simp add: two_pred_simp)

lemma two_pred_none: "two_pred\<cdot>c = none \<longleftrightarrow> c \<sqsubseteq> once"
  by (auto simp add: two_pred_simp)

definition record_call where "record_call x = (\<Lambda> ce. (\<lambda> y. if x = y then two_pred\<cdot>(ce y) else ce y))"

lemma record_call[simp]: "(record_call x \<cdot> f) x = two_pred \<cdot> (f x)"
  unfolding record_call_def by auto

lemma record_call_below_arg: "record_call x \<cdot> f \<sqsubseteq> f"
  unfolding record_call_def
  by (auto intro!: fun_belowI two_pred_below_arg)



end
