theory Env
  imports Main HOLCF
begin

default_sort type

subsubsection {* The type of finite maps *}

definition fdom :: "('key \<Rightarrow> 'value::pcpo) \<Rightarrow> 'key set" where "fdom m = {x. m x \<noteq> \<bottom>}"

lemma fempty_fdom[simp]: "fdom \<bottom> = {}" by (simp add: fdom_def)

lemma fempty_fdom2[simp]: "fdom (\<lambda>_ . \<bottom>) = {}" by (simp add: fdom_def)

lemma fdomIff: "(a \<in> fdom m) = (m a \<noteq> \<bottom>)" by (simp add: fdom_def)

lemma lookup_not_fdom: "x \<notin> fdom m \<Longrightarrow> m x = \<bottom>"  by (auto iff:fdomIff)

lemma lookup_fdom[simp]: "m x \<noteq> \<bottom> \<Longrightarrow> x \<in> fdom m"  by (auto iff:fdomIff)

subsubsection {* Updates *}

lemma fdom_fun_upd_subset: "fdom (h (x := v)) \<subseteq> insert x (fdom h)"
  by (auto simp add: fdom_def)

declare fun_upd_same[simp] fun_upd_other[simp]

subsubsection {* Restriction *}

definition fmap_restr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "fmap_restr S m = (\<lambda> x. if x \<in> S then m x else \<bottom>)"

abbreviation fmap_restr_rev  (infixl "f|`"  110) where "fmap_restr_rev m S \<equiv> fmap_restr S m"

notation (latex output) fmap_restr_rev ("_|\<^bsub>_\<^esub>")

lemma fmap_restr_empty[simp]: "fdom m \<inter> S = {} \<Longrightarrow> m f|` S = \<bottom>"
  by (fastforce simp add: fdom_def fmap_restr_def)

lemma lookup_fmap_restr[simp]: "x \<in> S \<Longrightarrow> (fmap_restr S m) x = m x"
  by (fastforce simp add: fmap_restr_def)

lemma lookup_fmap_restr_not_there[simp]: "x \<notin> S \<Longrightarrow> (fmap_restr S m) x = \<bottom>"
  by (fastforce simp add: fmap_restr_def)

lemma lookup_fmap_restr_eq: "(m f|` S) x = (if x \<in> S then m x else \<bottom>)"
  by simp

lemma fmap_restr_cong: "fdom m \<inter> S1 = fdom m \<inter> S2 \<Longrightarrow> m f|` S1 = m f|` S2"
  apply (rule ext)
  apply (simp add: lookup_fmap_restr_eq)
  by (metis Int_iff lookup_not_fdom)

lemma fmap_restr_fmap_restr[simp]:
 "x f|` d2 f|` d1 = x f|` (d1 \<inter> d2)"
  by (fastforce simp add: fmap_restr_def)

lemma fmap_restr_fmap_restr_subset:
 "d1 \<subseteq> d2 \<Longrightarrow> x f|` d2 f|` d1 = x f|` d1"
 by (metis Int_absorb2 fmap_restr_fmap_restr)

lemma fmap_restr_useless: "fdom m \<subseteq> S \<Longrightarrow> m f|` S = m"
  by (rule ext) (auto simp add: lookup_fmap_restr_eq dest!: set_mp)

lemma fmap_restr_UNIV[simp]: "m f|` UNIV = m"
  by (rule fmap_restr_useless) simp

lemma fmap_restr_fun_upd[simp]: "x \<in> S \<Longrightarrow> m1(x := v) f|` S = (m1 f|` S)(x := v)"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_fmap_restr_eq)
  done

lemma fmap_restr_fun_upd_other[simp]: "x \<notin> S \<Longrightarrow> m1(x := v) f|` S = m1 f|` S"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_fmap_restr_eq)
  done

lemma fmap_restr_eq_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' = m2 f|` S'"
  shows "m1 f|` S = m2 f|` S"
using assms
by (metis fmap_restr_fmap_restr le_iff_inf)

subsubsection {* Deleting *}

definition fmap_delete :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::pcpo)"
  where "fmap_delete x m = m(x := \<bottom>)"

lemma lookup_fmap_delete[simp]:
  "x' \<noteq> x \<Longrightarrow> fmap_delete x m x' = m x'"
  by (simp add: fmap_delete_def)

lemma lookup_fmap_delete_None[simp]:
  "fmap_delete x m x = \<bottom>"
  by (simp add: fmap_delete_def)

lemma fdom_fmap_delete[simp]:
  "fdom (fmap_delete x m) = fdom m - {x}"
  by (auto simp add: fmap_delete_def fdom_def)

lemma fdom_fmap_delete_subset:
  "fdom (fmap_delete x m) \<subseteq> fdom m" by auto

lemma fmap_delete_fun_upd[simp]:
  "fmap_delete x (m(x := v)) = fmap_delete x m"
  by (auto simp add: fmap_delete_def)

lemma fmap_delete_fun_upd2[simp]:
  "(fmap_delete x m)(x := v) = m(x := v)"
  by (auto simp add: fmap_delete_def)

lemma fmap_delete_fun_upd3[simp]:
  "x \<noteq> y \<Longrightarrow> fmap_delete x (m(y := v)) = (fmap_delete x m)(y := v)"
  by (auto simp add: fmap_delete_def)

lemma fmap_delete_noop[simp]:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (auto simp add: fmap_delete_def fdom_def)

lemma fun_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> (fmap_delete x \<Gamma>)(x := \<Gamma> x) = \<Gamma>"
  by (auto)

lemma fmap_restr_fmap_delete_other[simp]: "x \<notin> S \<Longrightarrow> fmap_delete x m f|` S = m f|` S"
  apply (rule ext)
  apply (auto simp add: lookup_fmap_restr_eq)
  by (metis lookup_fmap_delete)

lemma fmap_delete_restr: "fmap_delete x m = m f|` (-{x})"
  by (auto simp add: lookup_fmap_restr_eq)

subsubsection {* Merging of two functions *}

text {*
We'd like to have some nice syntax for @{term "override_on"}.
*}

abbreviation override_on_syn ("_ ++\<^bsub>_\<^esub> _" [100, 0, 100] 100) where "f1 ++\<^bsub>S\<^esub> f2 \<equiv> override_on f1 f2 S"

lemma override_on_fempty[simp]: "\<bottom> ++\<^bsub>S\<^esub> m = m f|` S" 
  by (auto simp add: override_on_def fmap_restr_def)

lemma override_on_fempty2[simp]: "m ++\<^bsub>S\<^esub> \<bottom> = m f|` (-S)" 
  by (auto simp add: override_on_def fmap_restr_def)

lemma fdom_override_on[simp]: "fdom (m1 ++\<^bsub>S\<^esub> m2) = (fdom m1 - S) \<union> (fdom m2 \<inter> S)"
  by (auto simp add: override_on_def fdom_def)

lemma lookup_override_on_eq: "(m1 ++\<^bsub>S\<^esub> m2) x = (if x \<in> S then m2 x else m1 x)"
  by (cases "x \<notin> S") simp_all

lemma override_on_upd_swap: 
  "x \<notin> S \<Longrightarrow> \<rho>(x := z) ++\<^bsub>S\<^esub> \<rho>' = (\<rho> ++\<^bsub>S\<^esub> \<rho>')(x := z)"
  by (auto simp add: override_on_def  fdom_def)

lemma override_on_upd: 
  "x \<in> S \<Longrightarrow> \<rho> ++\<^bsub>S\<^esub> (\<rho>'(x := z)) = (\<rho> ++\<^bsub>S - {x}\<^esub> \<rho>')(x := z)"
  by (auto simp add: override_on_def  fdom_def)

lemma fmap_restr_add: "(m1 ++\<^bsub>S2\<^esub> m2) f|` S = m1 f|` S ++\<^bsub>S2\<^esub> m2 f|` S"
  by (auto simp add: override_on_def  fdom_def fmap_restr_def)

lemma fmap_delete_add: "fmap_delete x (m1 ++\<^bsub>S\<^esub> m2) = fmap_delete x m1 ++\<^bsub>S - {x}\<^esub> fmap_delete x m2"
  by (auto simp add: override_on_def  fdom_def fmap_restr_def fmap_delete_def)

end
