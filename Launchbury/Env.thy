theory Env
  imports Main HOLCF
begin

default_sort type

text {*
Our type for environments is a function with a pcpo as the co-domain; this theory collects
related definitions.
*}

subsubsection {* The domain of a pcpo-valued function *}

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

definition env_restr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "env_restr S m = (\<lambda> x. if x \<in> S then m x else \<bottom>)"

abbreviation env_restr_rev  (infixl "f|`"  110) where "env_restr_rev m S \<equiv> env_restr S m"

notation (latex output) env_restr_rev ("_|\<^bsub>_\<^esub>")

lemma env_restr_empty[simp]: "fdom m \<inter> S = {} \<Longrightarrow> m f|` S = \<bottom>"
  by (fastforce simp add: fdom_def env_restr_def)

lemma lookup_env_restr[simp]: "x \<in> S \<Longrightarrow> (env_restr S m) x = m x"
  by (fastforce simp add: env_restr_def)

lemma lookup_env_restr_not_there[simp]: "x \<notin> S \<Longrightarrow> (env_restr S m) x = \<bottom>"
  by (fastforce simp add: env_restr_def)

lemma lookup_env_restr_eq: "(m f|` S) x = (if x \<in> S then m x else \<bottom>)"
  by simp

lemma env_restr_cong: "fdom m \<inter> S1 = fdom m \<inter> S2 \<Longrightarrow> m f|` S1 = m f|` S2"
  apply (rule ext)
  apply (simp add: lookup_env_restr_eq)
  by (metis Int_iff lookup_not_fdom)

lemma env_restr_env_restr[simp]:
 "x f|` d2 f|` d1 = x f|` (d1 \<inter> d2)"
  by (fastforce simp add: env_restr_def)

lemma env_restr_env_restr_subset:
 "d1 \<subseteq> d2 \<Longrightarrow> x f|` d2 f|` d1 = x f|` d1"
 by (metis Int_absorb2 env_restr_env_restr)

lemma env_restr_useless: "fdom m \<subseteq> S \<Longrightarrow> m f|` S = m"
  by (rule ext) (auto simp add: lookup_env_restr_eq dest!: set_mp)

lemma env_restr_UNIV[simp]: "m f|` UNIV = m"
  by (rule env_restr_useless) simp

lemma env_restr_fun_upd[simp]: "x \<in> S \<Longrightarrow> m1(x := v) f|` S = (m1 f|` S)(x := v)"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_env_restr_eq)
  done

lemma env_restr_fun_upd_other[simp]: "x \<notin> S \<Longrightarrow> m1(x := v) f|` S = m1 f|` S"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_env_restr_eq)
  done

lemma env_restr_eq_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' = m2 f|` S'"
  shows "m1 f|` S = m2 f|` S"
using assms
by (metis env_restr_env_restr le_iff_inf)

subsubsection {* Deleting *}

definition env_delete :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::pcpo)"
  where "env_delete x m = m(x := \<bottom>)"

lemma lookup_env_delete[simp]:
  "x' \<noteq> x \<Longrightarrow> env_delete x m x' = m x'"
  by (simp add: env_delete_def)

lemma lookup_env_delete_None[simp]:
  "env_delete x m x = \<bottom>"
  by (simp add: env_delete_def)

lemma fdom_env_delete[simp]:
  "fdom (env_delete x m) = fdom m - {x}"
  by (auto simp add: env_delete_def fdom_def)

lemma fdom_env_delete_subset:
  "fdom (env_delete x m) \<subseteq> fdom m" by auto

lemma env_delete_fun_upd[simp]:
  "env_delete x (m(x := v)) = env_delete x m"
  by (auto simp add: env_delete_def)

lemma env_delete_fun_upd2[simp]:
  "(env_delete x m)(x := v) = m(x := v)"
  by (auto simp add: env_delete_def)

lemma env_delete_fun_upd3[simp]:
  "x \<noteq> y \<Longrightarrow> env_delete x (m(y := v)) = (env_delete x m)(y := v)"
  by (auto simp add: env_delete_def)

lemma env_delete_noop[simp]:
  "x \<notin> fdom m \<Longrightarrow> env_delete x m = m"
  by (auto simp add: env_delete_def fdom_def)

lemma fun_upd_env_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> (env_delete x \<Gamma>)(x := \<Gamma> x) = \<Gamma>"
  by (auto)

lemma env_restr_env_delete_other[simp]: "x \<notin> S \<Longrightarrow> env_delete x m f|` S = m f|` S"
  apply (rule ext)
  apply (auto simp add: lookup_env_restr_eq)
  by (metis lookup_env_delete)

lemma env_delete_restr: "env_delete x m = m f|` (-{x})"
  by (auto simp add: lookup_env_restr_eq)

subsubsection {* Merging of two functions *}

text {*
We'd like to have some nice syntax for @{term "override_on"}.
*}

abbreviation override_on_syn ("_ ++\<^bsub>_\<^esub> _" [100, 0, 100] 100) where "f1 ++\<^bsub>S\<^esub> f2 \<equiv> override_on f1 f2 S"

lemma override_on_bot[simp]:
  "\<bottom> ++\<^bsub>S\<^esub> m = m f|` S" 
  "m ++\<^bsub>S\<^esub> \<bottom> = m f|` (-S)" 
  by (auto simp add: override_on_def env_restr_def)

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

lemma env_restr_add: "(m1 ++\<^bsub>S2\<^esub> m2) f|` S = m1 f|` S ++\<^bsub>S2\<^esub> m2 f|` S"
  by (auto simp add: override_on_def  fdom_def env_restr_def)

lemma env_delete_add: "env_delete x (m1 ++\<^bsub>S\<^esub> m2) = env_delete x m1 ++\<^bsub>S - {x}\<^esub> env_delete x m2"
  by (auto simp add: override_on_def  fdom_def env_restr_def env_delete_def)

end
