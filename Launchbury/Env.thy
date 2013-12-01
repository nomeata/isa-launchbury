theory Env
  imports Main "~~/HOL/Library/Quotient_Option" "~~/src/HOL/Library/AList" HOLCF
begin

default_sort type

subsubsection {* The type of finite maps *}

type_synonym  ('a, 'b) fmap = "'a \<Rightarrow> 'b" (infixr "f\<rightharpoonup>" 1)

definition fdom :: "'key f\<rightharpoonup> 'value::pcpo \<Rightarrow> 'key set" where "fdom m = {x. m x \<noteq> \<bottom>}"

definition lookup :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value" (infix "f!" 55) where "lookup m x = m x"

lemma lookup_fempty[simp]: "lookup \<bottom> x = \<bottom>" by (simp add: lookup_def)

lemma fempty_fdom[simp]: "fdom \<bottom> = {}" by (simp add: fdom_def)

lemma fempty_fdom2[simp]: "fdom (\<lambda>_ . \<bottom>) = {}" by (simp add: fdom_def)

lemma fdomIff: "(a \<in> fdom m) = (lookup m a \<noteq> \<bottom>)" by (simp add: fdom_def lookup_def)

lemma lookup_not_fdom: "x \<notin> fdom m \<Longrightarrow> lookup m x = \<bottom>"  by (auto iff:fdomIff)

lemma lookup_fdom[simp]: "m f! x \<noteq> \<bottom> \<Longrightarrow> x \<in> fdom m"  by (auto iff:fdomIff)

lemma fmap_eqI:
  assumes "\<And> x. a f! x = b f! x"
  shows "a = b"
using assms
by (auto simp add: lookup_def)

subsubsection {* Updates *}

lemma fdom_fun_upd_subset: "fdom (h (x := v)) \<subseteq> insert x (fdom h)"
  by (auto simp add: fdom_def)

lemma lookup_fun_upd[simp]: "lookup (h (x := v)) x = v"
  by (auto simp add: fdom_def  lookup_def)

lemma lookup_fun_upd_other[simp]: "x' \<noteq> x \<Longrightarrow> lookup (h (x := v)) x' = lookup h x'"
  by (auto simp add: fdom_def  lookup_def)

lemma lookup_fun_upd_eq: "lookup (h (x := v)) x' = (if x = x' then v else lookup h x')"
  by (auto simp add: fdom_def  lookup_def)

lemma fun_upd_noop[simp]: "x \<in> fdom f \<Longrightarrow> y = f f! x \<Longrightarrow> f (x := y) = f"
  by (auto simp add: fdom_def  lookup_def)

lemma fun_upd_eqD1: "m(a := x) = n(a := y) \<Longrightarrow> x = y"
  by (metis fun_upd_same)

subsubsection {* Restriction *}

definition fmap_restr :: "'a set \<Rightarrow> 'a f\<rightharpoonup> 'b::pcpo \<Rightarrow> 'a f\<rightharpoonup> 'b"
  where "fmap_restr S m = (\<lambda> x. if x \<in> S then m x else \<bottom>)"

abbreviation fmap_restr_rev  (infixl "f|`"  110) where "fmap_restr_rev m S \<equiv> fmap_restr S m"

lemma fmap_restr_empty[simp]: "fdom m \<inter> S = {} \<Longrightarrow> m f|` S = \<bottom>"
  by (fastforce simp add: fdom_def fmap_restr_def)

lemma lookup_fmap_restr[simp]: "x \<in> S \<Longrightarrow> lookup (fmap_restr S m) x = lookup m x"
  by (fastforce simp add: fmap_restr_def lookup_def)

lemma lookup_fmap_restr_not_there[simp]: "x \<notin> S \<Longrightarrow> lookup (fmap_restr S m) x = \<bottom>"
  by (fastforce simp add: fmap_restr_def lookup_def)

lemma lookup_fmap_restr_eq: "m f|` S f! x = (if x \<in> S then m f! x else \<bottom>)"
  by (simp)


lemma fmap_restr_cong: "fdom m \<inter> S1 = fdom m \<inter> S2 \<Longrightarrow> m f|` S1 = m f|` S2"
  apply (rule fmap_eqI)
  apply (simp add: lookup_fmap_restr_eq)
  by (metis Int_iff lookup_not_fdom)

lemma fmap_restr_fmap_restr[simp]:
 "x f|` d2 f|` d1 = x f|` (d1 \<inter> d2)"
  by (fastforce simp add: fmap_restr_def lookup_def)

lemma fmap_restr_fmap_restr_subset:
 "d1 \<subseteq> d2 \<Longrightarrow> x f|` d2 f|` d1 = x f|` d1"
 by (metis Int_absorb2 fmap_restr_fmap_restr)

lemma fmap_restr_useless: "fdom m \<subseteq> S \<Longrightarrow> m f|` S = m"
  by (rule fmap_eqI) (auto simp add: lookup_fmap_restr_eq dest!: set_mp)

lemma fmap_restr_UNIV[simp]: "m f|` UNIV = m"
  by (rule fmap_restr_useless) simp

lemma fmap_restr_fun_upd[simp]: "x \<in> S \<Longrightarrow> m1(x := v) f|` S = (m1 f|` S)(x := v)"
  apply (rule fmap_eqI)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_fmap_restr_eq)
  done

lemma fmap_restr_fun_upd_other[simp]: "x \<notin> S \<Longrightarrow> m1(x := v) f|` S = m1 f|` S"
  apply (rule fmap_eqI)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_fmap_restr_eq)
  done

subsubsection {* Deleting *}

definition fmap_delete :: "'a \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b::pcpo"
  where "fmap_delete x m = m(x := \<bottom>)"

lemma lookup_fmap_delete[simp]:
  "x' \<noteq> x \<Longrightarrow> fmap_delete x m f! x' = m f! x'"
  by (simp add: fmap_delete_def lookup_def)

lemma lookup_fmap_delete_None[simp]:
  "fmap_delete x m f! x = \<bottom>"
  by (simp add: fmap_delete_def lookup_def)

lemma fdom_fmap_delete[simp]:
  "fdom (fmap_delete x m) = fdom m - {x}"
  by (auto simp add: fmap_delete_def lookup_def fdom_def)

lemma fdom_fmap_delete_subset:
  "fdom (fmap_delete x m) \<subseteq> fdom m" by auto

lemma fmap_delete_fun_upd[simp]:
  "fmap_delete x (m(x := v)) = fmap_delete x m"
  by (auto simp add: fmap_delete_def )

lemma fmap_delete_fun_upd2[simp]:
  "(fmap_delete x m)(x := v) = m(x := v)"
  by (auto simp add: fmap_delete_def )

lemma fmap_delete_fun_upd3[simp]:
  "x \<noteq> y \<Longrightarrow> fmap_delete x (m(y := v)) = (fmap_delete x m)(y := v)"
  by (auto simp add: fmap_delete_def )

lemma fmap_delete_noop[simp]:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (auto simp add: fmap_delete_def fdom_def)

lemma fun_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> (fmap_delete x \<Gamma>)(x := \<Gamma> f! x) = \<Gamma>"
  by (auto)

lemma fmap_restr_fmap_delete_other[simp]: "x \<notin> S \<Longrightarrow> fmap_delete x m f|` S = m f|` S"
  apply (rule fmap_eqI)
  apply (auto simp add: lookup_fmap_restr_eq)
  by (metis lookup_fmap_delete)

lemma fmap_delete_restr: "fmap_delete x m = m f|` (-{x})"
  by (auto intro: fmap_eqI simp add: lookup_fmap_restr_eq)

subsubsection {* Addition (merging) of finite maps *}

definition fmap_add :: "'a set \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"  
  where "fmap_add S f1 f2 = (\<lambda> x. if x \<in> S then f2 x else f1 x)"

abbreviation fmap_add_syn ("_ f++\<^bsub>_\<^esub> _" [100, 0, 100] 100) where "f1 f++\<^bsub>S\<^esub> f2 \<equiv> fmap_add S f1 f2"

lemma fmap_add_fempty[simp]: "\<bottom> f++\<^bsub>S\<^esub> m = m f|` S" 
  by (auto simp add: fmap_add_def lookup_def fmap_restr_def)

lemma fmap_add_fempty2[simp]: "m f++\<^bsub>S\<^esub> \<bottom> = m f|` (-S)" 
  by (auto simp add: fmap_add_def lookup_def fmap_restr_def)

lemma fdom_fmap_add[simp]: "fdom (m1 f++\<^bsub>S\<^esub> m2) = (fdom m1 - S) \<union> (fdom m2 \<inter> S)"
  by (auto simp add: fmap_add_def lookup_def fdom_def)

lemma lookup_fmap_add1[simp]: "x \<in> S \<Longrightarrow> m1 f++\<^bsub>S\<^esub> m2 f! x = m2 f! x"
  by (auto simp add: fmap_add_def lookup_def fdom_def)

lemma lookup_fmap_add2[simp]:  "x \<notin> S \<Longrightarrow>  m1 f++\<^bsub>S\<^esub> m2 f! x = m1 f! x"
  by (auto simp add: fmap_add_def lookup_def fdom_def)

lemma lookup_fmap_add_eq: " m1 f++\<^bsub>S\<^esub> m2 f! x = (if x \<in> S then m2 f! x else m1 f! x)"
  by (cases "x \<notin> S") simp_all

lemma fmap_add_upd_swap: 
  "x \<notin> S \<Longrightarrow> \<rho>(x := z) f++\<^bsub>S\<^esub> \<rho>' = (\<rho> f++\<^bsub>S\<^esub> \<rho>')(x := z)"
  by (auto simp add: fmap_add_def  lookup_def fdom_def)

lemma fmap_add_upd: 
  "x \<in> S \<Longrightarrow> \<rho> f++\<^bsub>S\<^esub> (\<rho>'(x := z)) = (\<rho> f++\<^bsub>S - {x}\<^esub> \<rho>')(x := z)"
  by (auto simp add: fmap_add_def  lookup_def fdom_def)

lemma fmap_restr_add: "fmap_restr S (m1 f++\<^bsub>S2\<^esub> m2) = fmap_restr S m1 f++\<^bsub>S2\<^esub> fmap_restr S m2"
  by (auto simp add: fmap_add_def  lookup_def fdom_def fmap_restr_def)

lemma fmap_delete_add: "fmap_delete x (m1 f++\<^bsub>S\<^esub> m2) = fmap_delete x m1 f++\<^bsub>S - {x}\<^esub> fmap_delete x m2"
  by (auto simp add: fmap_add_def  lookup_def fdom_def fmap_restr_def fmap_delete_def)

subsubsection {* Map *}

definition fmap_map :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'c" where "fmap_map f m = (\<lambda> x. f (m x))"

lemma fmap_map_id[simp]: "fmap_map (\<lambda> x. x) m = m" by (simp add: fmap_map_def)

lemma lookup_fmap_map[simp]: "lookup (fmap_map f m) x = f (lookup m x)"  by (simp add: fmap_map_def lookup_def)

lemma fmap_map_fmap_restr[simp]: "f \<bottom> = \<bottom> \<Longrightarrow> fmap_map f (fmap_restr S m) = fmap_restr S (fmap_map f m)"
  by (rule fmap_eqI) (auto simp add: lookup_fmap_restr_eq)

lemma fmap_map_fun_upd[simp]: "fmap_map f (m(x := v)) = (fmap_map f m)(x := f v)"
  by (auto simp add: fmap_map_def lookup_def )


subsection {* Lifting relations pointwise *}

inductive fmap_lift_rel for P where
  fmap_lift_relI[intro]: "(\<And> x. P (m f! x) (m' f! x)) \<Longrightarrow> fmap_lift_rel P m m'"

inductive_cases fmap_lift_relE[elim]:  "fmap_lift_rel P m m'" 

end
