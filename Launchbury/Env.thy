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

definition
  fmap_upd :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value \<Rightarrow> 'key f\<rightharpoonup> 'value" ("_'(_ f\<mapsto> _')" [900,900]900)
  where "fmap_upd m x v = m( x :=  v)"


lemma fdom_fmap_upd_subset: "fdom (h (x f\<mapsto> v)) \<subseteq> insert x (fdom h)"
  by (auto simp add: fdom_def fmap_upd_def)

lemma lookup_fmap_upd[simp]: "lookup (h (x f\<mapsto> v)) x = v"
  by (auto simp add: fdom_def fmap_upd_def lookup_def)

lemma lookup_fmap_upd_other[simp]: "x' \<noteq> x \<Longrightarrow> lookup (h (x f\<mapsto> v)) x' = lookup h x'"
  by (auto simp add: fdom_def fmap_upd_def lookup_def)

lemma lookup_fmap_upd_eq: "lookup (h (x f\<mapsto> v)) x' = (if x = x' then v else lookup h x')"
  by (auto simp add: fdom_def fmap_upd_def lookup_def)

lemma fmap_upd_overwrite[simp]: "f (x f\<mapsto> y) (x f\<mapsto> z) = f (x f\<mapsto> z)"
  by (auto simp add: fdom_def fmap_upd_def lookup_def)

lemma fmap_upd_noop[simp]: "x \<in> fdom f \<Longrightarrow> y = f f! x \<Longrightarrow> f (x f\<mapsto> y) = f"
  by (auto simp add: fdom_def fmap_upd_def lookup_def)

lemma fmap_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a f\<mapsto> b))(c f\<mapsto> d) = (m(c f\<mapsto> d))(a f\<mapsto> b)"
  apply (rule fmap_eqI)
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

lemma fmap_upd_eqD1: "m(a f\<mapsto> x) = n(a f\<mapsto> y) \<Longrightarrow> x = y"
  by (metis fmap_upd_def fun_upd_same)

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

lemma fmap_restr_fmap_upd[simp]: "x \<in> S \<Longrightarrow> m1(x f\<mapsto> v) f|` S = (m1 f|` S)(x f\<mapsto> v)"
  apply (rule fmap_eqI)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_fmap_restr_eq)
  done

lemma fmap_restr_fmap_upd_other[simp]: "x \<notin> S \<Longrightarrow> m1(x f\<mapsto> v) f|` S = m1 f|` S"
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

lemma fmap_delete_fmap_upd[simp]:
  "fmap_delete x (m(x f\<mapsto> v)) = fmap_delete x m"
  by (auto simp add: fmap_delete_def fmap_upd_def)

lemma fmap_delete_fmap_upd2[simp]:
  "(fmap_delete x m)(x f\<mapsto> v) = m(x f\<mapsto> v)"
  by (auto simp add: fmap_delete_def fmap_upd_def)

lemma fmap_delete_fmap_upd3[simp]:
  "x \<noteq> y \<Longrightarrow> fmap_delete x (m(y f\<mapsto> v)) = (fmap_delete x m)(y f\<mapsto> v)"
  by (auto simp add: fmap_delete_def fmap_upd_def)

lemma fmap_delete_noop[simp]:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (auto simp add: fmap_delete_def fdom_def)

lemma fmap_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> (fmap_delete x \<Gamma>)(x f\<mapsto> \<Gamma> f! x) = \<Gamma>"
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
  "x \<notin> S \<Longrightarrow> \<rho>(x f\<mapsto> z) f++\<^bsub>S\<^esub> \<rho>' = (\<rho> f++\<^bsub>S\<^esub> \<rho>')(x f\<mapsto> z)"
  by (auto simp add: fmap_add_def fmap_upd_def lookup_def fdom_def)

lemma fmap_add_upd: 
  "x \<in> S \<Longrightarrow> \<rho> f++\<^bsub>S\<^esub> (\<rho>'(x f\<mapsto> z)) = (\<rho> f++\<^bsub>S - {x}\<^esub> \<rho>')(x f\<mapsto> z)"
  by (auto simp add: fmap_add_def fmap_upd_def lookup_def fdom_def)

lemma fmap_restr_add: "fmap_restr S (m1 f++\<^bsub>S2\<^esub> m2) = fmap_restr S m1 f++\<^bsub>S2\<^esub> fmap_restr S m2"
  by (auto simp add: fmap_add_def fmap_upd_def lookup_def fdom_def fmap_restr_def)

lemma fmap_delete_add: "fmap_delete x (m1 f++\<^bsub>S\<^esub> m2) = fmap_delete x m1 f++\<^bsub>S - {x}\<^esub> fmap_delete x m2"
  by (auto simp add: fmap_add_def fmap_upd_def lookup_def fdom_def fmap_restr_def fmap_delete_def)

(*
subsubsection {* Copying *}

lift_definition fmap_copy :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is "\<lambda> f x y . f (y := f x)" by auto

lemma fdom_fmap_copy[simp]: "fdom (fmap_copy m x y) = (if x \<in> fdom m then fdom m \<union> {y} else (fdom m - {y}))"
  by transfer auto

lemma fdom_fmap_copy_subset:
  "fdom (fmap_copy m x y) \<subseteq> insert y (fdom m)" by auto

lemma fmap_copy_cong: "lookup \<Gamma> x = lookup \<Gamma> x' \<Longrightarrow> fmap_copy \<Gamma> x y = fmap_copy \<Gamma> x' y"
  by transfer simp

lemma lookup_fmap_copy[simp]: "lookup (fmap_copy m x y) y = lookup m x"
  by transfer auto

lemma lookup_fmap_copy_other[simp]: "x' \<noteq> y \<Longrightarrow> lookup (fmap_copy m x y) x' = lookup m x'"
  by transfer auto

lemma lookup_fmap_copy_eq: "lookup (fmap_copy h x y) x' = (if y = x' then lookup h x else lookup h x')"
  by transfer simp

lemma fmap_restrict_fmap_copy[simp]: "x \<notin> S \<Longrightarrow> fmap_restr S (fmap_copy \<Gamma> y x) = fmap_restr S \<Gamma>"
  by transfer auto

lemma fmap_restrict_fmap_copy'[simp]: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> fmap_restr S (fmap_copy \<Gamma> y x) = fmap_copy (fmap_restr S \<Gamma>) y x"
  by transfer auto
*)


subsubsection {* Map *}

definition fmap_map :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'c" where "fmap_map f m = (\<lambda> x. f (m x))"

lemma fmap_map_id[simp]: "fmap_map (\<lambda> x. x) m = m" by (simp add: fmap_map_def)

lemma lookup_fmap_map[simp]: "lookup (fmap_map f m) x = f (lookup m x)"  by (simp add: fmap_map_def lookup_def)

lemma fmap_map_fmap_restr[simp]: "f \<bottom> = \<bottom> \<Longrightarrow> fmap_map f (fmap_restr S m) = fmap_restr S (fmap_map f m)"
  by (rule fmap_eqI) (auto simp add: lookup_fmap_restr_eq)

lemma fmap_map_fmap_upd[simp]: "fmap_map f (m(x f\<mapsto> v)) = (fmap_map f m)(x f\<mapsto> f v)"
  by (auto simp add: fmap_map_def lookup_def fmap_upd_def)
(*
lemma fmap_map_fmap_copy [simp]: "fmap_map f (fmap_copy m x y) = fmap_copy (fmap_map f m) x y"
  by transfer auto
*)

(*
subsubsection {* Conversion from associative lists *}

lift_definition fmap_of :: "('a \<times> 'b) list \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is map_of ..

lemma fmap_of_Nil[simp]: "fmap_of [] = f\<emptyset>"
 by (transfer, simp)

lemma fmap_of_Cons[simp]: "fmap_of (p # l) = (fmap_of l)(fst p f\<mapsto> snd p)" 
  by (transfer, simp)

lemma fmap_of_append[simp]: "fmap_of (l1 @ l2) = fmap_of l2 f++ fmap_of l1"
  by (transfer, simp)

lemma lookup_fmap_of[simp]:
  "lookup (fmap_of m) x = map_of m x"
  by (transfer, auto)

lemma fmap_delete_fmap_of[simp]:
  "fmap_delete x (fmap_of m) = fmap_of (AList.delete x m)"
  by (transfer, metis delete_conv')
*)

(*
subsubsection {* Less-than-relation for extending finite maps *}

instantiation fmap :: (type,type) order
begin
  definition "\<rho> \<le> \<rho>' = ((fdom \<rho> \<subseteq> fdom \<rho>') \<and> (\<forall>x \<in> fdom \<rho>. lookup \<rho> x = lookup \<rho>' x))"
  definition "(\<rho>::'a f\<rightharpoonup> 'b) < \<rho>' = (\<rho> \<noteq> \<rho>' \<and> \<rho> \<le> \<rho>')"

  lemma fmap_less_eqI[intro]:
    assumes assm1: "fdom \<rho> \<subseteq> fdom \<rho>'"
      and assm2:  "\<And> x. \<lbrakk> x \<in> fdom \<rho> ; x \<in> fdom \<rho>'  \<rbrakk> \<Longrightarrow> \<rho> f! x = \<rho>' f! x "
     shows "\<rho> \<le> \<rho>'"
   unfolding less_eq_fmap_def
   apply rule
   apply fact
   apply rule+
   apply (frule subsetD[OF `_ \<subseteq> _`])
   apply (frule  assm2)
   apply (auto iff: fdomIff)
   done
  
  lemma fmap_less_eqD:
    assumes "\<rho> \<le> \<rho>'"
    assumes "x \<in> fdom \<rho>"
    shows "lookup \<rho> x = lookup \<rho>' x"
    using assms
    unfolding less_eq_fmap_def by auto
  
  lemma fmap_antisym: assumes  "(x:: 'a f\<rightharpoonup> 'b) \<le> y" and "y \<le> x" shows "x = y "
  proof(rule fmap_eqI[rule_format])
      show "fdom x = fdom y" using `x \<le> y` and `y \<le> x` unfolding less_eq_fmap_def by auto
      
      fix v
      assume "v \<in> fdom x"
      hence "v \<in> fdom y" using `fdom _ = _` by simp
  
      thus "x f! v = y f! v"
        using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by simp
    qed
  
  lemma fmap_trans: assumes  "(x:: 'a f\<rightharpoonup> 'b) \<le> y" and "y \<le> z" shows "x \<le> z"
  proof
    show "fdom x \<subseteq> fdom z" using `x \<le> y` and `y \<le> z` unfolding less_eq_fmap_def
      by -(rule order_trans [of _ "fdom y"], auto)
    
    fix v
    assume "v \<in> fdom x" and "v \<in> fdom z"
    hence "v \<in> fdom y" using `x \<le> y`  unfolding less_eq_fmap_def by auto
    hence "lookup y v = lookup x v"
      using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by auto
    moreover
    have "lookup y v = lookup z v"
      by (rule fmap_less_eqD[OF `y \<le> z`  `v \<in> fdom y`])
    ultimately
    show "x f! v = z f! v" by auto
  qed
  
  instance
    apply default
    using fmap_antisym apply (auto simp add: less_fmap_def)[1]
    apply (auto simp add: less_eq_fmap_def)[1]
    using fmap_trans apply assumption
    using fmap_antisym apply assumption
    done
end

lemma fmap_less_fdom:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> fdom \<rho>1 \<subseteq> fdom \<rho>2"
  by (metis less_eq_fmap_def)

lemma fmap_less_restrict:
  "\<rho>1 \<le> \<rho>2 \<longleftrightarrow> \<rho>1 = fmap_restr (fdom \<rho>1) \<rho>2"
  unfolding less_eq_fmap_def
  apply transfer
  apply (auto simp add:restrict_map_def split:option.split_asm)
  by (metis option.simps(3))+

lemma fmap_restr_less:
  "fmap_restr S \<rho> \<le> \<rho>"
  unfolding less_eq_fmap_def
  by (transfer, auto)

lemma fmap_delete_less: "fmap_delete x \<rho> \<le> \<rho>"
  unfolding less_eq_fmap_def
  by (transfer, auto)

lemma fmap_upd_less[simp, intro]:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> v1 = v2 \<Longrightarrow> \<rho>1(x f\<mapsto> v1) \<le> \<rho>2(x f\<mapsto> v2)"
  apply (rule fmap_less_eqI)
  apply (auto dest: fmap_less_fdom)[1]
  apply (case_tac "xa = x")
  apply (auto dest: fmap_less_eqD)
  done

lemma fmap_upd_less2[simp, intro]:
  "x \<notin> fdom \<rho> \<Longrightarrow> \<rho> \<le> \<rho>(x f\<mapsto> v)"
  apply (rule fmap_less_eqI)
  apply (auto dest: fmap_less_fdom)[1]
  apply (case_tac "xa = x")
  apply (auto dest: fmap_less_eqD)
  done

lemma fmap_update_less[simp, intro]:
  "\<rho>1 \<le> \<rho>1' \<Longrightarrow> \<rho>2 \<le> \<rho>2' \<Longrightarrow>  (fdom \<rho>2' - fdom \<rho>2) \<inter> fdom \<rho>1 = {} \<Longrightarrow> \<rho>1 f++ \<rho>2 \<le> \<rho>1' f++ \<rho>2'"
  apply (rule fmap_less_eqI)
  apply (auto dest: fmap_less_fdom)[1]
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto dest: fmap_less_eqD fmap_less_fdom)
  apply (metis fmap_less_eqD fmap_less_fdom lookup_fmap_add1 set_mp)
  by (metis Diff_iff Diff_triv fmap_less_eqD lookup_fmap_add2)

lemma fmap_restr_le:
  assumes "\<rho>1 \<le> \<rho>2"
  assumes "S1 \<subseteq> S2"
  shows "fmap_restr S1 \<rho>1 \<le> fmap_restr S2 \<rho>2"
proof-
  show ?thesis
  proof (rule fmap_less_eqI)
    have "fdom \<rho>1 \<subseteq> fdom \<rho>2"
      by (metis assms(1) less_eq_fmap_def)
    thus "fdom (fmap_restr S1 \<rho>1) \<subseteq> fdom (fmap_restr S2 \<rho>2)"
      using `S1 \<subseteq> S2`
      by auto
  next
    fix x
    assume "x \<in> fdom (fmap_restr S1 \<rho>1) "
    hence [simp]:"x \<in> fdom \<rho>1" and [simp]:"x \<in> S1" and [simp]: "x \<in> S2"
      by (auto intro: set_mp[OF `S1 \<subseteq> S2`])
    have "\<rho>1 f! x = \<rho>2 f! x"
      by (metis `x \<in> fdom \<rho>1` assms(1) less_eq_fmap_def)
    thus "(fmap_restr S1 \<rho>1) f! x = (fmap_restr S2 \<rho>2) f! x"
      by simp
  qed
qed
*)

subsection {* Lifting relations pointwise *}

inductive fmap_lift_rel for P where
  fmap_lift_relI[intro]: "(\<And> x. P (m f! x) (m' f! x)) \<Longrightarrow> fmap_lift_rel P m m'"

inductive_cases fmap_lift_relE[elim]:  "fmap_lift_rel P m m'" 

end
