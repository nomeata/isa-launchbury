theory FMap
  imports Main "~~/src/HOL/Quotient_Examples/FSet" "~~/src/HOL/Library/DAList"
begin

subsubsection {* The type of finite maps *}

typedef (open) ('a, 'b) fmap  (infixr "f\<rightharpoonup>" 1) = "{x :: 'a \<rightharpoonup> 'b. finite (dom x) }"
  proof show "empty \<in> {x. finite (dom x)}" by simp qed

setup_lifting type_definition_fmap

lift_definition fdom :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key set" is "dom" ..

lift_definition fran :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'value set" is "ran" ..

lift_definition lookup :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value option" is "(\<lambda> x. x)" ..

lift_definition fempty :: "'key f\<rightharpoonup> 'value" is Map.empty by simp

lemma fempty_fdom[simp]: "fdom fempty = {}"
  by (transfer, auto)

lemma fdomIff: "(a : fdom m) = (lookup m a ~= None)"
 by (transfer, auto)

lemma lookup_not_fdom: "x \<notin> fdom m \<Longrightarrow> lookup m x = None"
  by (auto iff:fdomIff)

lemma finite_range:
  assumes "finite (dom m)"
  shows "finite (ran m)"
  apply (rule finite_subset[OF _ finite_imageI[OF assms, of "\<lambda> x . the (m x)"]])
  by (auto simp add: ran_def dom_def image_def)

lemma finite_fdom[simp]: "finite (fdom m)"
  by transfer

lemma finite_fran[simp]: "finite (fran m)"
  by (transfer, rule finite_range)

lemma fmap_eqI[intro]:
  assumes "fdom a = fdom b"
  and "\<And> x. x \<in> fdom a \<Longrightarrow> the (lookup a x) = the (lookup b x)"
  shows "a = b"
using assms
proof(transfer)
  fix a b :: "'a \<rightharpoonup> 'b"
  assume d: "dom a = dom b"
  assume eq: "\<And> x. x \<in> dom a \<Longrightarrow> the (a x) = the (b x)"
  show "a = b"
  proof
    fix x
    show "a x = b x"
    proof(cases "a x")
    case None
      hence "x \<notin> dom a" by (simp add: dom_def)
      hence "x \<notin> dom b" using d by simp
      hence " b x = None"  by (simp add: dom_def)
      thus ?thesis using None by simp
    next
    case (Some y)
      hence d': "x \<in> dom ( a)" by (simp add: dom_def)
      hence "the ( a x) = the ( b x)" using eq by auto
      moreover
      have "x \<in> dom ( b)" using Some d' d by simp
      then obtain y' where " b x = Some y'" by (auto simp add: dom_def)
      ultimately
      show " a x =  b x" using Some by auto
    qed
  qed
qed

subsubsection {* Updates *}

lift_definition
  fmap_upd :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value \<Rightarrow> 'key f\<rightharpoonup> 'value" ("_'(_ f\<mapsto> _')" [900,900]900)
  is "\<lambda> m x v. m( x \<mapsto> v)"  by simp

lemma fmap_upd_fdom[simp]: "fdom (h (x f\<mapsto> v)) = insert x (fdom h)"
  by (transfer, auto)

lemma the_lookup_fmap_upd[simp]: "lookup (h (x f\<mapsto> v)) x = Some v"
  by (transfer, auto)

lemma the_lookup_fmap_upd_other[simp]: "x' \<noteq> x \<Longrightarrow> lookup (h (x f\<mapsto> v)) x' = lookup h x'"
  by (transfer, auto)

lemma fmap_upd_overwrite[simp]: "f (x f\<mapsto> y) (x f\<mapsto> z) = f (x f\<mapsto> z)"
  by (transfer, auto) 

lemma fmap_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a f\<mapsto> b))(c f\<mapsto> d) = (m(c f\<mapsto> d))(a f\<mapsto> b)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

subsubsection {* Restriction *}

lift_definition fmap_restr :: "'a set \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is "\<lambda> S m. (if finite S then (restrict_map m S) else empty)" by auto

lemma lookup_fmap_restr[simp]: "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> lookup (fmap_restr S m) x = lookup m x"
  by (transfer, auto)

lemma fdom_fmap_restr[simp]: "finite S \<Longrightarrow> fdom (fmap_restr S m) = fdom m \<inter> S"
  by (transfer, simp)

lemma fmap_restr_fmap_restr[simp]:
 "finite d1 \<Longrightarrow> finite d2 \<Longrightarrow> fmap_restr d1 (fmap_restr d2 x) = fmap_restr (d1 \<inter> d2) x"
 by (transfer, auto simp add: restrict_map_def)

lemma fmap_restr_fmap_restr_subset:
 "finite d2 \<Longrightarrow> d1 \<subseteq> d2 \<Longrightarrow> fmap_restr d1 (fmap_restr d2 x) = fmap_restr d1 x"
 by (metis Int_absorb2 finite_subset fmap_restr_fmap_restr)

lemma fmap_restr_useless: "finite S \<Longrightarrow> fdom m \<subseteq> S \<Longrightarrow> fmap_restr S m = m"
  by (rule fmap_eqI, auto)

lemma fmap_restr_not_finite:
  "\<not> finite S \<Longrightarrow> fmap_restr S \<rho> = fempty"
  by (transfer, simp)

lemma fmap_restr_fmap_upd: "x \<in> S \<Longrightarrow> finite S \<Longrightarrow> fmap_restr S (m1(x f\<mapsto> v)) = (fmap_restr S m1)(x f\<mapsto> v)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "xa = x")
  apply auto
  done

subsubsection {* Delete *}

lift_definition fmap_delete :: "'a \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is "\<lambda> x m. m(x := None)" by auto

lemma fdom_fmap_delete[simp]:
  "fdom (fmap_delete x m) = fdom m - {x}"
  by (transfer, auto)

lemma fmap_delete_fmap_upd[simp]:
  "fmap_delete x (m(x f\<mapsto> v)) = fmap_delete x m"
  by (transfer, simp)

lemma fmap_delete_noop:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (transfer, auto)

lemma fmap_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> fmap_delete x \<Gamma>(x f\<mapsto> the (lookup \<Gamma> x)) = \<Gamma>"
  by (transfer, auto)
 
subsubsection {* Addition (mergeing) of finite maps *}

lift_definition fmap_add :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b" (infixl "f++" 100) 
  is "map_add" by auto

lemma fdom_fmap_add[simp]: "fdom (m1 f++ m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto)

lemma lookup_fmap_add1[simp]: "x \<in> fdom m2 \<Longrightarrow> lookup (fmap_add m1 m2) x = lookup m2 x"
  by (transfer, auto)

lemma lookup_fmap_add2[simp]:  "x \<notin> fdom m2 \<Longrightarrow> lookup (fmap_add m1 m2) x = lookup m1 x"
  apply transfer
  by (metis map_add_dom_app_simps(3))

lemma [simp]: "fmap_add \<rho> fempty = \<rho>"
  by (transfer, auto)

lemma fmap_add_overwrite: "fdom m1 \<subseteq> fdom m2 \<Longrightarrow> fmap_add m1 m2 = m2"
  apply transfer
  apply rule
  apply (case_tac "x \<in> dom m2")
  apply (auto simp add: map_add_dom_app_simps(1))
  done

lemma fmap_add_rho[simp]: "fmap_add \<rho> (fmap_add \<rho> x) = fmap_add \<rho> x"
  apply (rule fmap_add_overwrite)
  by (metis Un_upper1 fdom_fmap_add)

lemma fmap_add_upd_swap: 
  "x \<notin> fdom \<rho>' \<Longrightarrow> fmap_add (\<rho>(x f\<mapsto> z)) \<rho>' = (fmap_add \<rho> \<rho>')(x f\<mapsto> z)"
  apply transfer
  by (metis map_add_upd_left)

lemma fmap_add_upd: 
  "fmap_add \<rho> (\<rho>'(x f\<mapsto> z)) = (fmap_add \<rho> \<rho>')(x f\<mapsto> z)"
  apply transfer
  by (metis map_add_upd)

lemma fmap_restr_add: "fmap_restr S (m1 f++ m2) = fmap_restr S m1 f++ fmap_restr S m2"
  apply (cases "finite S")
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "x \<in> fdom m2")
  apply auto
  apply (simp add: fmap_restr_not_finite)
  done

subsubsection {* Conversion from associative lists *}

lift_definition fmap_of :: "('a \<times> 'b) list \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is map_of by (rule finite_dom_map_of)

lemma fmap_of_Nil[simp]: "fmap_of [] = fempty"
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
  
end
