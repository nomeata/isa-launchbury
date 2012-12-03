theory FMap
  imports Main "~~/src/HOL/Quotient_Examples/FSet" "~~/src/HOL/Library/DAList"
begin

typedef (open) ('a, 'b) fmap = "{x :: 'a \<rightharpoonup> 'b. finite (dom x) }"
  proof show "empty \<in> {x. finite (dom x)}" by simp qed

setup_lifting type_definition_fmap

lift_definition fdom :: "('key, 'value) fmap \<Rightarrow> 'key set" is "dom" ..

lift_definition fran :: "('key, 'value) fmap \<Rightarrow> 'value set" is "ran" ..

lift_definition lookup :: "('key, 'value) fmap \<Rightarrow> 'key \<Rightarrow> 'value option" is "(\<lambda> x. x)" ..

lift_definition fempty :: "('key, 'value) fmap" is Map.empty by simp

lemma fempty_fdom[simp]: "fdom fempty = {}"
  by (transfer, auto)

lift_definition
  fmap_upd :: "('key, 'value) fmap \<Rightarrow> 'key \<Rightarrow> 'value \<Rightarrow> ('key, 'value) fmap" ("_'(_ f\<mapsto> _')" [900,900]900)
  is "\<lambda> m x v. m( x \<mapsto> v)"  by simp

lemma fmap_upd_fdom[simp]: "fdom (h ( x f\<mapsto> v)) = insert x (fdom h)"
  by (transfer, auto)

lemma the_lookup_fmap_upd[simp]: "the (lookup (h (x f\<mapsto> v)) x) = v"
  by (transfer, auto)

lemma the_lookup_fmap_upd_other[simp]: "x' \<noteq> x \<Longrightarrow> the (lookup (h (x f\<mapsto> v)) x') = the (lookup h x')"
  by (transfer, auto)

lemma fmap_upd_overwrite[simp]: "f (x f\<mapsto> y) (x f\<mapsto> z) = f (x f\<mapsto> z)"
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
  fix a b :: "('a \<rightharpoonup> 'b)"
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

lemma fmap_upd_twist: "a ~= c ==> (m(a f\<mapsto> b))(c f\<mapsto> d) = (m(c f\<mapsto> d))(a f\<mapsto> b)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

lift_definition fmap_restr :: "'a set \<Rightarrow> ('a, 'b) fmap => ('a, 'b) fmap"
  is "\<lambda> S m. (if finite S then (restrict_map m S) else empty)" by auto

lemma lookup_fmap_restr[simp]: "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> lookup (fmap_restr S m) x = lookup m x"
  by (transfer, auto)

(*
lemma [transfer_rule]:"(op = ===> set_rel op = ===> op =) op = op ="
  unfolding set_rel_eq fun_rel_eq by (rule refl)

lemma [transfer_rule]: "(op = ===> set_rel op = ===> set_rel op =) op \<inter> op \<inter> "
  unfolding set_rel_eq fun_rel_eq by (rule refl)
*)

lemma fdom_fmap_restr[simp]: "finite S \<Longrightarrow> fdom (fmap_restr S m) = fdom m \<inter> S"
  by (transfer, simp)

lemma fmap_restr_fmap_restr[simp]:
 "finite d1 \<Longrightarrow> finite d2 \<Longrightarrow> fmap_restr d1 (fmap_restr d2 x) = fmap_restr (d1 \<inter> d2) x"
 by (transfer, auto simp add: restrict_map_def)

lemma fmap_restr_useless: "finite S \<Longrightarrow> fdom m \<subseteq> S \<Longrightarrow> fmap_restr S m = m"
  by (rule fmap_eqI, auto)

lemma fmap_restr_not_finite:
  "\<not> finite S \<Longrightarrow> fmap_restr S \<rho> = fempty"
  by (transfer, simp)

definition fmap_restr_l where
  "fmap_restr_l d = fmap_restr (set d)"

lift_definition fmap_delete :: "'a \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda> x m. m(x := None)" by auto

lemma fdom_fmap_delete[simp]:
  "fdom (fmap_delete x m) = fdom m - {x}"
  by (transfer, auto)

lift_definition fmap_add :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl "f++" 100) 
  is "map_add" by auto

lemma fdom_fmap_add[simp]: "fdom (m1 f++ m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto)

lift_definition fmap_of :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap"
  is map_of by (rule finite_dom_map_of)

lemma fdom_fmap_of[simp]: "fdom (fmap_of l) = fst ` set l"
  by (transfer, rule dom_map_of_conv_image_fst)

lemma fmap_of_Nil[simp]: "fmap_of [] = fempty"
 by (transfer, simp)

lemma fmap_of_Cons[simp]: "fmap_of (p # l) = (fmap_of l)(fst p f\<mapsto> snd p)" 
  by (transfer, simp)

lemma fmap_of_append[simp]: "fmap_of (l1 @ l2) = fmap_of l2 f++ fmap_of l1"
  by (transfer, simp)

lemma fmap_delete_fmap_upd[simp]:
  "fmap_delete x (m(x f\<mapsto> v)) = fmap_delete x m"
  by (transfer, simp)

lemma fmap_delete_noop:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (transfer, auto)

lemma fmap_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> fmap_delete x \<Gamma>(x f\<mapsto> the (lookup \<Gamma> x)) = \<Gamma>"
  by (transfer, auto)
 
lemma lookup_fmap_of[simp]:
  "lookup (fmap_of m) x = map_of m x"
  by (transfer, auto)

lemma fmap_delete_fmap_of[simp]:
  "fmap_delete x (fmap_of m) = fmap_of (AList.delete x m)"
  by (transfer, metis delete_conv')

end
