theory FMap
  imports Main
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

definition fmap_restr_l where
  "fmap_restr_l d = fmap_restr (set d)"


end
