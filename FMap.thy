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
  and "\<forall>x \<in> fdom a. the (lookup a x) = the (lookup b x)"
  shows "a = b"
using assms
proof(transfer)
  fix a b :: "('a \<rightharpoonup> 'b)"
  assume d: "dom a = dom b"
  assume eq: "\<forall>x \<in> dom a. the (a x) = the (b x)"
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
  apply rule
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

end
