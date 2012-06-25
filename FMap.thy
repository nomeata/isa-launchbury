theory FMap
  imports "~~/src/HOL/HOLCF/HOLCF"
begin

default_sort type

typedef (open) ('a, 'b) fmap = "{x :: 'a \<rightharpoonup> 'b. finite (dom x) }"
  proof show "empty \<in> {x. finite (dom x)}" by simp qed

setup_lifting type_definition_fmap

lift_definition fdom :: "('key, 'value) fmap \<Rightarrow> 'key set" is "dom" ..

lift_definition fran :: "('key, 'value) fmap \<Rightarrow> 'value set" is "ran" ..

lift_definition lookup :: "('key, 'value) fmap \<Rightarrow> 'key \<Rightarrow> 'value option" is "(\<lambda> x. x)" ..

lift_definition fempty :: "('key, 'value) fmap" is Map.empty by simp

lift_definition
  fmap_upd :: "('key, 'value) fmap \<Rightarrow> 'key \<Rightarrow> 'value \<Rightarrow> ('key, 'value) fmap" ("_'(_ f\<mapsto> _')" [900,900]900)
  is "\<lambda> m x v. m( x \<mapsto> v)"  by simp

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


instantiation fmap :: (type, po) po
begin
  definition "(a::('a, 'b) fmap) \<sqsubseteq> b \<equiv> (fdom a = fdom b) \<and> (\<forall>x \<in> fdom a. the (lookup a x) \<sqsubseteq> the (lookup b x))"

instance
proof default
  fix x :: "('a, 'b) fmap"
  show "x \<sqsubseteq> x" by (auto simp add:below_fmap_def)
next
  fix x y z :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z"
  thus "x \<sqsubseteq> z"
  apply (auto simp add: below_fmap_def)
  by (metis below.r_trans)
next
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x"
  thus "x = y"
  by (auto simp add: below_fmap_def po_eq_conv)
qed
end

lemma fmap_belowI:
  assumes "fdom a = fdom b"
    and "\<And> x y y2. \<lbrakk>
      x \<in> fdom a;
      x \<in> fdom b;
      lookup a x = Some y ;
      lookup b x = Some y2
      \<rbrakk>  \<Longrightarrow> y \<sqsubseteq> y2"
  shows "a \<sqsubseteq> b"
  using assms
  by (metis below_fmap_def lookup.rep_eq domIff fdom.rep_eq not_None_eq the.simps)


definition fmap_lub_raw where
  "fmap_lub_raw S = (\<lambda> x. 
      if (x \<in> dom (S 0))
      then Some (\<Squnion>i::nat. the (S i x))
      else None)"

lemma fmap_lub_raw_dom[simp]: "dom (fmap_lub_raw S) = dom (S 0)"
  by (auto simp add: fmap_lub_raw_def dom_def)  

lift_definition fmap_lub :: "(nat \<Rightarrow> ('key, 'value::po) fmap) \<Rightarrow> ('key, 'value) fmap" is "fmap_lub_raw"
  unfolding Lifting.invariant_def
  apply auto
  apply (erule  meta_allE[of _ 0])
  apply auto[1]
  apply (subgoal_tac "fun1 = fun2")
  apply auto
  done

find_theorems fmap_lub
thm fmap_lub.rep_eq

lemma fmap_below_dom:
  "a \<sqsubseteq> b \<Longrightarrow> fdom a = fdom b"
  unfolding below_fmap_def by simp

lemma is_lub_fmap:
  assumes "chain (S::nat => ('a::type, 'b::cpo) fmap)"
  shows "range S <<| fmap_lub S"
proof(rule is_lubI)

  def d \<equiv> "fdom (S 0)"
  have [simp]:"\<And>i . fdom (S i) = d"
    using chain_mono[OF `chain S`, of 0]
    unfolding d_def
    by (metis fmap_below_dom le0)
  hence [simp]: "fdom (fmap_lub S) = d"
    unfolding fmap_lub.rep_eq fdom.rep_eq fmap_lub_raw_def  dom_def
    by auto

{
  show "range S <| fmap_lub S"
  proof(rule is_ubI)
  case (goal1 m)
    then obtain i where "m = S i" by auto
    hence "S 0 \<sqsubseteq> m" using chain_mono[OF `chain S`] by auto

    have [simp]: "fdom m = d" using `m = S i` by simp

    show "m \<sqsubseteq> fmap_lub S"
    proof(rule fmap_belowI)
      fix x y y2
      assume "lookup (fmap_lub S) x = Some y2"

      assume "x \<in> fdom m"
      hence c2: "chain (\<lambda> i. the (Rep_fmap (S i) x))" using `chain S`
        unfolding chain_def below_fmap_def lookup.rep_eq
        by auto            

      assume "lookup m x = Some y"
      hence "y = the (Rep_fmap (S i) x)"  using `m = _` by (auto simp add: lookup.rep_eq)
      hence ylt: "y \<sqsubseteq> (\<Squnion>i::nat. the (Rep_fmap (S i) x))" 
          using is_ub_thelub[OF c2] by (auto simp add: lookup.rep_eq)

      have "x \<in> fdom (S 0) " using `x \<in> fdom m` by simp
      hence "lookup (fmap_lub S) x = Some (\<Squnion>i::nat. the (Rep_fmap (S i) x))"
        by (auto simp add: fmap_lub.rep_eq lookup.rep_eq fmap_lub_raw_def fdom.rep_eq)        
      thus "y \<sqsubseteq> y2" using `lookup m _ = _` ylt `lookup (fmap_lub S) x = Some y2`
        by simp
    qed simp
  qed
next
  fix u
  assume "range S <| u"

  hence [simp]: "fdom u = d"
    by (metis ub_rangeD  `\<And>i. fdom (S i) = d` fmap_below_dom)

  show "fmap_lub S \<sqsubseteq> u "
  proof(rule fmap_belowI)
    fix x
    fix y
    fix y2
    assume "lookup (fmap_lub S) x = Some y" 
    assume "lookup u x = Some y2" 
    hence "y2 = the (Rep_fmap u x)"  by (auto simp add: lookup.rep_eq)

    assume  "x \<in> fdom (fmap_lub S)"
    hence c2: "chain (\<lambda> i. the (Rep_fmap (S i) x))" (is "chain ?S2") using `chain S`
      unfolding chain_def below_fmap_def lookup.rep_eq
      by auto

    have "x \<in> fdom (S 0) " using `x \<in> fdom (fmap_lub S)` by simp
    hence "lookup (fmap_lub S) x = Some (lub (range ?S2))"
      by (auto simp add: fmap_lub.rep_eq lookup.rep_eq fmap_lub_raw_def fdom.rep_eq)        

    hence lub_at_x: "range ?S2 <<| the (lookup (fmap_lub S) x)"
      by (metis c2 the.simps thelubE)
    
    assume "x \<in> fdom u"
    have "range ?S2 <| the (lookup u x)"
      using ub_rangeD[OF `range S <| u`] `x \<in> fdom u`
      by (auto intro: ub_rangeI simp add:  below_fmap_def lookup.rep_eq)
     
    hence "the (lookup (fmap_lub S) x) \<sqsubseteq> the (lookup u x)"
      by (rule is_lubD2[OF lub_at_x])
    thus "y \<sqsubseteq> y2"
      using `_ = Some y` `_ = Some y2` by simp
  qed simp
}
qed

instance fmap :: (type, cpo) cpo
apply default
proof
  fix S :: "nat \<Rightarrow> ('a, 'b) fmap"
  assume "chain S"
  thus "range S <<| fmap_lub S"
    by (rule is_lub_fmap)
qed

lemma chain_iterate_from [simp]: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i\<cdot>F\<cdot>x)"
by (rule chainI, unfold iterate_Suc2, rule monofun_cfun_arg)

definition
  "fix1" :: "'a \<rightarrow> ('a::cpo \<rightarrow> 'a) \<rightarrow> 'a" where
  "fix1 = (\<Lambda> x F. \<Squnion>i. iterate i\<cdot>F\<cdot>x)"

lift_definition fmap_extend :: "('a, 'b::cpo) fmap \<Rightarrow> ('a, 'b) fmap  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda>m1 m2 x. (
    case m1 x of
      Some y1 \<Rightarrow> 
        (case m2 x of
          Some y2 \<Rightarrow> Some (lub {y1,y2})
          | None \<Rightarrow> Some y1
        )
      | None \<Rightarrow> 
        (case m2 x of
          Some y2 \<Rightarrow> Some y2
          | None \<Rightarrow> None
        )
     )"
  apply (rule_tac B = "dom fun1 \<union> dom fun2" in  finite_subset)
  by (auto simp add: map_def split add: option.split_asm)


definition fix_extend :: "('a, 'b::cpo) fmap \<Rightarrow> (('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap) \<Rightarrow> ('a, 'b) fmap"
  where
  "fix_extend h nh = fix1\<cdot>h\<cdot>(\<Lambda> h'. fmap_extend h' (nh h') )"

end
