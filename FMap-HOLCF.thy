theory "FMap-HOLCF"
  imports FMap "~~/src/HOL/HOLCF/HOLCF"
begin

default_sort type

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

primrec iterate :: "nat => ('a::cpo -> 'a) \<Rightarrow> ('a -> 'a)" where
    "iterate 0 F = (\<Lambda> x. x)"
  | "iterate (Suc n) F = (\<Lambda> x. F\<cdot>(iterate n F\<cdot>x))"

lemma iterate_Suc2: "iterate (Suc n) F \<cdot>x = iterate n F\<cdot>(F\<cdot>x)"
by (induct n) simp_all

lemma chain_iterate_from [simp]: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i F\<cdot>x)"
by (rule chainI, unfold iterate_Suc2, rule monofun_cfun_arg)

definition
  "fix1" :: "'a \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<Rightarrow> 'a" where
  "fix1 x F = (\<Squnion>i. iterate i F\<cdot>x)"

lemma iterate_below_fix: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> iterate n F \<cdot> x \<sqsubseteq> fix1 x F"
  unfolding fix1_def
  using chain_iterate_from
  by (rule is_ub_thelub)

lemma fix_eq: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow>  fix1 x F = F\<cdot>(fix1 x F)"
  apply (simp add: fix1_def)
  apply (subst lub_range_shift [of _ 1, symmetric])
  apply (erule chain_iterate_from)
  apply (subst contlub_cfun_arg)
  apply (erule chain_iterate_from)
  apply simp
  done

lemma iterate_stays_above: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> x \<sqsubseteq> iterate n F \<cdot> x"
  apply (rule nat_induct)
  apply simp
  by (metis "FMap-HOLCF.iterate_Suc2" monofun_cfun_arg rev_below_trans)

lemma fix1_ind: "\<lbrakk> adm P; P x; x \<sqsubseteq> F\<cdot>x; \<And>y. \<lbrakk>x \<sqsubseteq> y ; P y\<rbrakk> \<Longrightarrow> P (F\<cdot>y) \<rbrakk> \<Longrightarrow> P (fix1 x F)"
  unfolding fix1_def
  apply (erule admD)
  apply (erule chain_iterate_from)
  apply (rule nat_induct)
  apply (simp_all add: iterate_stays_above)
  done

lemma fix1_ind2:
  assumes adm: "adm P"
  assumes above: "x \<sqsubseteq> F\<cdot>x"
  assumes 0: "P x" and 1: "P (F\<cdot>x)"
  assumes step: "!!y. \<lbrakk>x \<sqsubseteq> y ; P y; P (F\<cdot>y)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>y))"
  shows "P (fix1 x F)"
  unfolding fix1_def
  apply (rule admD [OF adm chain_iterate_from[OF above]])
  apply (rule nat_less_induct)
  apply (case_tac n)
  apply (simp add: 0)
  apply (case_tac nat)
  apply (simp add: 1)
  apply (frule_tac x=nat in spec)
  apply (simp add: step iterate_stays_above[OF above])
done

lemma parallel_fix1_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes aboveF: "x1 \<sqsubseteq> F\<cdot>x1"
  assumes aboveG: "x2 \<sqsubseteq> G\<cdot>x2"
  assumes base: "P x1 x2"
  assumes step: "!!y z. \<lbrakk> x1 \<sqsubseteq> y ; x2 \<sqsubseteq> z; P y z \<rbrakk> \<Longrightarrow> P (F\<cdot>y) (G\<cdot>z)"
  shows "P (fix1 x1 F) (fix1 x2 G)"
proof -
  from adm have adm': "adm (split P)"
    unfolding split_def .
  have "!!i. P (iterate i F\<cdot>x1) (iterate i G\<cdot>x2)"
    by (induct_tac i, simp add: base, simp add: step iterate_stays_above[OF aboveF] iterate_stays_above[OF aboveG])
  hence "!!i. split P (iterate i F\<cdot>x1, iterate i G\<cdot>x2)"
    by simp
  hence "split P (\<Squnion>i. (iterate i F\<cdot>x1, iterate i G\<cdot>x2))"
    apply - apply (rule admD [OF adm']) by(auto intro: ch2ch_Pair simp add: chain_iterate_from[OF aboveF] chain_iterate_from[OF aboveG])
  hence "split P (\<Squnion>i. iterate i F\<cdot>x1, \<Squnion>i. iterate i G\<cdot>x2)"
    by (simp add: lub_Pair chain_iterate_from[OF aboveF] chain_iterate_from[OF aboveG])
  hence "P (\<Squnion>i. iterate i F\<cdot>x1) (\<Squnion>i. iterate i G\<cdot>x2)"
    by simp
  thus "P (fix1 x1 F) (fix1 x2 G)"
    by (simp add: fix1_def)
qed

definition max where "max x y = (if x \<sqsubseteq> y then y else x)"

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
  "fix_extend h nh = fix1 h (\<Lambda> h'. fmap_extend h' (nh h') )"

end
