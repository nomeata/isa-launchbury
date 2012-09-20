theory "FMap-HOLCF"
  imports FMap "HOLCF-Binary-Meet" "Fix1" "FixRestr"
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
  by (metis rev_below_trans)
next
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x"
  thus "x = y"
  by (metis "FMap-HOLCF.below_fmap_def" fmap_eqI po_eq_conv)
qed
end

lemma fmap_belowI':
  assumes "fdom a = fdom b"
    and "\<And> x. \<lbrakk>
      x \<in> fdom a;
      x \<in> fdom b
      \<rbrakk>  \<Longrightarrow> the (lookup a x) \<sqsubseteq> the (lookup b x)"
  shows "a \<sqsubseteq> b"
  using assms
  by (metis below_fmap_def)

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

lemma fmap_belowE:
  assumes "m1 \<sqsubseteq> m2"
  shows "the (lookup m1 x) \<sqsubseteq> the (lookup m2 x)"
  apply (cases "x \<in> fdom m1")
  using assms
  apply (metis below_fmap_def)
  using assms unfolding below_fmap_def
  apply (transfer, auto)
  done

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
  assumes "chain (S::nat => ('a, 'b::cpo) fmap)"
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

lemma unfold_lub_fmap:  "chain (Y::nat => ('a, 'b::cpo) fmap) \<Longrightarrow> lub (range Y) = fmap_lub Y"
  by (rule lub_eqI, rule is_lub_fmap)

lemma chain_fdom:
  assumes "chain (Y :: nat \<Rightarrow> ('a\<Colon>type, 'b\<Colon>cpo) fmap) "
  shows "fdom (Y i) = fdom (Y 0)" and "fdom (\<Squnion> i. Y i) = fdom (Y 0)"
proof-
    have "Y 0 \<sqsubseteq> Y i" apply (rule chain_mono[OF `chain Y`]) by simp
    thus "fdom (Y i) = fdom (Y 0)" by-(drule fmap_below_dom, rule sym)
    moreover
    have "Y 0 \<sqsubseteq> (\<Squnion>i . Y i)"  by (rule is_ub_thelub[OF `chain Y`])
    thus "fdom (\<Squnion> i. Y i) = fdom (Y 0)" by-(drule fmap_below_dom, rule sym)
qed

lemma lookup_chain:
  assumes "chain (Y :: nat \<Rightarrow> ('a, 'b::cpo) fmap)"
  shows "chain (\<lambda> i . the (lookup (Y i) x))"
proof(rule chainI)
  fix i 
  have "fdom (Y i) = fdom (Y 0)" and
       "fdom (Y (Suc i)) = fdom (Y 0)" and
       "fdom (Y j) = fdom (Y 0)"
       by (intro chain_fdom[OF `chain Y`])+
  have "Y i \<sqsubseteq> Y (Suc i)" using `chain _` by (rule chainE)
    hence "fdom (Y (Suc i)) = fdom (Y i)" unfolding below_fmap_def by simp
  show "the (lookup (Y i) x) \<sqsubseteq> the (lookup (Y (Suc i)) x)"
    proof(cases "x \<in> fdom (Y i)")
    case True thus ?thesis using `_ \<sqsubseteq> _`  by (simp add: below_fmap_def)
    next
    case False
      hence "the (lookup (Y i) x) = the None"
        by (transfer, auto simp add: dom_def)
      moreover
      have "x \<notin> fdom (Y (Suc i))"
        using False `fdom (Y (Suc i)) = fdom (Y i)` by simp
      hence "the (lookup (Y (Suc i)) x) = the None"
        by (transfer, auto simp add: dom_def)
      ultimately show ?thesis by simp
    qed
qed

lemma lookup_cont:
  assumes "chain (Y :: nat \<Rightarrow> ('a, 'b::cpo) fmap)"
  shows "the (lookup (\<Squnion> i. Y i) x) = (\<Squnion> i. the (lookup (Y i) x))"
proof(cases "x \<in> fdom (Y 0)")
case True thus ?thesis
  unfolding unfold_lub_fmap[OF `chain Y`]
  apply transfer
  apply (auto simp add: fmap_lub_raw_def)
  done
next
case False
  have "\<And> i. lookup (Y i) x = None"
    by (metis False assms chain_fdom(1) domIff fdom.rep_eq lookup.rep_eq)
  thus ?thesis
    unfolding unfold_lub_fmap[OF `chain Y`]
    by (transfer, auto simp add: fmap_lub_raw_def)
qed

lemma cont2cont_lookup[simp,cont2cont]:
  assumes "cont f"
  shows "cont (\<lambda>p :: ('a, 'b::cpo) fmap. the (lookup (f p) x))"
proof (rule cont_compose[OF _ `cont f`], rule contI)
  fix Y :: "nat \<Rightarrow> ('c, 'd::cpo) fmap"
  assume "chain Y"
  show "range (\<lambda>i. the (lookup (Y i) x)) <<| the (lookup (\<Squnion> i. Y i) x)"
    by (subst lookup_cont[OF `chain Y`], rule cpo_lubI[OF lookup_chain[OF `chain Y`]])
qed

lemma fmap_contI:
  assumes "\<And> x y . x \<sqsubseteq> y \<Longrightarrow> fdom (f x) = fdom (f y)"
  and "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> z \<in> fdom (f x) \<Longrightarrow> z \<in> fdom (f y) \<Longrightarrow> the (lookup (f x) z) \<sqsubseteq> the (lookup (f y) z)" (is "PROP ?a2")
  and "\<And> Y x. chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i)) \<Longrightarrow>
       x \<in> fdom (f (\<Squnion> i. Y i)) \<Longrightarrow> x \<in> fdom (\<Squnion> i. f (Y i)) \<Longrightarrow>
       the (lookup (f (\<Squnion> i. Y i)) x) \<sqsubseteq> the (lookup (\<Squnion> i. f (Y i)) x)" (is "PROP ?a3") 
  shows "cont (f :: 'c::cpo \<Rightarrow> ('a, 'b::cpo) fmap)  "
proof(intro contI2 monofunI fmap_belowI')
  fix x y :: 'c
  assume "x \<sqsubseteq> y"
  thus "fdom (f x) = fdom (f y)" using assms(1) by auto
next
  next
  fix Y
  assume c1: "chain (Y :: nat \<Rightarrow> 'c)"
  assume c2: "chain (\<lambda>i. f (Y i))"
  have "Y 0 \<sqsubseteq> Lub Y" by (metis is_ub_thelub[OF c1])
  hence "fdom (f (Y 0)) = fdom (f (Lub Y))" using assms(1) by auto
  thus "fdom (f (\<Squnion> i. Y i)) = fdom (\<Squnion> i. f (Y i))"
    by (simp add: chain_fdom(2)[OF c2])
qed fact+

lemma fmap_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. fmap_upd (f x) v (h x) :: ('a, 'b::cpo) fmap)"
proof (intro contI2  monofunI fmap_belowI')
  fix x1 x2 :: 'c
  assume "x1 \<sqsubseteq> x2"
  hence "f x1 \<sqsubseteq> f x2" by -(erule cont2monofunE[OF `cont f`])
  thus "fdom (f x1(v f\<mapsto> h x1)) = fdom (f x2(v f\<mapsto> h x2))"
    by (simp add: fmap_below_dom)

  (*  have finite_transfer[transfer_rule]: "(op = ===> op =) \<sqsubseteq> \<sqsubseteq>" 
  unfolding fun_rel_eq by (rule refl) *)

  fix v'
  assume "v' \<in> fdom (f x1(v f\<mapsto> h x1))"  and "v' \<in> fdom (f x2(v f\<mapsto> h x2))"
  thus "the (lookup (f x1(v f\<mapsto> h x1)) v') \<sqsubseteq> the (lookup (f x2(v f\<mapsto> h x2)) v')"
  proof(cases "v = v'")
    case True
    thus ?thesis
      using cont2monofunE[OF `cont h` `x1 \<sqsubseteq> x2`]
      by (transfer, auto)
  next
    case False
    moreover
    with ` v' \<in> fdom (f x1(v f\<mapsto> h x1))` `v' \<in> fdom (f x2(v f\<mapsto> h x2))`
    have "v' \<in> fdom (f x1)" and "v' \<in> fdom (f x2)" by auto
    moreover
    have "the (lookup (f x1) v') \<sqsubseteq> the (lookup (f x2) v')"
      by (rule fmap_belowE[OF cont2monofunE[OF `cont f` `x1 \<sqsubseteq> x2`]])
    ultimately
    show  ?thesis  by (transfer, simp)
  qed

next
  fix Y
  assume c1: "chain (Y :: nat \<Rightarrow> 'c)"
  assume c2: "chain (\<lambda>i. f (Y i)(v f\<mapsto> h (Y i)))"
  have "Y 0 \<sqsubseteq> Lub Y" by (metis is_ub_thelub[OF c1])
  hence "f (Y 0) \<sqsubseteq> f (Lub Y)" by (rule cont2monofunE[OF `cont f`])
  hence "fdom (f (Y 0)) = fdom (f (Lub Y))" by (rule fmap_below_dom)

  thus "fdom (f (\<Squnion> i. Y i)(v f\<mapsto> h (\<Squnion> i. Y i))) = fdom (\<Squnion> i. f (Y i)(v f\<mapsto> h (Y i)))"
    by (simp add: chain_fdom(2)[OF c2])

  fix v'
  show "the (lookup (f (\<Squnion> i. Y i)(v f\<mapsto> h (\<Squnion> i. Y i))) v') \<sqsubseteq> the (lookup (\<Squnion> i. f (Y i)(v f\<mapsto> h (Y i))) v') "
  proof(cases "v = v'")
    case True
    thus ?thesis
      using lookup_cont[OF c2]  cont2contlubE[OF `cont h` c1]
      by simp
  next
    case False
    thus ?thesis
      using lookup_cont[OF c2] cont2contlubE[OF `cont f` c1]
            lookup_cont[OF ch2ch_cont[OF `cont f` `chain Y`]]
      by simp
  qed
qed      

lemma fdom_pred_adm[intro]: "adm (\<lambda> a. P (fdom a))" 
  by (rule admI, metis chain_fdom(2))

lemma fdom_fix1[simp]: assumes "x \<sqsubseteq> F\<cdot>x" shows "fdom (fix1 x F) = fdom x"
  apply (rule fix1_ind[OF fdom_pred_adm refl assms])
  using  fmap_below_dom[OF monofun_cfun_arg[of x _ F]]  fmap_below_dom[OF assms]
  by auto

lemma fdom_chainFrom_funpow[simp]: "chainFrom F x ==> fdom ((F^^i) x) = fdom x"
  apply (induct i)
  apply simp
  by (metis FixRestr.iterate_stays_above fmap_below_dom)

lemma fdom_chainFrom_funpow2[simp]: "chainFrom F x ==> fdom (F ((F^^i) x)) = fdom x"
  by (metis fdom_chainFrom_funpow funpow.simps(2) o_apply)

lemma fdom_fixR[simp]: assumes "chainFrom F x" shows "fdom (fixR x F) = fdom x"
  apply (rule fixR_ind[OF fdom_pred_adm refl assms])
  by (simp add: fdom_chainFrom_funpow2[OF assms])

lemma fixR_cong: 
  assumes "chainFrom F a" and "chainFrom G a"
      and "\<And> x. fdom x = fdom a \<Longrightarrow> F x = G x"
  shows "fixR a F = fixR a G"
  apply (rule parallel_fixR_ind[OF _ assms(1) assms(2) refl])
  apply auto[1]
  by (metis fmap_below_dom assms(3))

lemma fix1_cong: 
  assumes "a \<sqsubseteq> F \<cdot> a" and "a \<sqsubseteq> G \<cdot> a"
      and "\<And> x. fdom x = fdom a \<Longrightarrow> F\<cdot>x = G\<cdot>x"
  shows "fix1 a F = fix1 a G"
  apply (rule parallel_fix1_ind[OF _ assms(1) assms(2) refl])
  apply auto[1]
  by (metis fmap_below_dom assms(3))


lift_definition fmap_update :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda>m1 m2 x. (
    case m2 x of Some y1 \<Rightarrow> Some y1 | None \<Rightarrow> m1 x 
     )"
  apply (rule_tac B = "dom fun1 \<union> dom fun2" in  finite_subset)
  by (auto simp add: map_def split add: option.split_asm)

lemma fdom_fmap_update[simp]: "fdom (fmap_update m1 m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto simp add: dom_def split:option.split)

lemma lookup_fmap_update1[simp]: "x \<in> fdom m2 \<Longrightarrow> lookup (fmap_update m1 m2) x = lookup m2 x"
  by (transfer, auto)

lemma lookup_fmap_update2[simp]:  "x \<notin> fdom m2 \<Longrightarrow> lookup (fmap_update m1 m2) x = lookup m1 x"
  by (transfer, auto simp add: dom_def )

lemma [simp]: "fmap_update \<rho> fempty = \<rho>"
  by (transfer, auto)

lemma fmap_update_rho[simp]: "fmap_update \<rho> (fmap_update \<rho> x) = fmap_update \<rho> x"
  by (transfer, auto split add: option.split)

lemma fmap_update_cont1: "cont (\<lambda> x. fmap_update x (m::('a, 'b::cpo) fmap))"
proof(rule fmap_contI)
  fix x y :: "('a, 'b::cpo) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (fmap_update x m) = fdom (fmap_update y m)"  by simp 
next
  fix x y :: "('a, 'b::cpo) fmap"
  assume "x \<sqsubseteq> y"
  fix z :: 'a  
  show "the (lookup (fmap_update x m) z) \<sqsubseteq> the (lookup (fmap_update y m) z)"
    using `x \<sqsubseteq> y`
    by(cases "z \<in> fdom m", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> ('a, 'b::cpo) fmap"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. fmap_update (Y i) m)"
  fix x :: 'a
  show "the (lookup (fmap_update (\<Squnion> i. Y i) m) x) \<sqsubseteq> the (lookup (\<Squnion> i. fmap_update (Y i) m) x)"
    by (cases "x \<in> fdom m", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_update_cont2: "cont (\<lambda> x. fmap_update m (x::('a, 'b::cpo) fmap))"
proof(rule fmap_contI)
  fix x y :: "('a, 'b::cpo) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (fmap_update m x) = fdom (fmap_update m y)" by simp
next
  fix x y :: "('a, 'b::cpo) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  fix z :: 'a  
  show "the (lookup (fmap_update m x) z) \<sqsubseteq> the (lookup (fmap_update m y) z)"
    using `x \<sqsubseteq> y` `fdom x = fdom y`
    by(cases "z \<in> fdom x", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> ('a, 'b::cpo) fmap"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. fmap_update m (Y i))"
    hence [simp]:"\<And> i. fdom (Y i) =  fdom (\<Squnion> i . Y i)"
      by (metis chain_fdom(1) chain_fdom(2))
  fix x :: 'a
  show "the (lookup (fmap_update m (\<Squnion> i. Y i)) x) \<sqsubseteq> the (lookup (\<Squnion> i. fmap_update m (Y i)) x)"
    by (cases "x \<in> fdom (\<Squnion> i . Y i)", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_update_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_update (f x) (g x :: ('a, 'b::cpo) fmap))"
by (rule cont_apply[OF assms(1) fmap_update_cont1 cont_compose[OF fmap_update_cont2 assms(2)]])

lemma fmap_update_upd_swap: 
  "x \<notin> fdom \<rho>' \<Longrightarrow> fmap_update (\<rho>(x f\<mapsto> z)) \<rho>' = (fmap_update \<rho> \<rho>')(x f\<mapsto> z)"
  apply (rule fmap_eqI[rule_format])
  apply auto[1]
  apply (case_tac "x = xa")
  apply auto[1]
  apply (case_tac "xa \<in> fdom \<rho>'")
  apply (auto)
  done

(* A definition of fmap_meep that requires compatible fmaps *)

lift_definition fmap_meet :: "('a, 'b::pcpo) fmap \<Rightarrow> ('a, 'b) fmap  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda>m1 m2 x. (
    case m1 x of
      Some x1 \<Rightarrow> case m2 x of
        Some x2 => Some (x1 \<squnion> x2)
        | None => Some x1
      | None \<Rightarrow> m2 x 
     )"
  apply (rule_tac B = "dom fun1 \<union> dom fun2" in  finite_subset)
  by (auto simp add: map_def split add: option.split_asm)

lemma fdom_fmap_meet[simp]: "fdom (fmap_meet m1 m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto simp add: dom_def split:option.split)

lemma [simp]: "fmap_meet \<rho> fempty = \<rho>"
  by (transfer, auto split:option.split)

lemma [simp]: "fmap_meet fempty \<rho> = \<rho>"
  by (transfer, auto split:option.split)

definition compatible :: "'a::po \<Rightarrow> 'a \<Rightarrow> bool"
  where "compatible x y = (\<exists> z. {x, y} <<| z)"

definition compatible_fmap :: "('a, 'b::po) fmap  \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool"
  where "compatible_fmap m1 m2 = (\<forall> z \<in> fdom m1 \<inter> fdom m2 . compatible (the (lookup m1 z)) (the (lookup m2 z)))"


lift_definition fmap_extend :: "('a, 'b::pcpo) fmap \<Rightarrow> 'a set  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda> m1 S. (if finite S then (\<lambda> x. if x \<in> S then Some \<bottom> else m1 x) else empty)"
  apply (case_tac "finite set")
  apply (rule_tac B = "dom fun \<union> set" in   finite_subset)
  apply auto
  done

lift_definition fmap_bottom :: "'a set  \<Rightarrow> ('a, 'b::pcpo) fmap"
  is "\<lambda> S. (if finite S then (\<lambda> x. if x \<in> S then Some \<bottom> else None) else empty)"
  apply (case_tac "finite set")
  apply (rule_tac B = "set" in  finite_subset)
  apply (auto simp add: dom_def)
  done

lemma fdom_fmap_bottom[simp]: "finite S \<Longrightarrow> fdom (fmap_bottom S) = S"
  by (transfer, auto simp add: dom_def)

lemma fmap_bottom_lookup[simp]: "\<lbrakk> x \<in> S ; finite S \<rbrakk> \<Longrightarrow> lookup (fmap_bottom S) x = Some \<bottom>"
  by (transfer, auto)

lemma[simp]: "fmap_bottom {} = fempty"
  by (rule, auto)

lemma fmap_bottom_below[simp]:
  "S = fdom \<rho> \<Longrightarrow> fmap_bottom S \<sqsubseteq> \<rho>"
 by(rule fmap_belowI, auto)


definition fix_extend :: "('a, 'b::pcpo) fmap \<Rightarrow> 'a set \<Rightarrow> (('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap) \<Rightarrow> ('a, 'b) fmap"
  where
  "fix_extend h S nh = fmap_update h (fix1 (fmap_bottom S)  (\<Lambda> h'. (nh (fmap_update h h') )))"

instantiation fmap :: (type,pcpo) order
begin
  definition "(\<rho>::('a,'b) fmap) \<le> \<rho>' = ((fdom \<rho> \<subseteq> fdom \<rho>') \<and> (\<forall>x \<in> fdom \<rho>. lookup \<rho> x = lookup \<rho>' x))"
  definition "(\<rho>::('a,'b) fmap) < \<rho>' = (\<rho> \<noteq> \<rho>' \<and> \<rho> \<le> \<rho>')"

lemma fmap_less_eqI[intro]:
  assumes assm1: "fdom (\<rho>::('a,'b) fmap) \<subseteq> fdom \<rho>'"
    and assm2:  "\<And> x. \<lbrakk> x \<in> fdom \<rho> ; x \<in> fdom \<rho>'  \<rbrakk> \<Longrightarrow> the (lookup \<rho> x) = the (lookup \<rho>' x) "
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
  assumes "(\<rho>::('a,'b) fmap) \<le> \<rho>'"
  assumes "x \<in> fdom \<rho>"
  shows "lookup \<rho> x = lookup \<rho>' x"
  using assms
  unfolding less_eq_fmap_def by auto


lemma fmap_antisym: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> x" shows "x = y "
proof(rule fmap_eqI[rule_format])
    show "fdom x = fdom y" using `x \<le> y` and `y \<le> x` unfolding less_eq_fmap_def by auto
    
    fix v
    assume "v \<in> fdom x"
    hence "v \<in> fdom y" using `fdom _ = _` by simp

    thus "the (lookup x v) = the (lookup y v)"
      using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by simp
  qed

lemma fmap_trans: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> z" shows "x \<le> z"
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
  show "the (lookup x v) = the (lookup z v)" by auto
qed

instance
  apply default
  using fmap_antisym apply (auto simp add: less_fmap_def)[1]
  apply (auto simp add: less_eq_fmap_def)[1]
  using fmap_trans apply assumption
  using fmap_antisym apply assumption
  done
end


(*

instantiation fmap :: (type,pcpo) order
begin
  definition "(\<rho>::('a,'b) fmap) \<le> \<rho>' = ((fdom \<rho> \<subseteq> fdom \<rho>') \<and> (\<forall>x \<in> fdom \<rho>. lookup \<rho> x \<noteq> Some \<bottom> \<longrightarrow> lookup \<rho> x = lookup \<rho>' x))"
  definition "(\<rho>::('a,'b) fmap) < \<rho>' = (\<rho> \<noteq> \<rho>' \<and> \<rho> \<le> \<rho>')"

lemma fmap_less_eqI[intro]:
  assumes assm1: "fdom (\<rho>::('a,'b) fmap) \<subseteq> fdom \<rho>'"
    and assm2:  "\<And> x. \<lbrakk> x \<in> fdom \<rho> ; x \<in> fdom \<rho>' ; lookup \<rho> x \<noteq> Some \<bottom> \<rbrakk> \<Longrightarrow> the (lookup \<rho> x) = the (lookup \<rho>' x) "
   shows "\<rho> \<le> \<rho>'"
 unfolding less_eq_fmap_def
 apply rule
 apply fact
 apply rule+
 apply (frule subsetD[OF `_ \<subseteq> _`])
 apply (frule (2) assm2)
 apply (auto iff: fdomIff)
 done

lemma fmap_less_eqD:
  assumes "(\<rho>::('a,'b) fmap) \<le> \<rho>'"
  assumes "x \<in> fdom \<rho>"
  assumes "lookup \<rho> x \<noteq> Some \<bottom>"
  shows "lookup \<rho> x = lookup \<rho>' x"
  using assms
  unfolding less_eq_fmap_def by auto


lemma fmap_antisym: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> x" shows "x = y "
proof(rule fmap_eqI[rule_format])
    show "fdom x = fdom y" using `x \<le> y` and `y \<le> x` unfolding less_eq_fmap_def by auto
    
    fix v
    assume "v \<in> fdom x"
    hence "v \<in> fdom y" using `fdom _ = _` by simp

    { assume "lookup x v \<noteq> Some \<bottom>"
      hence "the (lookup x v) = the (lookup y v)"
        using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by simp
    }
    moreover
    { assume "lookup y v \<noteq> Some \<bottom>"
      hence "the (lookup x v) = the (lookup y v)"
        using `y \<le> x` `v \<in> fdom y` unfolding less_eq_fmap_def by simp
    }
    ultimately
    show "the (lookup x v) = the (lookup y v)"
      using `v \<in> fdom x` `v \<in> fdom y`
      by (auto iff: fdomIff, blast)
  qed

lemma fmap_trans: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> z" shows "x \<le> z"
proof
  show "fdom x \<subseteq> fdom z" using `x \<le> y` and `y \<le> z` unfolding less_eq_fmap_def
    by -(rule order_trans [of _ "fdom y"], auto)
  
  fix v
  assume "v \<in> fdom x" and "v \<in> fdom z"
  hence "v \<in> fdom y" using `x \<le> y`  unfolding less_eq_fmap_def by auto
  assume "lookup x v \<noteq> Some \<bottom>"
  hence "lookup y v = lookup x v"
    using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by auto
  moreover
  hence "lookup y v \<noteq> Some \<bottom>"
    using `lookup x v \<noteq> Some \<bottom>` by simp
  hence "lookup y v = lookup z v"
    by (rule fmap_less_eqD[OF `y \<le> z`  `v \<in> fdom y`])
  ultimately
  show "the (lookup x v) = the (lookup z v)" by auto
qed

instance
  apply default
  using fmap_antisym apply (auto simp add: less_fmap_def)[1]
  apply (auto simp add: less_eq_fmap_def)[1]
  using fmap_trans apply assumption
  using fmap_antisym apply assumption
  done
end
*)
end
