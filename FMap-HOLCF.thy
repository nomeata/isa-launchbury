theory "FMap-HOLCF"
  imports FMap "HOLCF-Join" "HOLCF-Set"
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
  fixes f :: "'a::cpo \<Rightarrow> ('b::type, 'c::cpo) fmap"
  assumes "cont f"
  shows "cont (\<lambda>p. the (lookup (f p) x))"
proof (rule cont_compose[OF _ `cont f`], rule contI)
  fix Y :: "nat \<Rightarrow> ('b::type, 'c::cpo) fmap"
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

lemma fmap_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x f\<mapsto> v1) \<sqsubseteq> \<rho>2(x f\<mapsto> v2)"
  apply (rule fmap_belowI')
  apply (auto dest:fmap_below_dom)[1]
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fmap_belowE)
  done

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

(*
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
*)


lemma  fmap_add_belowI:
  assumes "fdom x \<union> fdom y = fdom z"
  and "\<And> a. a \<in> fdom y \<Longrightarrow> the (lookup y a) \<sqsubseteq> the (lookup z a)"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> a \<notin> fdom y \<Longrightarrow> the (lookup x a) \<sqsubseteq> the (lookup z a)"
  shows  "fmap_add x y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI)
  apply auto[1]
  by (metis fdomIff lookup_fmap_add1 lookup_fmap_add2 the.simps)

lemma fmap_add_cont1: "cont (\<lambda> x. fmap_add x (m::('a::type, 'b::cpo) fmap))"
proof(rule fmap_contI)
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (fmap_add x m) = fdom (fmap_add y m)"  by simp 
next
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y"
  fix z :: 'a  
  show "the (lookup (fmap_add x m) z) \<sqsubseteq> the (lookup (fmap_add y m) z)"
    using `x \<sqsubseteq> y`
    by(cases "z \<in> fdom m", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> ('a, 'b) fmap"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. fmap_add (Y i) m)"
  fix x :: 'a
  show "the (lookup (fmap_add (\<Squnion> i. Y i) m) x) \<sqsubseteq> the (lookup (\<Squnion> i. fmap_add (Y i) m) x)"
    by (cases "x \<in> fdom m", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_add_cont2: "cont (\<lambda> x. fmap_add m (x::('a::type, 'b::cpo) fmap))"
proof(rule fmap_contI)
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (fmap_add m x) = fdom (fmap_add m y)" by simp
next
  fix x y :: "('a, 'b) fmap"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  fix z :: 'a  
  show "the (lookup (fmap_add m x) z) \<sqsubseteq> the (lookup (fmap_add m y) z)"
    using `x \<sqsubseteq> y` `fdom x = fdom y`
    by(cases "z \<in> fdom x", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> ('a, 'b) fmap"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. fmap_add m (Y i))"
    hence [simp]:"\<And> i. fdom (Y i) =  fdom (\<Squnion> i . Y i)"
      by (metis chain_fdom(1) chain_fdom(2))
  fix x :: 'a
  show "the (lookup (fmap_add m (\<Squnion> i. Y i)) x) \<sqsubseteq> the (lookup (\<Squnion> i. fmap_add m (Y i)) x)"
    by (cases "x \<in> fdom (\<Squnion> i . Y i)", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_add_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_add (f x) (g x :: ('a, 'b::cpo) fmap))"
by (rule cont_apply[OF assms(1) fmap_add_cont1 cont_compose[OF fmap_add_cont2 assms(2)]])

lemma fmap_add_mono:
  assumes "x1 \<sqsubseteq> (x2 :: ('a::type, 'b::cpo) fmap)"
  assumes "y1 \<sqsubseteq> y2"
  shows "fmap_add x1 y1 \<sqsubseteq> fmap_add x2 y2"
by (rule below_trans[OF cont2monofunE[OF fmap_add_cont1 assms(1)] cont2monofunE[OF fmap_add_cont2 assms(2)]])

lemma fmap_upd_belowI:
  assumes "fdom \<rho>' = insert x (fdom \<rho>)"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> the (lookup \<rho> z) \<sqsubseteq> the (lookup \<rho>' z)" 
  assumes "y \<sqsubseteq> the (lookup \<rho>' x)"
  shows  "\<rho>(x f\<mapsto> y) \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI')
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_upd_belowI2:
  assumes "fdom \<rho> = insert x (fdom \<rho>')"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> the (lookup \<rho> z) \<sqsubseteq> the (lookup \<rho>' z)" 
  assumes "the (lookup \<rho> x) \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x f\<mapsto> y)"
  apply (rule fmap_belowI')
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done


lemma fmap_restr_belowI:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> the (lookup (fmap_restr S m1) x) \<sqsubseteq> the (lookup (fmap_restr S m2) x)"
  and "fdom m1 = fdom m2"
  shows "fmap_restr S m1 \<sqsubseteq> fmap_restr S m2"
proof (cases "finite S")
case True thus ?thesis
  apply -
  apply (rule fmap_belowI)
  apply (simp add: `fdom m1 = fdom m2`)
  by (metis Int_iff assms(1) fdom_fmap_restr the.simps)
next
case False thus ?thesis unfolding fmap_restr_def by simp
qed

lemma fmap_restr_belowI2:
  assumes "finite S"
  assumes "fdom m2 = fdom m1 \<inter> S"
  assumes  "\<And> x. x \<in> S \<Longrightarrow> x \<in> fdom m1 \<Longrightarrow> the (lookup m1 x) \<sqsubseteq> the (lookup m2 x)"
  shows "fmap_restr S m1 \<sqsubseteq> m2"
  apply (rule fmap_belowI')
  apply (simp add: assms(1,2))
  apply (simp add: assms(1,2))
  apply (rule assms(3))
  by auto

lemma fmap_restr_monofun:  "monofun (fmap_restr S)"
proof (cases "finite S")
  case True thus ?thesis
    apply -
    apply (rule monofunI)
    apply (rule fmap_restr_belowI)
    apply (subst lookup_fmap_restr[OF True], assumption)+
    apply (metis fmap_belowE)
    by (metis fmap_below_dom)
next
case False thus ?thesis  by -(rule monofunI, simp add: fmap_restr_def)
qed

lemma fmap_restr_cont:  "cont (fmap_restr S)"
proof(cases "finite S")
case True thus ?thesis apply -
  apply (rule contI2[OF fmap_restr_monofun])
  apply (rule fmap_belowI')
  apply (simp add: chain_fdom(2))[1]
  apply auto
  apply (subst lookup_cont, assumption)+
  apply (rule lub_mono[OF lookup_chain lookup_chain], assumption+)
  apply (subst lookup_fmap_restr[OF True], assumption)
  apply (rule below_refl)
  done
next
case False thus ?thesis by -(rule contI2[OF fmap_restr_monofun], simp add: fmap_restr_def)
qed

lemmas fmap_restr_cont2cont[simp,cont2cont] = cont_compose[OF fmap_restr_cont]

lemma fmap_restr_l_cont:
  "cont (fmap_restr_l l)" unfolding fmap_restr_l_def by (rule fmap_restr_cont)


(* A definition of fmap_meep that requires compatible fmaps *)

lift_definition fmap_join :: "('a, 'b::pcpo) fmap \<Rightarrow> ('a, 'b) fmap  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda>m1 m2 x. (
    case m1 x of
      Some x1 \<Rightarrow> case m2 x of
        Some x2 => Some (x1 \<squnion> x2)
        | None => Some x1
      | None \<Rightarrow> m2 x 
     )"
  apply (rule_tac B = "dom fun1 \<union> dom fun2" in  finite_subset)
  by (auto simp add: map_def split add: option.split_asm)

lemma fdom_fmap_join[simp]: "fdom (fmap_join m1 m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto simp add: dom_def split:option.split)

lemma [simp]: "fmap_join \<rho> fempty = \<rho>"
  by (transfer, auto split:option.split)

lemma [simp]: "fmap_join fempty \<rho> = \<rho>"
  by (transfer, auto split:option.split)

lift_definition compatible_fmap :: "('a, 'b::pcpo) fmap  \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool"
  is "\<lambda> m1 m2 . (\<forall> z \<in> dom m1 \<inter> dom m2 . compatible (the (m1 z)) (the (m2 z)))"..

lemma compatible_fmap_def':
  "compatible_fmap m1 m2 = (\<forall> z \<in> fdom m1 \<inter> fdom m2 . compatible (the (lookup m1 z)) (the (lookup m2 z)))"
  by (transfer, rule)

lemma compatible_fmapI:
  assumes "\<And> x. \<lbrakk> x \<in> fdom m1 ; x \<in> fdom m2 \<rbrakk> \<Longrightarrow> compatible (the (lookup m1 x)) (the (lookup m2 x))"
  shows "compatible_fmap m1 m2"
  unfolding compatible_fmap_def' using assms by auto

lemma compatible_fmapE:
  assumes "compatible_fmap m1 m2"
  assumes "x \<in> fdom m1"
  assumes "x \<in> fdom m2"
  shows "compatible (the (lookup m1 x)) (the (lookup m2 x))"
  using assms unfolding compatible_fmap_def' by auto

lemma [simp]:
  "compatible_fmap fempty \<rho>" 
  "compatible_fmap \<rho> fempty"
  by (transfer, simp)+

lemma fmap_join_rho[simp]:
  "compatible_fmap \<rho> x \<Longrightarrow> fmap_join \<rho> (fmap_join \<rho> x) = fmap_join \<rho> x"
  apply (transfer)
  apply rule
  apply (case_tac "\<rho> xa", case_tac "x xa")
  by (auto simp add: domIff Ball_def split add:option.split)

lemma lookup_fmap_join1[simp]:
  "compatible_fmap \<rho> \<rho>' \<Longrightarrow>  x \<in> fdom \<rho> \<Longrightarrow> x \<in> fdom \<rho>' \<Longrightarrow> the (lookup (fmap_join \<rho> \<rho>') x) = the (lookup \<rho> x) \<squnion> the (lookup \<rho>' x) "
  by (transfer, auto)

lemma lookup_fmap_join2[simp]:
  "compatible_fmap \<rho> \<rho>' \<Longrightarrow>  x \<in> fdom \<rho> \<Longrightarrow> x \<notin> fdom \<rho>' \<Longrightarrow> the (lookup (fmap_join \<rho> \<rho>') x) = the (lookup \<rho> x)"
  by (transfer, auto split:option.split)

lemma lookup_fmap_join3[simp]:
  "compatible_fmap \<rho> \<rho>' \<Longrightarrow>  x \<notin> fdom \<rho> \<Longrightarrow> x \<in> fdom \<rho>' \<Longrightarrow> the (lookup (fmap_join \<rho> \<rho>') x) = the (lookup \<rho>' x)"
  by (transfer, auto split:option.split)

lemma compatible_fmap_disjoint_fdom:
  "fdom m1 \<inter> fdom m2 = {} \<Longrightarrow> compatible_fmap m1 m2"
  by (auto intro: compatible_fmapI)

lemma fmap_join_below1:
  "compatible_fmap m1 m2 \<Longrightarrow> fdom m1 = fdom m2 \<Longrightarrow> m1 \<sqsubseteq> fmap_join m1 m2"
  apply (rule fmap_belowI', simp)
  apply transfer
  apply (auto simp add: intro!:join_above1 split:option.split)
  by (metis domI the.simps)

lemma fmap_join_below2:
  "compatible_fmap m1 m2 \<Longrightarrow> fdom m1 = fdom m2 \<Longrightarrow> m2 \<sqsubseteq> fmap_join m1 m2"
  apply (rule fmap_belowI', simp)
  apply transfer
  apply (auto simp add: intro!:join_above2 split:option.split)
  by (metis domI the.simps)

lemma fmap_join_least:
  "compatible_fmap m1 m2 \<Longrightarrow> fdom m1 = fdom m2 \<Longrightarrow> m1 \<sqsubseteq> m \<Longrightarrow> m2 \<sqsubseteq> m \<Longrightarrow> fmap_join m1 m2 \<sqsubseteq> m"
  apply (rule fmap_belowI', metis below_fmap_def fmap_join_below2)
  apply (drule_tac x = x in fmap_belowE)
  apply (drule_tac x = x in fmap_belowE)
  apply transfer
  apply (auto split:option.split intro!:join_below)
  by (metis domI the.simps)

lemma fmap_join_mono:
  assumes "compatible_fmap a b"
  assumes "compatible_fmap c d"
  assumes "a \<sqsubseteq> c"
  assumes "b \<sqsubseteq> d"
  shows "fmap_join a b \<sqsubseteq> fmap_join c d"
proof (rule fmap_belowI')
case goal1 thus ?case using assms by  (simp add: fmap_below_dom) 
next
case (goal2 x)
  from assms have [simp]: "fdom c = fdom a" "fdom d = fdom b" by (metis fmap_below_dom)+
  show ?case
  proof(cases "x \<in> fdom a")
  case True
    hence "x \<in> fdom c" by simp
    show ?thesis
    proof (cases "x \<in> fdom b")
    case True
      hence "x \<in> fdom d" by simp
      from `x \<in> fdom a` `x \<in> fdom b`
      have [simp]:"the (lookup (fmap_join a b) x) = the (lookup a x) \<squnion> the (lookup b x)"
        by (transfer, auto split add:option.split)
      from `x \<in> fdom c` `x \<in> fdom d`
      have [simp]:"the (lookup (fmap_join c d) x) = the (lookup c x) \<squnion> the (lookup d x)"
        by (transfer, auto split add:option.split)
      have "compatible (the (lookup a x)) (the (lookup b x))"
        by (metis Int_iff `x \<in> fdom a` `x \<in> fdom b` assms(1) compatible_fmap_def')
      moreover
      have "compatible (the (lookup c x)) (the (lookup d x))"
        by (metis Int_iff `x \<in> fdom c` `x \<in> fdom d` assms(2) compatible_fmap_def')
      ultimately
      show ?thesis
        apply (simp, rule join_mono)
        apply (rule fmap_belowE[OF assms(3)])
        apply (rule fmap_belowE[OF assms(4)])
        done
    next
    case False
      hence [simp]:"the (lookup (fmap_join a b) x) = the (lookup a x)"
        by (transfer, auto split add:option.split)
      from False have "x \<notin> fdom d" by simp
      hence [simp]:"the (lookup (fmap_join c d) x) = the (lookup c x)"
        by (transfer, auto split add:option.split)
      show ?thesis
        by (simp, rule fmap_belowE[OF assms(3)])
    qed
  next
  case False
    hence [simp]:"the (lookup (fmap_join a b) x) = the (lookup b x)"
      by (transfer, auto split add:option.split)
    from False have "x \<notin> fdom c" by simp
    hence [simp]:"the (lookup (fmap_join c d) x) = the (lookup d x)"
      by (transfer, auto split add:option.split)
    thus ?thesis
      by -(simp, rule fmap_belowE[OF assms(4)])
  qed
qed

lift_definition fmap_expand :: "('a, 'b::pcpo) fmap \<Rightarrow> 'a set  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda> m1 S. (if finite S then (\<lambda> x. if x \<in> S then Some (case m1 x of (Some x) => x | None => \<bottom>) else None) else empty)"
  apply (case_tac "finite set")
  apply (rule_tac B = "dom fun \<union> set" in   finite_subset)
  apply auto
  done

lift_definition fmap_extend :: "('a, 'b::pcpo) fmap \<Rightarrow> 'a set  \<Rightarrow> ('a, 'b) fmap"
  is "\<lambda> m1 S. (if finite S then (\<lambda> x. if x \<in> S then Some \<bottom> else m1 x) else empty)"
  apply (case_tac "finite set")
  apply (rule_tac B = "dom fun \<union> set" in   finite_subset)
  apply auto
  done

lemma fmap_expand_nonfinite:
  "\<not> finite S \<Longrightarrow> fmap_expand m S = fempty"
  by (transfer, simp)

lemma fmap_extend_nonfinite:
  "\<not> finite S \<Longrightarrow> fmap_extend m S = fempty"
  by (transfer, simp)

lemma fmap_restr_fmap_extend:
  "finite d2 \<Longrightarrow> fmap_restr d1 (fmap_extend m d2) = fmap_restr d1 (fmap_extend m (d1 \<inter> d2))"
  apply(cases "finite d1")
  apply transfer
  apply (auto simp add: restrict_map_def)
  unfolding fmap_restr_def
  by auto

lemma fmap_restr_fmap_expand:
  "finite d2 \<Longrightarrow> fmap_restr d1 (fmap_expand m d2) = fmap_restr d1 (fmap_expand m (d1 \<inter> d2))"
  apply(cases "finite d1")
  apply transfer
  apply (auto simp add: restrict_map_def)
  unfolding fmap_restr_def
  by auto

lemma fmap_restr_fmap_expand2:
  "finite d2 \<Longrightarrow> d1 \<subseteq> d2 \<Longrightarrow> fmap_restr d1 (fmap_expand m d2) = fmap_expand m d1"
  apply(cases "finite d1")
  apply transfer
  apply (auto simp add: restrict_map_def split:option.split)
  apply (metis set_mp)
  by (metis rev_finite_subset)


lemma fdom_fmap_extend[simp]:
  "finite S \<Longrightarrow> fdom (fmap_extend m S) = fdom m \<union> S"
  by (transfer, auto)

lemma fdom_fmap_expand[simp]:
  "finite S \<Longrightarrow> fdom (fmap_expand m S) = S"
  by (transfer, auto split:if_splits) 

lemma fmap_expand_noop[simp]:
  "S = fdom \<rho> \<Longrightarrow> fmap_expand \<rho> S = \<rho>"
  by (transfer, auto split: option.split)

lemma fmap_expand_idem:
  "finite S2 \<Longrightarrow> fdom \<rho> \<subseteq> S1 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> fmap_expand (fmap_expand \<rho> S1) S2 = fmap_expand \<rho> S2"
  apply (transfer)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  apply (rule ext)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  by (metis finite_subset)

lemma lookup_fmap_extend1[simp]:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> lookup (fmap_extend m S) x = Some \<bottom>"
  by (transfer, auto)

lemma lookup_fmap_expand1[simp]:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<in> fdom m \<Longrightarrow> lookup (fmap_expand m S) x = lookup m x"
  by (transfer, auto)

lemma lookup_fmap_extend2[simp]:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> lookup (fmap_extend m S) x = lookup m x"
  by (transfer, auto)

lemma lookup_fmap_expand2[simp]:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> fdom m \<Longrightarrow> lookup (fmap_expand m S) x = Some \<bottom>"
  by (transfer, auto split:option.split)

lemma lookup_fmap_expand3[simp]:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> lookup (fmap_expand m S) x = None"
  by (transfer, auto split:option.split)

lemma fmap_expand_fdom[simp]: "fmap_expand \<rho> (fdom \<rho>) = \<rho>"
  by (transfer, auto split:option.split)

lemma fmap_expand_belowI:
  assumes "fdom \<rho>' = S"
  assumes "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<in> S \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> the (lookup \<rho>' x)"
  shows "fmap_expand \<rho> S \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI')
  apply (metis assms(1) fdom_fmap_expand finite_fdom)
  apply (case_tac "x \<in> fdom \<rho>")
  apply (metis assms(1) assms(2) finite_fdom lookup_fmap_expand1)
  apply (metis assms(1) finite_fdom lookup_fmap_expand2 minimal the.simps)
  done

lemma fmap_expand_fmap_restr_below:
  assumes [simp]:"fdom x = S2"
  shows "fmap_expand (fmap_restr S1 x) S2 \<sqsubseteq> x"
  apply (rule fmap_expand_belowI[OF assms(1)])
  by (metis Int_iff below.r_refl empty_iff fdom_fmap_restr fempty_fdom fmap_restr_not_finite lookup_fmap_restr)

lemma fmap_extend_monofun:
  "monofun (\<lambda> m. fmap_extend m S)"
proof(cases "finite S")
case True
  show ?thesis
  proof (rule monofunI, rule fmap_belowI')
  case goal1 thus ?case using True by (simp add: fmap_below_dom)
  case (goal2 m1 m2 x) thus ?case
    using goal2 True
    by (cases  "x \<in> S", auto dest:fmap_belowE)
  qed
next
case False
  show ?thesis by (rule monofunI, simp add: fmap_extend_nonfinite[OF False])
qed

lemma fmap_expand_monofun:
  "monofun (\<lambda> m. fmap_expand m S)"
proof(cases "finite S")
case True
  show ?thesis
  proof (rule monofunI, rule fmap_belowI')
  case goal1 thus *: ?case using True by (simp add: fmap_below_dom)
  case (goal2 m1 m2 x) thus ?case
    using goal2 True
    apply (cases "x \<in> S")
    apply (cases "x \<in> fdom m1")
    apply (subgoal_tac "x \<in> fdom m2")
    apply (auto dest:fmap_belowE simp add: fmap_below_dom)
    done
  qed
next
case False
  show ?thesis by (rule monofunI, simp add: fmap_expand_nonfinite[OF False])
qed


lemma fmap_extend_cont:
  "cont (\<lambda> m. fmap_extend m S)"
proof(cases "finite S")
case True[simp]
  show ?thesis
  proof (rule fmap_contI)
  case goal1 thus ?case by (simp add: fmap_below_dom)
  case goal2 thus ?case by (metis True fmap_belowE lookup_fmap_extend1 lookup_fmap_extend2 minimal the.simps)
  next
  case (goal3 Y x)[simp]
    show ?case
      by (cases "x\<in>S", simp_all add: lookup_cont)
  qed
next
case False
  show ?thesis by (rule contI2[OF fmap_extend_monofun] , simp add: fmap_extend_nonfinite[OF False])
qed

lemma fmap_expand_cont:
  "cont (\<lambda> m. fmap_expand m S)"
proof(cases "finite S")
case True[simp]
  show ?thesis
  proof (rule fmap_contI)
  case goal1 thus ?case by (simp add: fmap_below_dom)
  case goal2 thus ?case by (metis True below_fmap_def fdom_fmap_expand lookup_fmap_expand1 lookup_fmap_expand2 minimal the.simps)
  next
  case (goal3 Y x)[simp]
    hence [simp]:"x \<in> S" by simp
    show ?case
      apply (cases "x \<in> fdom (\<Squnion> i. Y i)")
      apply (subgoal_tac "\<And> i. x \<in> fdom (Y i)")
      apply (simp add: lookup_cont)
      apply (metis chain_fdom(1) chain_fdom(2) goal3(1))
      apply (simp)
      done
  qed
next
case False
  show ?thesis by (rule contI2[OF fmap_expand_monofun] , simp add: fmap_expand_nonfinite[OF False])
qed

lemma compatible_fmap_expand: 
  assumes "compatible_fmap m1 m2"
  shows "compatible_fmap (fmap_expand m1 S)  (fmap_expand m2 S)"
proof(cases "finite S")
case True with assms show ?thesis
  apply transfer
  apply (auto  split:option.split)
  by (metis Int_iff domI the.simps)
next
  case False thus ?thesis by (transfer, auto)
qed

lemma fmap_upd_expand:
  "finite S \<Longrightarrow>
   x \<in> S \<Longrightarrow>
   fmap_expand (\<rho>(x f\<mapsto> y)) S = (fmap_expand \<rho> (S - {x}))(x f\<mapsto> y)"
   apply (rule fmap_eqI, auto)
   apply (case_tac "xa \<in> fdom (\<rho>(x f\<mapsto> y))", auto)
   apply (case_tac "xa = x", auto)
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

lemma fmap_bottom_below_iff[iff]:
  "finite S \<Longrightarrow> fmap_bottom S \<sqsubseteq> \<rho> \<longleftrightarrow> S = fdom \<rho>"
  by (metis fdom_fmap_bottom fmap_below_dom fmap_bottom_below)

lemma fmap_bottom_eqI[intro!]: "x = y \<Longrightarrow> fmap_bottom x = fmap_bottom y"
  by (transfer, auto)

lemma fmap_bottom_inj[iff]: "finite x \<Longrightarrow> finite y \<Longrightarrow> fmap_bottom x = fmap_bottom y \<longleftrightarrow> x = y"
  apply transfer
  apply (auto simp add: option.split option.split_asm)
  apply (metis option.simps(3))+
  done

lemma fmap_expand_fempty[simp]: "fmap_expand fempty S = fmap_bottom S"
  by (transfer, auto)

lemma fmap_expand_fmap_bottom[simp]: "fmap_expand (fmap_bottom S') S = fmap_bottom S"
  by (transfer, auto)

lemma fmap_restr_fmap_bottom[simp]:
  "finite S \<Longrightarrow> finite S2 \<Longrightarrow> fmap_restr S (fmap_bottom S2) = fmap_bottom (S \<inter> S2)"
  by (transfer, auto simp add: restrict_map_def)

lemma restr_extend_cut:
  "finite d \<Longrightarrow> d' \<subseteq> d \<Longrightarrow> fdom x = d' \<Longrightarrow> fmap_restr d' (fmap_extend x (d - d')) = x "
  by (rule fmap_eqI, auto)

(*
definition fix_extend :: "('a, 'b::pcpo) fmap \<Rightarrow> 'a set \<Rightarrow> (('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap) \<Rightarrow> ('a, 'b) fmap"
  where
  "fix_extend h S nh = fmap_add h (fix1 (fmap_bottom S)  (\<Lambda> h'. (nh (fmap_add h h') )))"
*)


lemma fmap_bottom_insert:
  "finite S \<Longrightarrow>
  fmap_bottom (insert x S) = (fmap_bottom S)(x f\<mapsto> \<bottom>)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "xa = x", auto)
  done

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

lemma fmap_less_fdom:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> fdom \<rho>1 \<subseteq> fdom \<rho>2"
  by (metis less_eq_fmap_def)

lemma fmap_less_restrict:
  "\<rho>1 \<le> \<rho>2 \<longleftrightarrow> (fdom \<rho>1 \<subseteq> fdom \<rho>2 \<and> \<rho>1 = fmap_restr (fdom \<rho>1) \<rho>2)"
  unfolding less_eq_fmap_def
  apply transfer
  apply (auto simp add:restrict_map_def split:option.split_asm)
  by (metis option.simps(3))

lemma fmap_restr_less:
  "fmap_restr S \<rho> \<le> \<rho>"
  unfolding less_eq_fmap_def
  by (transfer, auto)

lemma less_fmap_expand:
  "finite S \<Longrightarrow> fdom \<rho> \<subseteq> S \<Longrightarrow> \<rho> \<le> fmap_expand \<rho> S"
  unfolding less_eq_fmap_def
  by (transfer, auto)

lemma fdom_adm:
   "adm (\<lambda>\<rho>. P (fdom \<rho>))"
   by (metis admI chain_fdom(2))

lemma fdom_adm2:
  "cont u \<Longrightarrow> cont v \<Longrightarrow> adm (\<lambda>x. P (fdom (u x)) (fdom (v x)))"
  apply (rule admI)
  apply (frule (1) chain_fdom(2)[OF ch2ch_cont])
  apply (frule (1) chain_fdom(2)[OF ch2ch_cont]) back
  apply (erule (1) ssubst[OF cont2contlubE])
  apply (erule (1) ssubst[OF cont2contlubE])
  apply simp
  done

lemma fdom_adm_eq[simp]:
   "adm (\<lambda>\<rho>. fdom \<rho> = z)"
   by (rule fdom_adm)

lemma adm_less_fmap [simp]:
  "[|cont (\<lambda>x. u x); cont (\<lambda>x. v x)|] ==> adm (\<lambda>x. u x \<le> ((v x)::('a::type,'b::pcpo) fmap))"
  apply (subst fmap_less_restrict)
  apply (intro adm_lemmas fdom_adm2, assumption+)
  apply (rule contI)
  apply (subst chain_fdom(1)[OF ch2ch_cont[of u]], assumption+)
  apply (subst cont2contlubE[of u], assumption+)
  apply (subst chain_fdom(2)[OF ch2ch_cont[of u]], assumption+)
  apply (rule contE)
  apply auto
  done

lemma fmap_bottom_less[simp]:
  "finite S2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> fmap_bottom S1 \<le> fmap_bottom S2"
  apply (subgoal_tac "finite S1")
  apply (rule fmap_less_eqI)
  apply simp
  apply simp
  by (rule rev_finite_subset)


lemma adm_lookup: assumes "adm P" shows "adm (\<lambda> \<rho>. P (the (lookup \<rho> x)))"
  apply (rule admI)
  apply (subst lookup_cont)
  apply assumption
  apply (erule admD[OF assms lookup_chain])
  apply metis
  done

lemma fdom_fix_on:
  assumes "fix_on_cond S b F"
  shows  "fdom (fix_on' b F) = fdom b"
proof-
  have "fix_on' b F \<in> S"
    by (rule fix_on_there[OF assms])
  hence "b \<sqsubseteq> fix_on' b F"
    by (metis assms bottom_of_subpcpo_bot_minimal fix_on_cond.simps subpcpo_is_subpcpo_bot)
  thus ?thesis
    by (metis fmap_below_dom)
qed

locale iterative =
  fixes \<rho> :: "('a::type, 'b::pcpo) fmap"
   and e1 :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
   and e2 :: "('a, 'b) fmap \<Rightarrow> 'b"
   and S :: "'a set" and x :: 'a
   and D
  defines "D \<equiv> insert x (fdom \<rho> \<union> S)"
  assumes cont_e1 [simp]:"cont e1"
  assumes cont_e2 [simp]:"cont e2"
  assumes dom[simp]: "\<And> \<rho>. fdom (e1 \<rho>) = S"
  assumes ne:"x \<notin> S"

sublocale iterative < subpcpo "{x. fmap_bottom D \<sqsubseteq> x}" by (rule subpcpo_cone_above)

context iterative
begin

  lemma [simp]: "finite S" using dom[of undefined] by (auto simp del: dom)
  lemma [simp]: "finite D" by (simp add: D_def)
 

  abbreviation "cpo == {x. fmap_bottom D \<sqsubseteq> x}"
  abbreviation "b == fmap_bottom D"

  abbreviation "L == (\<lambda> \<rho>'. (\<rho> f++ e1 \<rho>')(x f\<mapsto> e2 \<rho>'))"
  abbreviation "H == (\<lambda> \<rho>' \<rho>''. \<rho>' f++ e1 \<rho>'')"
  abbreviation "R == (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' (fmap_bottom D) (H \<rho>')))(x f\<mapsto> e2 \<rho>'))"

  lemma condL: "fix_on_cond cpo b L"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (simp add: D_def)
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condL]

  lemma condH: "\<And> \<rho>'. \<rho>' \<in> cpo \<Longrightarrow> fix_on_cond cpo b (H \<rho>')"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (auto simp add: D_def)[1]
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condH]
  
  lemma condR: "fix_on_cond cpo b R"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      using fdom_fix_on[OF condH]  apply (auto simp add: D_def)[1]
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_upd_cont[OF cont_id cont_const]]
                fmap_upd_cont[OF cont_const cont_id]
                _
                cont_is_cont_on[OF cont_e2]])
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_add_cont1]
                fmap_add_cont2
                cont_is_cont_on[OF cont_const]
                ])
    apply (rule cont_comp_cont_on[OF fmap_restr_cont])
    apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (1) fix_on_mono[OF condH condH])
      apply (erule cont2monofunE[OF fmap_add_cont1])

    apply (rule eq_imp_below)
    apply (rule fix_on_cont[OF chain_on_is_chain condH[OF chain_on_is_on]])
      apply assumption
      apply assumption
    apply (rule cont2cont_lambda[OF fmap_add_cont1])
    done
  lemmas [simp] = fdom_fix_on[OF condR]


  lemma iterative_fmap_add:
    shows "fix_on' (fmap_bottom D) (\<lambda> \<rho>'. (\<rho> f++ e1 \<rho>')(x f\<mapsto> e2 \<rho>')) =
           fix_on' (fmap_bottom D) (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' (fmap_bottom D) (\<lambda> \<rho>''. \<rho>' f++ e1 \<rho>'')))(x f\<mapsto> e2 \<rho>'))"
  proof(rule below_antisym)
    have [simp]: "D \<inter> S = S" 
      by (auto simp add: D_def)
  
    { fix y \<rho>
      assume "y \<notin> S" and there: "(\<rho> :: ('a, 'b) fmap) \<in> cpo"
      hence "lookup (fix_on' b (H \<rho>)) y = lookup \<rho> y"
      apply (subst fix_on_eq[OF condH[OF there]])
      by simp
    } note H_ignores_not_S = this
  
    { fix \<rho> \<rho>'
      assume there: "(\<rho> :: ('a, 'b) fmap) \<in> cpo"
      assume "\<And> x. x \<in> S \<Longrightarrow> the (lookup (e1 \<rho>') x) \<sqsubseteq> the (lookup \<rho> x)"
      hence "H \<rho> \<rho>' \<sqsubseteq> \<rho>"
        apply -
        apply (rule fmap_belowI')
        using there apply (auto simp add: D_def)[1]
        apply (case_tac "x \<in> fdom (e1 \<rho>')")
        apply simp
        apply simp
        done
    } note H_noop = this
    
    note fix_eq_R = fix_on_eq[OF condR]
    note fix_eq_L = fix_on_eq[OF condL]
    note fix_eq_HR = fix_on_eq[OF condH[OF fix_on_there[OF condR]]]
  
    have HR_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) x = lookup (fix_on' b R) x"
      apply (subst fix_eq_HR) by simp
  
    have HR_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
      apply (subgoal_tac "y \<noteq> x")
      apply (subst fix_eq_HR)
      apply simp
      using ne by metis
  
    have L_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b L) y = lookup (e1 (fix_on' b L)) y"
      apply (subgoal_tac "y \<noteq> x")
      apply (subst (1) fix_eq_L)
      apply simp
      using ne by metis
  
    have L_x2[simp]: "the (lookup (fix_on' b L) x) = e2 (fix_on' b L)"
      by (subst (1) fix_eq_L, simp)
  
    have L_not_S_x2[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b L) y = lookup \<rho> y"
      by (subst (1) fix_eq_L, simp)
  
    have R_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b R) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
      apply (subgoal_tac "y \<noteq> x")
      apply (subst fix_eq_R)
      apply simp
      using ne by metis
  
    have R_x2[simp]: "the (lookup (fix_on' b R) x) = e2 (fix_on' b R)"
      by (subst fix_eq_R, simp)
  
    have R_not_S[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b R) y = lookup \<rho> y"
      by (subst fix_eq_R, simp)
  
    have HR_is_R[simp]: "fix_on' b (H (fix_on' b R)) = fix_on' b R"
      apply (rule fmap_eqI)
      apply simp
      apply (case_tac "xa \<in> S")
      apply simp_all
      done
  
    have HLL_below_L: "H (fix_on' b L) (fix_on' b L) \<sqsubseteq> (fix_on' b L)"
      by (rule H_noop, simp_all)
  
    show "fix_on' b R \<sqsubseteq> fix_on' b L"
    proof (rule fix_on_least_below[OF condR])
      show "fix_on' b L \<in> cpo"
        by simp
      show "R (fix_on' b L) \<sqsubseteq> fix_on' b L"
      proof(rule fmap_upd_belowI)
        case goal1 show ?case by (simp, auto simp add: D_def)
        show "e2 (fix_on' b L) \<sqsubseteq> the (lookup (fix_on' b L) x)"
          by simp
        case (goal2 y)
          hence [simp]:"y \<noteq> x" by metis
        show "the (lookup (\<rho> f++ fmap_restr S (fix_on' b (H (fix_on' b L)))) y) \<sqsubseteq> the (lookup (fix_on' b L) y)"
        proof(cases "y \<in> S")
        case True[simp]
          from HLL_below_L
          have "(fix_on' b (H (fix_on' b L))) \<sqsubseteq> (fix_on' b L)"
            by (rule fix_on_least_below[OF condH[OF fix_on_there[OF condL]] fix_on_there[OF condL]])
          hence "the (lookup (fix_on' b (H (fix_on' b L))) y) \<sqsubseteq> the (lookup (fix_on' b L) y)"
            by (rule fmap_belowE)
          thus ?thesis
            by (subst lookup_fmap_add1, simp_all)
        next
        case False
          thus ?thesis by simp
        qed
      qed
    qed
  
    show "fix_on' b L \<sqsubseteq> fix_on' b R"
    proof (rule fix_on_least_below[OF condL])
      show "fix_on' b R \<in> cpo"
        by simp
      show "L (fix_on' b R) \<sqsubseteq> fix_on' b R"
        apply (rule  fmap_upd_belowI)
        apply simp apply (auto simp add: D_def)[1]
        apply (case_tac "z \<notin> S")
        apply simp_all
      done
    qed
  qed
end

instance fmap :: (type, Nonempty_Meet_cpo) Bounded_Nonempty_Meet_cpo
apply default
proof-
  fix S :: "('a, 'b) fmap set"
  assume "S \<noteq> {}" and "\<exists>z. S >| z"
  then obtain b where "\<And> m. m\<in>S \<Longrightarrow> b \<sqsubseteq> m" by (metis is_lbD)
  hence [simp]:"\<And> m. m \<in> S \<Longrightarrow> fdom m = fdom b" by (metis fmap_below_dom)
  
  obtain f where f: "\<And> x. x \<in> fdom b \<Longrightarrow> (\<lambda>m . the (lookup m x)) ` S >>| f x "
  proof-
    {
    fix x
    assume "x \<in> fdom b"
    have "(\<lambda>m . the (lookup m x)) ` S \<noteq> {}" using `S \<noteq> {}` by auto
    then obtain l where  "(\<lambda>m . the (lookup m x)) ` S >>| l" by (metis nonempty_meet_exists)
    hence "(\<lambda>m . the (lookup m x)) ` S >>| (SOME l. (\<lambda>m . the (lookup m x)) ` S >>| l)"
      by (rule someI)
    }
    thus ?thesis by (rule that)
  qed 

  let ?zm = "\<lambda> x. if x \<in> fdom b then Some (f x) else None"
  have "dom ?zm = fdom b" by (auto simp add: dom_def)

  obtain z where [simp]: "fdom z = fdom b" and z: "\<And> x m . x \<in> fdom b \<Longrightarrow> (\<lambda>m . the (lookup m x)) ` S >>| the (lookup z x)"
  proof-
    show ?thesis  
      apply (rule that[of "Abs_fmap ?zm"])
      apply (subst fdom.rep_eq)
      apply (subst  Abs_fmap_inverse)
      prefer 3
      apply (subst (2) lookup.rep_eq)
      apply (subst  Abs_fmap_inverse)
      apply (auto simp add: dom_def)
      apply (erule f)
      done
  qed

  have "S >>| z"
    apply (rule is_glbI)
    apply (rule is_lbI)
    apply (rule fmap_belowI')
    apply simp
    apply (rule is_lbD)
    apply (rule is_glbD1)
    apply (rule z, simp)
    apply auto
    apply (rule fmap_belowI')
    apply (metis `S \<noteq> {}` `\<And>m. m \<in> S \<Longrightarrow> fdom m = fdom b` `fdom z = fdom b` all_not_in_conv fmap_below_dom is_lbD)
    apply (rule is_glbD2)
    apply (rule z, simp)
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule fmap_belowE)
    apply (erule (1) is_lbD)
    done
  thus "\<exists> z. S >>| z" by auto
qed

instantiation fmap :: (type, pcpo) subpcpo_partition
begin
  definition "to_bot x = fmap_bottom (fdom x)"
  lemma [simp]:"fdom (to_bot x) = fdom x"
    unfolding to_bot_fmap_def by auto

  lemma to_bot_vimage_cone:"to_bot -` {to_bot x} = {z. fmap_bottom (fdom x) \<sqsubseteq> z}"
    by (auto simp add:to_bot_fmap_def)

  instance  
  apply default
  apply (subst to_bot_vimage_cone)
  apply (rule subpcpo_cone_above)
  apply (simp add: to_bot_fmap_def fmap_below_dom)
  apply (simp add: to_bot_fmap_def)
  done
end


end
