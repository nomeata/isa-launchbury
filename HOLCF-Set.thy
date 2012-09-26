theory "HOLCF-Set"
 imports HOLCF
begin

default_sort cpo

locale subpcpo =
  fixes S :: "'a set"
  assumes pcpo: "(\<forall>Y. (chain Y \<longrightarrow> (\<forall> i. Y i \<in> S) \<longrightarrow> (\<Squnion> i. Y i) \<in> S))
          \<and>  (\<exists> z \<in> S. \<forall> y \<in> S. z \<sqsubseteq> y)"

lemma subpcpoI:
  assumes "\<And> Y. \<lbrakk> chain Y; \<And> i. Y i \<in> S \<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  assumes "b \<in> S"
  assumes "\<And> y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y"
  shows "subpcpo S"
unfolding subpcpo_def by (metis assms)

locale subpcpo_syn = 
  fixes S :: "'a set" 
begin

definition chain_on :: "(nat => 'a) => bool" where
  "chain_on Y = ((\<forall>i. Y i \<sqsubseteq> Y (Suc i) \<and> (\<forall>i. Y i \<in> S)))"

definition
  adm_on :: "('a::cpo => bool) \<Rightarrow> bool" where
  "adm_on P = (\<forall>Y. chain_on Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i))"

definition bottom_of :: "'a"
  where "bottom_of = (THE x. x\<in>S \<and> (\<forall>y \<in> S. x \<sqsubseteq> y))"

definition
  monofun_on :: "('a => 'b) => bool" where
  "monofun_on f = (\<forall>x\<in>S. \<forall>y\<in>S. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

definition
  cont_on :: "('a::cpo => 'b::cpo) => bool"
where
  "cont_on f = (\<forall>Y. chain_on Y --> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i))"

definition
  "fix_on'" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "fix_on' b F = 
    (if chain (\<lambda>i. (F^^i) bottom_of) \<and> subpcpo S \<and> b = bottom_of
    then (\<Squnion>i. (F^^i) bottom_of)
    else b)"

abbreviation fix_on where
  "fix_on \<equiv> fix_on' (bottom_of)"

lemmas fix_on_def = fix_on'_def

definition 
  closed_on :: "('a::cpo => 'a::cpo) => bool"
where
  "closed_on f = (\<forall> x\<in> S. f x \<in> S)"

end

sublocale subpcpo < subpcpo_syn.

context subpcpo
begin

lemma monofun_onE: 
  "[|monofun_on f; x\<in> S; y \<in> S; x \<sqsubseteq> y|] ==> f x \<sqsubseteq> f y"
by (simp add: monofun_on_def)

lemma monofun_onI: 
  "[|\<And>x y. \<lbrakk> x \<in> S; y \<in> S; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y|] ==> monofun_on f"
by (simp add: monofun_on_def)

lemma cont_onE:
  "[|cont_on f; chain_on Y|] ==> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
by (simp add: cont_on_def)

lemma bin_chain_on: "\<lbrakk> x\<in>S; y\<in>S; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> chain_on (\<lambda>i. if i=0 then x else y)"
  by (simp add: chain_on_def)

lemma binchain_cont_on:
  "\<lbrakk>cont_on f; x \<in> S; y \<in> S ; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
apply (erule subst)
apply (erule cont_onE)
apply (erule (2) bin_chain_on)
apply (rule_tac f=f in arg_cong)
apply (erule is_lub_bin_chain [THEN lub_eqI])
done

lemma cont_on2mono_on:
  "cont_on F \<Longrightarrow> monofun_on F"
apply (rule monofun_onI)
apply (drule (3) binchain_cont_on)
apply (drule_tac i=0 in is_lub_rangeD1)
apply simp
done


lemma adm_onD:
  assumes "adm_on P"
  and "chain_on Y"
  and"\<And>i. P (Y i)"
  shows "P (\<Squnion>i. Y i)"
using assms unfolding adm_on_def by auto

lemma closed_onE: 
  "[|closed_on f; x \<in> S|] ==> f x \<in> S"
by (simp add: closed_on_def)

lemma shows bottom_of_there[simp]: "bottom_of \<in> S"
      and bottom_of_minimal: "\<And> x. x \<in> S \<Longrightarrow> bottom_of \<sqsubseteq> x"
proof-
  from pcpo obtain y where y: "y \<in> S \<and> (\<forall> x \<in> S. y \<sqsubseteq> x)" unfolding subpcpo_def by auto
  hence "bottom_of \<in> S \<and> (\<forall>y \<in> S. bottom_of \<sqsubseteq> y)"
    unfolding bottom_of_def
    by (rule theI[where a = y], metis y po_eq_conv)
  thus "bottom_of \<in> S" and "\<And> x. x \<in> S \<Longrightarrow> bottom_of \<sqsubseteq> x" by metis+
qed

lemma iterate_closed_on: "closed_on F \<Longrightarrow> closed_on (F^^i)"
  unfolding closed_on_def
  by (induct i, auto)

lemma closed_is_chain [simp]: "closed_on F \<Longrightarrow> monofun_on F \<Longrightarrow> chain (\<lambda>i. (F^^i) bottom_of)"
  apply (rule chainI)
  apply (induct_tac i)
  apply (simp, erule bottom_of_minimal[OF closed_onE[OF _ bottom_of_there]])[1]
  apply simp
  apply (erule monofun_onE)
  apply (erule closed_onE[OF iterate_closed_on bottom_of_there])
  apply (rule closed_onE[OF _ closed_onE[OF iterate_closed_on bottom_of_there]], assumption, assumption)
  apply assumption
  done

lemma closed_is_chain_on: "closed_on F \<Longrightarrow> monofun_on F \<Longrightarrow> chain_on (\<lambda>i. (F^^i) bottom_of)"
  unfolding chain_on_def
  apply rule
  apply rule
  apply (drule closed_is_chain, assumption)
  apply (simp add: chain_def)
  apply (rule)
  apply (erule closed_onE[OF iterate_closed_on bottom_of_there])
  done

lemma iterate_below_fix_on: "closed_on F \<Longrightarrow> monofun_on F \<Longrightarrow> (F^^i) bottom_of \<sqsubseteq> fix_on F"
  unfolding fix_on_def
  by (auto intro: is_ub_thelub closed_is_chain  subpcpo_axioms)

end

interpretation subpcpo_syn S for S.

lemma chain_on_product:
  assumes "chain_on S1 Y" and "chain_on S2 Z"
  shows "chain_on (S1 \<times> S2) (\<lambda> i. (Y i, Z i))"
  using assms by (auto simp add: chain_on_def)

lemma subpcpo_product:
  assumes "subpcpo S1" and "subpcpo S2"
  shows "subpcpo (S1 \<times> S2)"
proof(rule subpcpoI)
  interpret subpcpo S1 by fact
  interpret s2!: subpcpo S2  by fact
{
  fix Y :: "nat \<Rightarrow> ('a \<times>'b)"
  assume "chain Y"
  hence "chain (\<lambda> i. (fst (Y i)))" and  "chain (\<lambda> i. (snd (Y i)))"
    by (auto simp add: chain_def fst_monofun snd_monofun)
  moreover
  assume "\<And> i. Y i \<in> S1 \<times> S2"
  hence "\<And> i. fst (Y i) \<in> S1" and  "\<And> i. snd (Y i) \<in> S2"
    by (metis mem_Sigma_iff surjective_pairing)+
  ultimately
  have "(\<Squnion> i. fst (Y i)) \<in> S1" and "(\<Squnion> i. snd (Y i)) \<in> S2" using pcpo s2.pcpo by auto
  thus "(\<Squnion> i. Y i) \<in> S1 \<times> S2" by (auto simp add: lub_prod[OF `chain Y`])
  next
  show "(bottom_of S1, bottom_of S2) \<in> S1 \<times> S2" by simp
  next
  fix y
  assume "y \<in> S1 \<times> S2"
  thus "(bottom_of S1, bottom_of S2) \<sqsubseteq> y"
    by (metis (full_types) Pair_below_iff bottom_of_minimal mem_Sigma_iff prod.exhaust s2.bottom_of_minimal)
}
qed

lemma parallel_fix_on_ind:
  assumes pcpo1: "subpcpo S1"
  assumes pcpo2: "subpcpo S2"
  assumes adm: "adm_on (S1 \<times> S2) (\<lambda>x. P (fst x) (snd x))"
  assumes closedF: "closed_on S1 F"
  assumes chainF: "cont_on S1 F"
  assumes closedG: "closed_on S2 G"
  assumes chainG: "cont_on S2 G"
  assumes base: "P (bottom_of S1) (bottom_of S2)"
  assumes step: "!!y z. \<lbrakk> y \<in> S1 ; z \<in> S2; P y z \<rbrakk> \<Longrightarrow> P (F y) (G z)"
  shows "P (fix_on S1 F) (fix_on S2 G)"
proof -
  interpret subpcpo S1 by fact
  interpret s2!: subpcpo S2  by fact
  interpret sp!: subpcpo "(S1 \<times> S2)"  by (rule subpcpo_product, fact+)

  note chain1 = closed_is_chain[OF closedF cont_on2mono_on[OF chainF]] 
  note chain2 = s2.closed_is_chain[OF closedG s2.cont_on2mono_on[OF chainG]] 

  from adm have adm': "adm_on (S1 \<times> S2) (split P)"
    unfolding split_def .
  { fix i
    have "P ((F^^i) (bottom_of S1)) ((G^^i) (bottom_of S2))"
    proof(induct i)
    case 0 thus ?case by (simp add: base)
    next
    case (Suc i)
      have "((F ^^ i) (bottom_of S1)) \<in> S1" by (rule closed_onE[OF iterate_closed_on[OF closedF] bottom_of_there])
      moreover
      have "((G ^^ i) (bottom_of S2)) \<in> S2" by (rule s2.closed_onE[OF s2.iterate_closed_on[OF closedG] s2.bottom_of_there])
      ultimately
      show ?case using Suc by (simp add: step)
    qed
  }
  hence "!!i. split P ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2))"
    by simp
  hence "split P (\<Squnion>i. ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2)))"
    apply -
    apply (rule sp.adm_onD [OF adm'
               chain_on_product[OF closed_is_chain_on[OF closedF cont_on2mono_on[OF chainF]]
                                   s2.closed_is_chain_on[OF closedG s2.cont_on2mono_on[OF chainG]]]])
    apply (auto intro: ch2ch_Pair simp add: chain1 chain2)
    done
  hence "split P (\<Squnion>i. ((F^^i) (bottom_of S1)), \<Squnion>i. (G^^i) (bottom_of S2))"
    by (simp add: lub_Pair chain1 chain2)
  hence "P (\<Squnion>i. (F^^i) (bottom_of S1)) (\<Squnion>i. (G^^i) (bottom_of S2))"
    by simp
  thus "P (fix_on S1 F) (fix_on S2 G)"
    using chain1 chain2 subpcpo_axioms s2.subpcpo_axioms
    by (simp add: fix_on_def)
qed


end
