theory "HOLCF-Set"
 imports HOLCF
begin

default_sort cpo

locale subcpo =
  fixes S :: "'a set"
  assumes cpo': "(\<forall>Y. (chain Y \<longrightarrow> (\<forall> i. Y i \<in> S) \<longrightarrow> (\<Squnion> i. Y i) \<in> S))"

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

interpretation subpcpo_syn S for S.

lemma chain_onI:
  assumes  "\<And> i. Y i \<sqsubseteq> Y (Suc i)" and "\<And>i. Y i \<in> S"
  shows "chain_on S Y"
unfolding chain_on_def using assms by auto

lemma chain_on_is_on: "chain_on S Y \<Longrightarrow> Y i \<in> S"
  unfolding chain_on_def by auto

lemma chain_onE: "chain_on S Y \<Longrightarrow> Y i \<sqsubseteq> Y (Suc i)"
  unfolding chain_on_def by auto

lemma chain_on_is_chain: "chain_on S Y \<Longrightarrow> chain Y"
  unfolding chain_on_def chain_def by auto

lemma closed_onE: 
  "[|closed_on S f; x \<in> S|] ==> f x \<in> S"
by (simp add: closed_on_def)

lemma monofun_onE: 
  "[|monofun_on S f; x\<in> S; y \<in> S; x \<sqsubseteq> y|] ==> f x \<sqsubseteq> f y"
by (simp add: monofun_on_def)

lemma monofun_onI: 
  "[|\<And>x y. \<lbrakk> x \<in> S; y \<in> S; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y|] ==> monofun_on S f"
by (simp add: monofun_on_def)

lemma ub2ub_monofun_on: 
  "[|monofun_on S f; \<And> i. Y i \<in> S; u \<in> S; range Y <| u|] ==> range (\<lambda>i. f (Y i)) <| f u"
apply (rule ub_rangeI)
apply (erule  monofun_onE)
apply assumption+
apply (erule ub_rangeD)
done


lemma monofun_comp_monofun_on:
  "monofun f \<Longrightarrow> monofun_on S g \<Longrightarrow> monofun_on S (\<lambda> x. f (g x))"
  unfolding monofun_on_def
  by (auto elim:monofunE)

lemma monofun_comp_monofun_on2:
  assumes "monofun f"
  and "\<And> x. monofun (f x)"
  shows "monofun_on S g \<Longrightarrow> monofun_on S h \<Longrightarrow> monofun_on S (\<lambda> x. f (g x) (h x))"
  unfolding monofun_on_def
  by (auto intro: rev_below_trans[OF fun_belowD[OF monofunE[OF assms(1)]] monofunE[OF assms(2)]]) 

lemma cont_onI:
  "[|!!Y. chain_on S Y ==> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)|] ==> cont_on S f"
by (simp add: cont_on_def)

lemma ch2ch_monofun_on: "[|monofun_on S f; chain_on S Y|] ==> chain (\<lambda>i. f (Y i))"
  apply (rule chainI)
  apply (erule monofun_onE)
  apply (erule chain_on_is_on)+
  apply (erule chain_onE)
  done


lemma cont_onE:
  "[|cont_on S f; chain_on S Y|] ==> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
by (simp add: cont_on_def)

lemma bin_chain_on: "\<lbrakk> x\<in>S; y\<in>S; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> chain_on S (\<lambda>i. if i=0 then x else y)"
  by (simp add: chain_on_def)

lemma binchain_cont_on:
  "\<lbrakk>cont_on S f; x \<in> S; y \<in> S ; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
apply (erule subst)
apply (erule cont_onE)
apply (erule (2) bin_chain_on)
apply (rule_tac f=f in arg_cong)
apply (erule is_lub_bin_chain [THEN lub_eqI])
done

lemma cont_on2mono_on:
  "cont_on S F \<Longrightarrow> monofun_on S F"
apply (rule monofun_onI)
apply (drule (3) binchain_cont_on)
apply (drule_tac i=0 in is_lub_rangeD1)
apply simp
done

lemma cont_on2contlubE:
  "[|cont_on S f; chain_on S Y|] ==> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))"
apply (rule lub_eqI [symmetric])
apply (erule (1) cont_onE)
done

lemma cont_is_cont_on:
  "cont P \<Longrightarrow> cont_on S P"
  unfolding cont_on_def cont_def by (metis (full_types) chain_on_def po_class.chainI)

lemma adm_onD:
  assumes "adm_on S P"
  and "chain_on S Y"
  and"\<And>i. P (Y i)"
  shows "P (\<Squnion>i. Y i)"
using assms unfolding adm_on_def by auto

lemma adm_is_adm_on:
  "adm P \<Longrightarrow> adm_on S P"
  unfolding adm_def adm_on_def by (metis (full_types) chain_on_def po_class.chainI)

sublocale subpcpo < subpcpo_syn.

lemma subpcpo_is_subcpo: "subpcpo S \<Longrightarrow> subcpo S" unfolding subpcpo_def subcpo_def by simp

sublocale subpcpo < subcpo by (rule subpcpo_is_subcpo[OF subpcpo_axioms])

context subpcpo
begin

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

lemma chain_on_lub_on:
  "chain_on Y \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  unfolding chain_on_def by (metis chain_def pcpo)

lemma cont_onI2:
  fixes f :: "'a::cpo => 'b::cpo"
  assumes mono: "monofun_on f"
  assumes below: "!!Y. [|chain_on Y; chain (\<lambda>i. f (Y i))|]
     ==> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  shows "cont_on f"
proof (rule cont_onI)
  fix Y :: "nat => 'a"
  assume Y: "chain_on Y"
  with mono have fY: "chain (\<lambda>i. f (Y i))"
    by (rule ch2ch_monofun_on)
  have "(\<Squnion>i. f (Y i)) = f (\<Squnion>i. Y i)"
    apply (rule below_antisym)
    apply (rule lub_below [OF fY])
    apply (rule monofun_onE [OF mono])
    apply (rule chain_on_is_on[OF Y])
    apply (rule chain_on_lub_on[OF Y])
    apply (rule is_ub_thelub [OF chain_on_is_chain[OF Y]])
    apply (rule below [OF Y fY])
    done
  with fY show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
    by (rule thelubE)
qed

lemma cont_comp_cont_on:
  "cont f \<Longrightarrow> cont_on g \<Longrightarrow> cont_on (\<lambda> x. f (g x))"
  apply (rule cont_onI2)
  apply (erule (1) monofun_comp_monofun_on[OF cont2mono cont_on2mono_on])
  by (metis ch2ch_monofun_on cont2contlubE cont_on2contlubE cont_on2mono_on eq_imp_below)

lemma cont_comp_cont_on2:
  "cont f \<Longrightarrow> (\<And>x. cont (f x)) \<Longrightarrow> cont_on g \<Longrightarrow> cont_on h \<Longrightarrow> cont_on (\<lambda> x. f (g x) (h x))"
proof (rule cont_onI2)
case goal1 thus ?case by (rule  monofun_comp_monofun_on2[OF cont2mono cont2mono cont_on2mono_on cont_on2mono_on])
next
case goal2
  have c1: "chain (\<lambda>i. h (Y i))" by (rule ch2ch_monofun_on[OF cont_on2mono_on[OF goal2(4)] goal2(5)])
  have c2: "chain (\<lambda>i. g (Y i))" by (rule ch2ch_monofun_on[OF cont_on2mono_on[OF goal2(3)] goal2(5)])
  have c3: "chain (\<lambda>i. f (g (Y i)))" by (rule ch2ch_cont[OF goal2(1) c2])
  have c4: "\<And>x. chain (\<lambda>i. f x (h (Y i)))" by (rule ch2ch_cont[OF goal2(2) c1])
  have c5: "\<And>x. chain (\<lambda>i. f (g (Y i)) x)" by (rule ch2ch_fun[OF c3])

  show ?case
  apply (subst cont_on2contlubE[OF goal2(3) goal2(5)])
  apply (subst cont_on2contlubE[OF goal2(4) goal2(5)])
  apply (subst cont2contlubE[OF goal2(2) c1])
  apply (subst cont2contlubE[OF goal2(1) c2])
  apply (subst lub_fun[OF c3])
  apply (subst diag_lub[OF c4 c5])
  apply rule
  done
qed

end

interpretation subpcpo_syn S for S.

locale subpcpo_bot = subpcpo S for S +
  fixes b
  assumes "bottom_of S = b"

lemmas subpcpo_bot_def' = subpcpo_bot_def[unfolded subpcpo_bot_axioms_def]

lemma subpcpo_bot_is_subpcpo:
  "subpcpo_bot S b \<Longrightarrow> subpcpo S"
  unfolding subpcpo_bot_def by auto

lemma bottom_of_subpcpo_bot:
  "subpcpo_bot S b \<Longrightarrow> bottom_of S = b"
  unfolding subpcpo_bot_def' by auto

lemma bottom_of_subpcpo_bot_there:
  "subpcpo_bot S b \<Longrightarrow> b \<in> S"
  unfolding subpcpo_bot_def' by (metis subpcpo.bottom_of_there)

lemma bottom_of_subpcpo_bot_minimal:
  "subpcpo_bot S b \<Longrightarrow> x \<in> S \<Longrightarrow> b \<sqsubseteq> x"
  unfolding subpcpo_bot_def' by (metis subpcpo.bottom_of_minimal)

lemma subpcpo_is_subpcpo_bot:
  "subpcpo S \<Longrightarrow> subpcpo_bot S (bottom_of S)"
  unfolding subpcpo_bot_def' by auto

lemma subpcpo_botI:
  assumes "\<And> Y. \<lbrakk> chain Y; \<And> i. Y i \<in> S \<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  assumes "b \<in> S"
  assumes "\<And> y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y"
  shows "subpcpo_bot S b"
unfolding subpcpo_bot_def' 
proof
  show "subpcpo S" by (rule subpcpoI[OF assms])
  interpret subpcpo S by fact
  show "bottom_of S = b"
    by (metis assms(2) assms(3) below_antisym bottom_of_minimal bottom_of_there)
qed


lemma ch2chain_on_monofun_on:
  shows "[|monofun_on S1 f; chain_on S1 Y; f ` S1 \<subseteq> S2 |] ==> chain_on S2 (\<lambda>i. f (Y i))"
proof-
  show "[|monofun_on S1 f; chain_on S1 Y; f ` S1 \<subseteq> S2 |] ==> chain_on S2 (\<lambda>i. f (Y i))"
    apply (rule chain_onI)
    apply (erule monofun_onE)
    apply (erule chain_on_is_on)+
    apply (erule chain_onE)
    apply (erule subsetD)
    apply (rule imageI)
    apply (erule chain_on_is_on)
    done
qed

lemma ch2ch_cont_on:
  assumes "cont_on S1 f" and "chain_on S1 Y" and "f ` S1 \<subseteq> S2"
  shows "chain_on S2 (\<lambda>i. f (Y i))"
  by (rule ch2chain_on_monofun_on[OF cont_on2mono_on[OF assms(1)] assms(2) assms(3)])

lemma adm_on_subst:
  assumes cont: "cont_on S1 t"  and closed: "t ` S1 \<subseteq> S2" and  adm: "adm_on S2 P" 
  shows "adm_on S1 (\<lambda>x. P (t x))"
proof-
  from cont closed adm
  show ?thesis
  by (auto simp add: adm_on_def cont_on2contlubE ch2ch_cont_on)
qed

lemma chain_on_product:
  assumes "chain_on S1 Y" and "chain_on S2 Z"
  shows "chain_on (S1 \<times> S2) (\<lambda> i. (Y i, Z i))"
  using assms by (auto simp add: chain_on_def)

lemma subpcpo_UNIV:
  shows "subpcpo (UNIV::'a::pcpo set)"
  by(rule subpcpoI, auto)

lemma subpcpo_cone_above:
  shows "subpcpo {y . x \<sqsubseteq> y}"
  by (rule subpcpoI,  auto intro:admD)

lemma bottom_of_cone_above[simp]:
  shows "bottom_of {y . x \<sqsubseteq> y} = x"
proof-
  interpret subpcpo "{y . x \<sqsubseteq> y}" by (rule subpcpo_cone_above)
  show ?thesis by (metis bottom_of_minimal bottom_of_there mem_Collect_eq po_eq_conv)
qed

lemma subpcpo_bot_cone_above:
  shows "subpcpo_bot {y . x \<sqsubseteq> y} x"
  by (metis bottom_of_cone_above subpcpo_is_subpcpo_bot[OF subpcpo_cone_above])

lemma subpcpo_bot_image:
  assumes "subpcpo_bot S b"
  and "cont f"
  and "cont g"
  and im: "g ` f ` S \<subseteq> S"
  and cut: "\<And> x. x \<in> f ` S \<Longrightarrow> f (g x) = x"
  shows "subpcpo_bot (f`S) (f b)"
proof(rule subpcpo_botI)
  interpret subpcpo S by (rule subpcpo_bot_is_subpcpo, fact)
{
  fix Y :: "nat \<Rightarrow> 'b"
  assume *: "\<And> i. Y i \<in> f ` S"
  have "\<And> i. g (Y i) \<in> S"
    by (metis (full_types) "*" im image_eqI set_mp)
  moreover
  assume "chain Y"
  hence "chain (\<lambda> i. g (Y i))"
    by (metis ch2ch_cont[OF `cont g`])
  ultimately
  have "(\<Squnion> i. g (Y i)) \<in> S" by (metis pcpo)
  hence "f (\<Squnion> i. g (Y i)) \<in> f` S" by (rule imageI)
  hence "(\<Squnion> i. f (g (Y i))) \<in> f` S" by (metis cont2contlubE[OF `cont f` `chain (\<lambda>i. g (Y i))` ])
  thus "(\<Squnion> i. Y i) \<in> f` S" by (metis "*" cut lub_eq)
  next
  show "f b \<in> f ` S" by (rule imageI, rule bottom_of_subpcpo_bot_there, fact)
  next
  fix y
  assume "y \<in> f`S"
  hence "g y \<in> S" by (metis im imageI in_mono)
  hence "b \<sqsubseteq> g y" by (metis bottom_of_subpcpo_bot[OF assms(1)] bottom_of_minimal)
  hence "f b \<sqsubseteq> f (g y)" by (metis cont2monofunE[OF `cont f`])
  thus  "f b \<sqsubseteq> y" by (metis `y \<in> f\` S` cut)
}
qed

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

lemma subpcpo_bot_inter:
  assumes "subpcpo_bot S1 b1" and "subcpo S2"
  and bot_in_2: "b1 \<in> S2"
  shows "subpcpo_bot (S1 \<inter> S2) b1"
proof(rule subpcpo_botI)
  interpret subpcpo S1 by (rule subpcpo_bot_is_subpcpo, fact)
  interpret s2!: subcpo S2  by (fact)
{
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  moreover
  assume "\<And> i. Y i \<in> S1 \<inter> S2"
  hence "\<And> i. Y i \<in> S1" and  "\<And> i. Y i \<in> S2" by auto
  ultimately
  have "(\<Squnion> i. Y i) \<in> S1" and "(\<Squnion> i. Y i) \<in> S2" using pcpo s2.cpo' by auto
  thus "(\<Squnion> i. Y i) \<in> S1 \<inter> S2" by auto
  next
  show "b1 \<in> S1 \<inter> S2" by (auto simp add: bot_in_2 bottom_of_subpcpo_bot_there[OF assms(1)])
  next
  fix y
  assume "y \<in> S1 \<inter> S2"
  thus "b1 \<sqsubseteq> y"
    by (auto intro: bottom_of_subpcpo_bot_minimal[OF assms(1)])
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
  note chain2 = s2.closed_is_chain[OF closedG cont_on2mono_on[OF chainG]] 

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
      have "((G ^^ i) (bottom_of S2)) \<in> S2" by (rule closed_onE[OF s2.iterate_closed_on[OF closedG] s2.bottom_of_there])
      ultimately
      show ?case using Suc by (simp add: step)
    qed
  }
  hence "!!i. split P ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2))"
    by simp
  hence "split P (\<Squnion>i. ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2)))"
    apply -
    apply (rule adm_onD [OF adm'
               chain_on_product[OF closed_is_chain_on[OF closedF cont_on2mono_on[OF chainF]]
                                   s2.closed_is_chain_on[OF closedG cont_on2mono_on[OF chainG]]]])
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
