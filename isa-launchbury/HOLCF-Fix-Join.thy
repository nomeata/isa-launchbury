theory "HOLCF-Fix-Join"
  imports "HOLCF-Set" "HOLCF-Join" "HOLCF-Down-Closed"
begin

definition fix_join_compat' :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition} \<Rightarrow> 'a set"
  where "fix_join_compat' \<rho> = {x. compatible \<rho> x}"

lemma fjc'_iff[iff]:
  "x \<in> fix_join_compat' \<rho> \<longleftrightarrow> compatible \<rho> x"
  unfolding fix_join_compat'_def by auto

lemma subcpo_jfc': "subcpo (fix_join_compat' \<rho>)"
  apply (rule subcpoI)
  apply simp
  apply (rule admD[OF compatible_adm2])
  apply assumption+
  done

lemma compatible_to_bot: "compatible x y \<Longrightarrow> to_bot y = to_bot x"
by (metis join_above1 join_above2 unrelated)

lemma subpcpo_bot_jfc': "subpcpo_bot (fix_join_compat' \<rho>) (to_bot \<rho>)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo' subcpo_jfc')
  apply (auto)
  apply (metis below.r_refl compatibleI to_bot_minimal)
  by (metis compatible_to_bot to_bot_minimal)

lemma subpcpo_jfc': "subpcpo (fix_join_compat' \<rho>)"
   by (rule subpcpo_bot_is_subpcpo[OF subpcpo_bot_jfc'])

lemma bottom_of_jfc': "bottom_of (fix_join_compat' \<rho>) = to_bot \<rho>"
  by (rule bottom_of_subpcpo_bot[OF subpcpo_bot_jfc'])

lemma down_closed_jfc': "down_closed (fix_join_compat' \<rho>)"
  apply (rule down_closedI)
  unfolding fix_join_compat'_def
  apply simp
  by (rule compatible_down_closed2)

lemma compat_jfc': "x \<in> fix_join_compat' \<rho> \<Longrightarrow> compatible \<rho> x"  by simp

context
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition}"
  fixes F :: "'a \<Rightarrow> 'a"
  assumes "cont F"
  assumes F_pres_compat: "\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
begin

  lemma compatible_F_jfc': "x \<in> fix_join_compat' \<rho> \<Longrightarrow> compatible \<rho> (F x)"
    by (metis F_pres_compat compat_jfc')

  lemma closed_jfc': "x \<in> (fix_join_compat' \<rho>) \<Longrightarrow> \<rho> \<squnion> F x \<in> (fix_join_compat' \<rho>)"
    apply auto
    by (metis "HOLCF-Join.join_above1" F_pres_compat below.r_refl compatibleI)

  lemma closed_on_jfc': "closed_on (fix_join_compat' \<rho>) (\<lambda> x. \<rho> \<squnion> F x)"
    by (rule closed_onI, rule closed_jfc')

  lemma cont_on_jfc': "cont_on (fix_join_compat' \<rho>) (\<lambda> x. \<rho> \<squnion> F x)"
  proof(rule subpcpo.cont_onI2[OF subpcpo_jfc'])
  case goal1 show ?case
    apply (rule monofun_onI)
    apply (rule join_mono[OF compat_jfc' compat_jfc' below_refl cont2monofunE[OF `cont F`]])
    apply (metis  compatible_F_jfc' fjc'_iff)
    apply (metis  compatible_F_jfc' fjc'_iff)
    .
  next
  case (goal2 Y)
    hence "chain Y" by (metis chain_on_is_chain)
    show ?case
      apply (rule subst[OF cont2contlubE[OF `cont F` `chain Y`, symmetric]])
      apply (subst join_cont2[OF ch2ch_cont[OF `cont F` `chain Y`] compatible_F_jfc'[OF chain_on_is_on[OF goal2(1)]]])
      apply (rule below_refl)
    done
  qed

end

lemma subset_fjc': "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> fix_join_compat' \<rho>' \<subseteq> fix_join_compat' \<rho>"
  apply rule
  apply simp
  by (rule compatible_down_closed)

lemma fjc'_Inter:
  assumes "chain Y"
  shows "(\<Inter> i. (fix_join_compat' (Y i))) = fix_join_compat' (\<Squnion>i. Y i)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" by (auto intro: admD[OF compatible_adm1 `chain Y`])
next
  show "?R \<subseteq> ?L" by (auto elim: compatible_down_closed intro: is_ub_thelub[OF `chain Y`])
qed

definition fix_join_compat'' where 
  "fix_join_compat'' (\<rho>::'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition})  F = {\<rho>'. \<rho>' \<sqsubseteq> fix_on' (to_bot \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>')}"

lemma fjc''_iff[iff]:
  "\<rho>' \<in> fix_join_compat'' \<rho> F \<longleftrightarrow> \<rho>' \<sqsubseteq> fix_on' (to_bot \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>')"
  unfolding fix_join_compat''_def by auto

lemma subcpo_jfc'': "subcpo (fix_join_compat'' \<rho> F)"
  unfolding fix_join_compat''_def by (rule subcpo_cone_below)

lemma subpcpo_jfc'': "subpcpo (fix_join_compat'' \<rho> F)"
  unfolding fix_join_compat''_def by (rule subpcpo_cone_below)

lemma subpcpo_bot_jfc'': "subpcpo_bot (fix_join_compat'' \<rho> F) (to_bot \<rho>)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo' subcpo_jfc'')
  apply (auto)
  by (metis to_bot_fix_on to_bot_minimal unrelated)

lemma bottom_of_jfc'': "bottom_of (fix_join_compat'' \<rho> F) = to_bot \<rho>"
  by (rule bottom_of_subpcpo_bot[OF subpcpo_bot_jfc''])

lemma down_closed_jfc'': "down_closed (fix_join_compat'' \<rho> F)"
  by (auto intro: down_closedI dest:below_trans)

lemma compat_jfc'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> y \<in> fix_join_compat'' \<rho> F \<Longrightarrow> compatible x y"
  by (auto elim:ub_implies_compatible)

lemma join_jfc'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> y \<in> fix_join_compat'' \<rho> F \<Longrightarrow> x \<squnion> y \<in> fix_join_compat'' \<rho> F"
  by (rule, metis join_below[OF compat_jfc''] fjc''_iff)

lemma closed_on_join_jfc'': "closed_on (fix_join_compat'' \<rho> F) G \<Longrightarrow> closed_on (fix_join_compat'' \<rho> F) H \<Longrightarrow> closed_on (fix_join_compat'' \<rho> F) (\<lambda> x. G x \<squnion> H x)"
  apply (rule closed_onI)
  apply (rule join_jfc'')
  apply (erule (1) closed_onE)+
  done

lemma cont_on_join_jfc':
  assumes "closed_on (fix_join_compat'' \<rho> F) G"
  assumes "closed_on (fix_join_compat'' \<rho> F) H"
  assumes "cont_on  (fix_join_compat'' \<rho> F) G"
  assumes "cont_on  (fix_join_compat'' \<rho> F) H"
  shows "cont_on (fix_join_compat'' \<rho> F) (\<lambda> x. G x \<squnion> H x)"
  proof(rule subpcpo.cont_onI2[OF subpcpo_jfc''])
  case goal1
  show ?case
    proof(rule monofun_onI)
    case (goal1 x y)
      hence "compatible (G x) (H x)" and "compatible (G y) (H y)"
        by -(rule compat_jfc''[OF closed_onE[OF assms(1)] closed_onE[OF assms(2)]], assumption+)+
      moreover
      from goal1
      have "G x \<sqsubseteq> G y"
        by (rule monofun_onE[OF cont_on2mono_on[OF assms(3)]])
      moreover
      from goal1
      have "H x \<sqsubseteq> H y"
        by (rule monofun_onE[OF cont_on2mono_on[OF assms(4)]])
      ultimately
      show ?case
        by (rule join_mono)
    qed
  next
  case (goal2 Y)
    have "G (\<Squnion> i. Y i) \<squnion> H (\<Squnion> i. Y i) = (\<Squnion> i. G (Y i)) \<squnion> (\<Squnion> i. H (Y i))"
      by (simp add: cont_on2contlubE[OF assms(3) goal2(1)]  cont_on2contlubE[OF assms(4) goal2(1)])
    also
    have "... = (\<Squnion> i. G (Y i) \<squnion> H (Y i))"
      apply (rule join_cont12)
      apply (rule chain_on_is_chain[OF ch2ch_cont_on'[OF assms(3) goal2(1) assms(1)]])
      apply (rule chain_on_is_chain[OF ch2ch_cont_on'[OF assms(4) goal2(1) assms(2)]])
      apply (rule compat_jfc''[OF closed_onE[OF assms(1) chain_on_is_on[OF goal2(1)]] closed_onE[OF assms(2) chain_on_is_on[OF goal2(1)]]])
      done
   finally show ?case by (rule eq_imp_below)
qed

inductive fix_on_cond_jfc'
  where fix_on_cond_jfc'I:
  "cont F \<Longrightarrow>
   (\<And> i. compatible \<rho> (F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>)))) \<Longrightarrow> fix_on_cond_jfc' \<rho> F "


context
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition}" and S and F
  assumes "fix_on_cond_jfc' \<rho> F"
begin
  lemma cont_F_jfc'': "cont F"
    by (rule fix_on_cond_jfc'.induct[OF `fix_on_cond_jfc' _ _`]) 

  lemma chain_compat_jfc'': "compatible \<rho> (F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>)))"
    by (rule fix_on_cond_jfc'.induct[OF `fix_on_cond_jfc' _ _`]) 

  lemma chain_jfc'': "chain (\<lambda>i. ((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')^^i) (to_bot \<rho>))"
  proof(rule chainI, induct_tac i, simp_all)
    have "to_bot \<rho> \<sqsubseteq> \<rho>"
      by (rule to_bot_minimal)
    also have "\<rho> \<sqsubseteq> \<rho> \<squnion> F (to_bot \<rho>)"
      by (rule join_above1[OF chain_compat_jfc''[of 0, simplified]])
    finally
    show "to_bot \<rho> \<sqsubseteq> \<rho> \<squnion> F (to_bot \<rho>)".
   
    fix n
    assume "((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>) \<sqsubseteq> \<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>))"
    thus "\<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>)) \<sqsubseteq> \<rho> \<squnion> F (\<rho> \<squnion> F (((\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>') ^^ n) (to_bot \<rho>)))"
      by (rule join_mono[OF chain_compat_jfc'' chain_compat_jfc''[of "Suc n", simplified] below_refl cont2monofunE[OF `cont F`]])
  qed 
  
  lemma rho_jfc'': "\<rho> \<in> fix_join_compat'' \<rho> F"
    apply auto
    apply (subst fix_on_def, subst if_P[OF chain_jfc''])
    apply (rule below_trans[OF _ is_ub_thelub[of _ 1, OF chain_jfc'']])
    apply (simp del: funpow.simps(1))
    apply (rule join_above1)
    apply (rule fix_on_cond_jfc'.induct[OF `fix_on_cond_jfc' _ _`])
    apply assumption
    done

  lemma F_pres_compat'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> F x \<in> fix_join_compat'' \<rho> F" 
    apply auto
    apply (drule cont2monofunE[OF cont_F_jfc''])
    apply (erule below_trans)
    apply (subst (1 2) fix_on_def, subst (1 2) if_P[OF chain_jfc''])
    apply (subst cont2contlubE[OF cont_F_jfc'' chain_jfc''])
    apply (subst lub_range_shift[symmetric, OF chain_jfc'', of 1])
    apply (rule lub_mono[OF ch2ch_cont[OF cont_F_jfc'' chain_jfc''] chain_shift[OF chain_jfc'']])
    apply simp
    apply (rule join_above2[OF chain_compat_jfc''])
    done

  lemma rho_F_compat_jfc'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> compatible \<rho> (F x)"
    by (rule compat_jfc''[OF rho_jfc'' F_pres_compat''])


(*
context
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition}"
  fixes F :: "'a \<Rightarrow> 'a"
  assumes "cont F"
  assumes F_pres_compat: "\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
begin
  lemma rho_jfc'': "\<rho> \<in> fix_join_compat'' \<rho> F"
    apply auto
    apply (subst fix_on_jfc'_eq[OF `cont F` F_pres_compat], assumption)
    apply (rule join_above1)
    apply (metis (full_types) F_pres_compat `cont F`  fjc'_iff subpcpo.fix_on_there[OF subpcpo_jfc' cont_on_jfc' closed_on_jfc'])
    done    

  lemma F_pres_compat'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> F x \<in> fix_join_compat'' \<rho> F" 
    apply auto
    apply (subst fix_on_jfc'_eq[OF `cont F` F_pres_compat], assumption)
    apply (rule below_trans)
    apply (erule cont2monofunE[OF `cont F`])
    apply (rule join_above2)
    by (metis (full_types) F_pres_compat `cont F` closed_on_jfc' compatible_F_jfc' cont_on_jfc' subpcpo.fix_on_there subpcpo_jfc')
*)

  lemma F_closed_on_jfc'': "closed_on (fix_join_compat'' \<rho> F) F"
    by (rule, rule F_pres_compat'')

  lemma closed_jfc'': "x \<in> fix_join_compat'' \<rho> F \<Longrightarrow> \<rho> \<squnion> F x \<in> fix_join_compat'' \<rho> F"
    by (metis F_pres_compat'' rho_jfc'' join_jfc'')

  lemma closed_on_jfc'': "closed_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x)"
    by (rule closed_onI, rule closed_jfc'')

  lemma cont_on_jfc'': "cont_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x)"
    by (rule cont_on_join_jfc'[OF const_closed_on[OF rho_jfc''] F_closed_on_jfc'' cont_is_cont_on[OF cont_const] cont_is_cont_on[OF `cont F`]]) 

  lemma fix_on_cond_jfc'':
    "fix_on_cond (fix_join_compat'' \<rho> F) (bottom_of (fix_join_compat'' \<rho> F)) (\<lambda>x. \<rho> \<squnion> F x)"
    apply (subst bottom_of_jfc'')
    by (rule fix_on_condI[OF subpcpo_jfc'' bottom_of_jfc'' closed_on_jfc'' cont_on_jfc''])

  lemma fix_on_jfc''_ind:
    assumes "adm_on (fix_join_compat'' \<rho> F) P"
    assumes "P (bottom_of (fix_join_compat'' \<rho> F))"
    assumes "\<And> y. y \<in> fix_join_compat'' \<rho> F \<Longrightarrow> P y \<Longrightarrow> P (\<rho> \<squnion> F y)"
    shows "P (fix_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x))"
      by (rule fix_on_ind[OF fix_on_cond_jfc'' assms])

  lemma fix_on_jfc''_eq:
    shows "fix_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x) = \<rho> \<squnion> F (fix_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x))"
    by (rule fix_on_eq[OF fix_on_cond_jfc''])
end

(*
lemma fix_on_jfc''_mono'':
  fixes \<rho> \<rho>':: "'a::{Bounded_Nonempty_Meet_cpo, subpcpo_partition}"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  assumes "cont F"
  assumes F_pres_compat1: "\<And> i x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
  assumes F_pres_compat2: "\<And> i x. compatible \<rho>' x \<Longrightarrow> compatible \<rho>' (F x)"

  shows "fix_on (fix_join_compat'' \<rho> F) (\<lambda> x. \<rho> \<squnion> F x) \<sqsubseteq> (fix_on (fix_join_compat'' \<rho>' F) (\<lambda> x. \<rho>' \<squnion> F x))"
  apply (rule parallel_fix_on_ind[OF subpcpo_jfc'' subpcpo_jfc''])
  apply (rule adm_is_adm_on, simp)
  apply (metis closed_on_jfc'' assms(2) assms(3))
  apply (metis cont_on_jfc'' assms(2) assms(3))
  apply (metis closed_on_jfc'' assms(2) assms(4))
  apply (metis cont_on_jfc'' assms(2) assms(4))
  apply (subst (1 2) bottom_of_jfc'')
  apply (rule eq_imp_below[OF unrelated[OF assms(1)]])
  by (metis F_pres_compat1 F_pres_compat2 assms(1) assms(2) cont2monofunE compat_jfc'' rho_jfc'' join_mono)
*)

lemma subset_fjc'':
  assumes "cont F"
  assumes "fix_on_cond_jfc' \<rho> F"
  assumes "fix_on_cond_jfc' \<rho>' F"
  shows "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> fix_join_compat'' \<rho> F \<subseteq> fix_join_compat'' \<rho>' F"
  apply rule
  apply (simp only: fjc''_iff)
  apply (erule below_trans)
  apply (rule fix_on_mono2[OF fix_on_cond_jfc''[OF assms(2)] fix_on_cond_jfc''[OF assms(3)], unfolded bottom_of_jfc''])
  apply (metis po_eq_conv unrelated)
  by (rule join_mono[OF
        rho_F_compat_jfc''[OF assms(2)]
        rho_F_compat_jfc''[OF assms(3)]
        _
        cont2monofunE[OF `cont F`]])

(*
lemma subset_fjc'':
  assumes "cont F"
  assumes F_pres_compat1: "\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
  assumes F_pres_compat2: "\<And> x. compatible \<rho>' x \<Longrightarrow> compatible \<rho>' (F x)"
  shows "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> fix_join_compat'' \<rho> F \<subseteq> fix_join_compat'' \<rho>' F"
  apply rule
  apply simp
  apply (erule below_trans)
  apply (rule fix_on_mono2[OF subpcpo_jfc' subpcpo_jfc' closed_on_jfc' cont_on_jfc' closed_on_jfc' cont_on_jfc'])
  apply (auto simp add: assms)
  apply (metis bottom_of_jfc' po_eq_conv unrelated)
  apply (erule (3) join_mono[OF F_pres_compat1 F_pres_compat2 _ cont2monofunE[OF `cont F`]])
  done
*)

(* Wrong 
lemma jfc''_Union:
  assumes "chain Y"
  assumes "cont F"
  assumes F_pres_compat: "\<And> i x. compatible (Y i) x \<Longrightarrow> compatible (Y i) (F x)"
  assumes F_pres_compat': "\<And> x. compatible (\<Squnion> i. Y i) x \<Longrightarrow> compatible (\<Squnion> i. Y i) (F x)"
*)

lemma fix_on_join_cont'_general:
  fixes F :: "'a::Bounded_Nonempty_Meet_cpo \<Rightarrow> 'a"
  assumes "subpcpo S'"
  assumes pcpo_i: "\<And> i. subpcpo (S i)"
  assumes "down_closed S'"
  assumes down_closed: "\<And> i. down_closed (S i)"
  assumes same_bottoms: "\<And> i j. bottom_of (S i) = bottom_of (S j)"
  assumes same_bottoms'[simp]: "\<And> i. bottom_of (S i) = bottom_of S'"
  assumes "chain Y"
  assumes "cont F"
  assumes compat: "\<And> i x. x \<in> S i \<Longrightarrow> compatible (Y i) (F x)"
  assumes compat': "\<And> x. x \<in> S' \<Longrightarrow> compatible (\<Squnion> i. Y i) (F x)"
  assumes cl: "\<And> i. closed_on (S i) (\<lambda>x. Y i \<squnion> F x)"
  assumes cl': "\<And> i. closed_on S' (\<lambda>x. (\<Squnion>i. Y i) \<squnion> F x)"

  shows "fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on _ _ = Lub ?F")
proof-
  interpret subpcpo S' by fact
  interpret down_closed S' by fact

  have coF: "cont_on S' F" by (rule cont_is_cont_on[OF `cont F`])

  have co: "\<And> i. cont_on (S i) (\<lambda>x. Y i \<squnion> F x)"
  proof(rule subpcpo.cont_onI2[OF pcpo_i])
  case goal1 show ?case
    by (rule monofun_onI, erule (2) join_mono[OF compat compat below_refl cont2monofunE[OF `cont F`]])
  next
  case (goal2 i Y)
    hence "chain Y" by (metis chain_on_is_chain)
    show ?case
      apply (rule subst[OF cont2contlubE[OF `cont F` `chain Y`, symmetric]])
      apply (subst join_cont2[OF ch2ch_cont[OF `cont F` `chain Y`] compat[OF chain_on_is_on[OF goal2(1)]]])
      apply (rule below_refl)
    done
  qed

  have co': "cont_on S' (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
  proof(rule cont_onI2)
  case goal1 show ?case
    by (rule monofun_onI, rule join_mono[OF compat' compat' below_refl cont2monofunE[OF `cont F`]])
  next
  case (goal2 Y)
    hence "chain Y" by (metis chain_on_is_chain)
    show ?case
      apply (rule subst[OF cont2contlubE[OF `cont F` `chain Y`, symmetric]])
      apply (subst join_cont2[OF ch2ch_cont[OF `cont F` `chain Y`] compat'[OF chain_on_is_on[OF goal2(1)]]])
      apply (rule below_refl)
    done
  qed

  have foc': "fix_on_cond S' (bottom_of S') (\<lambda>x. (\<Squnion>i. Y i) \<squnion> F x)"
    by (rule fix_on_condI[OF subpcpo_axioms refl cl' co'])
  have foc: "\<And> i. fix_on_cond (S i) (bottom_of (S i)) (\<lambda>x. Y i \<squnion> F x)"
    by (rule fix_on_condI[OF pcpo_i refl cl co])

  { fix i j
    have  "compatible (Y j) (F (?F i))"
    proof(cases "i \<le> j")
    case True show ?thesis
      apply (rule compatible_down_closed2)
      apply (rule compat[OF fix_on_there[OF foc]])
      apply (rule cont2monofunE[OF `cont F`])
      apply (rule fix_on_mono2[OF foc foc eq_imp_below[OF same_bottoms]])
      apply (erule (2) join_mono[OF compat compat chain_mono[OF `chain Y` True] cont2monofunE[OF `cont F`] ])
      done
   next
   case False
     hence "j \<le> i" by (metis nat_le_linear)
     thus ?thesis
       by (rule compatible_down_closed[OF compat[OF fix_on_there[OF foc]] chain_mono[OF `chain Y`]])
   qed
  } note compat'' = this

  have  "fix_on S' (\<lambda>x. (Lub Y) \<squnion> F x) \<in> S'"
    by (rule fix_on_there[OF foc'])
  moreover
  have "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<sqsubseteq> fix_on S' (\<lambda>x. (Lub Y) \<squnion> F x)"
    apply (rule fix_on_mono2[OF foc foc'])
    apply simp      
    apply (erule (2) join_mono[OF
        compat
        compat'
        is_ub_thelub[OF `chain Y`]
        cont2monofunE[OF `cont F`]])
    done
  ultimately
  have F_in_S: "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<in> S'"
    by (rule down_closedE)

  have chF: "chain ?F"
    apply (rule chainI)
    apply (rule fix_on_mono2[OF foc foc])
    apply simp
    by (rule join_mono[OF compat compat chainE[OF `chain Y`] cont2monofunE[OF `cont F`]])
  have cho: "chain_on S' ?F"
    apply (rule chain_onI[OF _ F_in_S])
    apply (rule chainE[OF chF])
    done

  have c1: "\<And> j. chain (\<lambda>i. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' chainE[OF `chain Y`] below_refl])
  have c2: "\<And> i. chain (\<lambda>j. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' below_refl cont2monofunE[OF `cont F` chainE[OF chF]]])
  have c3: "chain (\<lambda>i. F (?F i))"
    by (rule ch2ch_cont[OF `cont F` chF])

  have "(\<Squnion> i. ?F i) \<in> S'"
    by (rule chain_on_lub_on[OF cho])
  moreover
  {
  have "(\<Squnion> i. Y i) \<squnion> F (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))
    = (\<Squnion> i. Y i) \<squnion> (\<Squnion> i. F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x)))"
    by (subst cont_on2contlubE[OF coF cho], rule)
  also have " ... = (\<Squnion> i. Y i \<squnion> (\<Squnion> i. F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x))))"
    by (rule join_cont1[OF `chain Y` admD[OF compatible_adm2 c3 compat'']])
  also have " ... = (\<Squnion> i j. Y i \<squnion> F (fix_on (S j) (\<lambda>x. Y j \<squnion> F x)))"
    by (subst join_cont2[OF c3 compat''], rule)
  also have " ... = (\<Squnion> i. Y i \<squnion> F (fix_on (S i) (\<lambda>x. Y i \<squnion> F x)))"
    by (rule diag_lub[OF c1 c2])
  also have " ... = (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))"
    by (subst fix_on_eq[symmetric, OF foc], rule)
  also note calculation
  }
  hence "(\<Squnion> i. Y i) \<squnion> F (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x)) \<sqsubseteq> (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))"
    by (rule eq_imp_below)
  ultimately
  have "fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    by (rule fix_on_least_below[OF foc'])
  moreover
  have  "(\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x))) \<sqsubseteq> fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x)"
  proof (rule lub_below[OF chF])
    fix i
    show "(fix_on (S i) (\<lambda> x. Y i \<squnion> F x)) \<sqsubseteq> fix_on S' (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x)"
      apply (rule fix_on_mono2[OF foc foc' eq_imp_below[OF same_bottoms']])
      by (rule join_mono[OF compat compat' is_ub_thelub[OF `chain Y`] cont2monofunE[OF `cont F`]])
  qed
  finally
  show ?thesis.
qed


lemma fix_on_join_cont':
  fixes F :: "'a::Bounded_Nonempty_Meet_cpo \<Rightarrow> 'a"
  assumes pcpo_i: "\<And> i. subpcpo (S i)"
  assumes down_closed: "\<And> i. down_closed (S i)"
  assumes ss: "\<And> i j. S (j + i) \<subseteq> S i"
  assumes "chain Y"
  assumes "cont F"
  assumes compat: "\<And> i x. x \<in> S i \<Longrightarrow> compatible (Y i) (F x)"
  assumes cl: "\<And> i. closed_on (S i) (\<lambda>x. Y i \<squnion> F x)"

  shows "fix_on (\<Inter> i. S i) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on ?S _ = Lub ?F")
proof(rule fix_on_join_cont'_general[OF _ pcpo_i _ down_closed _ _ `chain Y` `cont F` compat _ cl])
  show same_bottoms: "\<And> i j. bottom_of (S i) = bottom_of (S j)"
  proof-
    {
    fix i j :: nat
    assume "i < j"
    
    have "S j \<subseteq> S i"
      using `i < j` by (metis less_imp_add_positive nat_add_commute ss)
    hence "bottom_of (S j) \<in> S i"
      by (rule subsetD[OF _ subpcpo.bottom_of_there[OF pcpo_i]])
    hence b: "bottom_of (S i) \<sqsubseteq> bottom_of (S j)"
      by (rule subpcpo.bottom_of_minimal[OF pcpo_i])
    moreover
    have "bottom_of (S i) \<in> S j"
      by (rule down_closed.down_closedE[OF down_closed subpcpo.bottom_of_there[OF pcpo_i] b])
    hence "bottom_of (S j) \<sqsubseteq> bottom_of (S i)"
      by (rule subpcpo.bottom_of_minimal[OF pcpo_i])
    finally
    have "bottom_of (S j) = bottom_of (S i)"..
    }
    thus "\<And> i j. bottom_of (S i) = bottom_of (S j)" by (metis linorder_neqE_nat)
  qed

  interpret subpcpo ?S by (rule subpcpo_Inter[OF pcpo_i same_bottoms])
  show "subpcpo ?S" by (rule subpcpo_axioms)
  interpret down_closed ?S by (metis down_closed down_closed_Inter)
  show "down_closed ?S" by (rule down_closed_axioms)

  show same_bottoms'[simp]: "\<And> i. bottom_of (S i) = bottom_of ?S"
    by (metis bottom_of_Inter pcpo_i same_bottoms)
  have ss': "\<And> i. ?S \<subseteq> S i"
    by (metis INF_lower UNIV_I)

  show compat': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (\<Squnion>i. Y i) (F x)"
    by (rule admD[OF compatible_adm1 `chain Y` compat[OF subsetD[OF ss']]])

  show cl': "closed_on ?S (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
  proof (rule closed_onI)
    fix x
    assume  "x \<in> (\<Inter>i. S i)"
    hence x: "\<And>i. x \<in> S i" by (metis INT_E UNIV_I)
    have "\<And> i. (\<Squnion> i. Y i) \<squnion> F x \<in> S i"
    proof-
      fix i
      have "chain_on (S i) (\<lambda> j. Y (j + i) \<squnion> F x )"
        apply (rule chain_onI[OF 
            join_mono[OF
               compat[OF x]
               compat[OF x]
               _
               below_refl]
            subsetD[OF ss closed_onE[OF cl x]]
            ])
        by (simp add: chainE[OF `chain Y`])
      hence "(\<Squnion> j. Y (j + i) \<squnion> F x) \<in> S i" by (rule subpcpo.chain_on_lub_on[OF pcpo_i])
      hence "(\<Squnion> j. Y (j + i)) \<squnion> F x \<in> S i"
        by (subst join_cont1[OF chain_shift[OF `chain Y`] compat[OF x]])
      thus "(\<Squnion> i. Y i) \<squnion> F x \<in> S i"
        by (subst (asm) lub_range_shift[OF `chain Y`])
    qed
    thus "(\<Squnion> i. Y i) \<squnion> F x \<in> (\<Inter>i. S i)" by (metis INT_iff)
  qed
qed

lemma closed_on_Union:
  assumes "\<And> i. closed_on (S i) F"
  shows "closed_on (\<Union>i. S i) F"
  apply (rule closed_onI)
  apply (erule UN_E)
  apply (rule UN_I[OF UNIV_I])
  apply (erule closed_onE[OF assms])
  done


lemma fix_on_join_cont'_covariant:
  fixes F :: "'a::Bounded_Nonempty_Meet_cpo \<Rightarrow> 'a"
  assumes pcpo: "subpcpo (\<Union> i. S i)"
  assumes pcpo_i: "\<And> i. subpcpo (S i)"
  assumes down_closed: "\<And> i. down_closed (S i)"
  assumes ss: "\<And> i j. S i \<subseteq> S (j + i)"
  assumes "chain Y"
  assumes "cont F"
  assumes compat: "\<And> i x. x \<in> S i \<Longrightarrow> compatible (Y i) (F x)"
  assumes cl: "\<And> i. closed_on (S i) (\<lambda>x. Y i \<squnion> F x)"

  shows "fix_on (\<Union> i. S i) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on ?S _ = Lub ?F")
proof(rule fix_on_join_cont'_general[OF pcpo pcpo_i _ down_closed _ _ `chain Y` `cont F` compat _ cl])
  show same_bottoms: "\<And> i j. bottom_of (S i) = bottom_of (S j)"
  proof-
    {
    fix i j :: nat
    assume "i < j"
    
    have "S i \<subseteq> S j"
      using `i < j` by (metis less_imp_add_positive nat_add_commute ss)
    hence "bottom_of (S i) \<in> S j"
      by (rule subsetD[OF _ subpcpo.bottom_of_there[OF pcpo_i]])
    hence b: "bottom_of (S j) \<sqsubseteq> bottom_of (S i)"
      by (rule subpcpo.bottom_of_minimal[OF pcpo_i])
    moreover
    have "bottom_of (S j) \<in> S i"
      by (rule down_closed.down_closedE[OF down_closed subpcpo.bottom_of_there[OF pcpo_i] b])
    hence "bottom_of (S i) \<sqsubseteq> bottom_of (S j)"
      by (rule subpcpo.bottom_of_minimal[OF pcpo_i])
    finally
    have "bottom_of (S i) = bottom_of (S j)"..
    }
    thus "\<And> i j. bottom_of (S i) = bottom_of (S j)" by (metis linorder_neqE_nat)
  qed

  interpret subpcpo ?S by fact
  interpret down_closed ?S
    apply (rule down_closedI)
    apply (erule UN_E)
    apply (rule UN_I[OF UNIV_I down_closed.down_closedE])
    by (metis down_closed )
  show "down_closed ?S" by (rule down_closed_axioms)

  have ss': "\<And> i. S i \<subseteq> ?S"
    by (metis SUP_upper UNIV_I)
  show same_bottoms'[simp]: "\<And> i. bottom_of (S i) = bottom_of ?S"
    apply (rule below_antisym)
    apply (metis UN_E bottom_of_there pcpo_i same_bottoms subpcpo.bottom_of_minimal)
    by (metis bottom_of_minimal pcpo_i set_mp ss' subpcpo.bottom_of_there)

  show compat': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (\<Squnion>i. Y i) (F x)"
  proof-
    fix x
    assume "x \<in> ?S"
    then obtain i where "x \<in> S i" by auto
    hence "\<And> j. x \<in> S (j + i)" by (metis in_mono ss)
    hence "\<And> j. compatible (Y (j + i)) (F x)" by (rule compat)
    hence "compatible (\<Squnion> j. (Y (j + i))) (F x)"
      by (rule admD[OF compatible_adm1 chain_shift[OF `chain Y`]])
    thus "compatible (\<Squnion>i. Y i) (F x)"
      by (metis lub_range_shift[OF `chain Y`])
  qed

  show cl': "closed_on ?S (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
  proof (rule closed_onI)
    fix x
    assume  "x \<in> (\<Union>i. S i)"
    then obtain i where "x \<in> S i" by auto
    hence j: "\<And> j. x \<in> S (j + i)" by (metis in_mono ss)
    hence "\<And> j. Y (j + i) \<squnion> (F x) \<in> S (j + i)" by (rule closed_onE[OF cl])
    hence "\<And> j. Y (j + i) \<squnion> (F x) \<in> (\<Union> i. S i)" by (metis UNIV_I UN_iff)
    hence "chain_on ?S (\<lambda>j. Y (j + i) \<squnion> (F x))"
      apply -
      apply (rule chain_onI)
      apply (rule join_mono[OF compat[OF j] compat[OF j] _ below_refl])
      apply (metis add_Suc_right add_Suc_shift chainE[OF `chain Y`])
      apply assumption
      done
    hence "(\<Squnion>j. Y (j + i) \<squnion> (F x)) \<in> (\<Union> i. S i)" by (rule chain_on_lub_on)
    hence "(\<Squnion>j. Y (j + i)) \<squnion> (F x) \<in> (\<Union> i. S i)"
      apply (subst join_cont1[OF chain_shift[OF `chain Y`]])
      apply (rule compat[OF j])
      apply auto
      done
    thus "(\<Squnion>i. Y i) \<squnion> (F x) \<in> (\<Union> i. S i)"
      by (metis lub_range_shift[OF `chain Y`])
   qed
qed

lemma fix_on_join_cont'':
  fixes Y :: "nat \<Rightarrow> 'a::{Bounded_Nonempty_Meet_cpo, subpcpo_partition}"
  assumes "chain Y"
  assumes "cont F"
  assumes F_pres_compat: "\<And> i x. compatible (Y i) x \<Longrightarrow> compatible (Y i) (F x)"

  shows "fix_on (fix_join_compat' (\<Squnion> i. Y i)) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (fix_join_compat' (Y i)) (\<lambda> x. Y i \<squnion> F x)))"
proof-
  have "fix_on (\<Inter> i. (fix_join_compat' (Y i))) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (fix_join_compat' (Y i)) (\<lambda> x. Y i \<squnion> F x)))"
  apply (rule fix_on_join_cont'[OF subpcpo_jfc' down_closed_jfc'])
  apply (metis subset_fjc'[OF chain_mono[OF `chain Y`]] le_add1 nat_add_commute)
  apply fact+
  apply (metis compatible_F_jfc' assms(2) assms(3))
  apply (metis closed_onI closed_jfc' assms(2) assms(3))
  done
  thus ?thesis unfolding fjc'_Inter[OF `chain Y`].
qed

lemma fix_on_join_cont''':
  fixes Y :: "nat \<Rightarrow> 'a::{Bounded_Nonempty_Meet_cpo, subpcpo_partition}"
  assumes "chain Y"
  assumes focj: "\<And>i. fix_on_cond_jfc' (Y i) F"
  assumes focj': "fix_on_cond_jfc' (\<Squnion> i. Y i) F"

  shows "fix_on (fix_join_compat'' (\<Squnion> i. Y i) F) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) = (\<Squnion> i. (fix_on (fix_join_compat'' (Y i) F) (\<lambda> x. Y i \<squnion> F x)))"
proof(rule fix_on_join_cont'_general)
  fix i
  show "\<And> j. bottom_of (fix_join_compat'' (Y i) F) = bottom_of (fix_join_compat'' (Y j) F)"
    apply (simp add: bottom_of_jfc'')
    by (metis linorder_linear unrelated[OF chain_mono[OF `chain Y`]])
  next
  fix i
  show "bottom_of (fix_join_compat'' (Y i) F) = bottom_of (fix_join_compat'' (\<Squnion> i. Y i) F)"
    apply (simp add: bottom_of_jfc'')
    by (rule unrelated[OF is_ub_thelub[OF `chain Y`]])
  next
  show "cont F"
    by (rule cont_F_jfc''[OF focj])
  next
  fix i x
  assume "x \<in> fix_join_compat'' (Y i) F"
  thus "compatible (Y i) (F x)"
    by (rule rho_F_compat_jfc''[OF focj])
  next
  fix x
  assume "x \<in> fix_join_compat'' (\<Squnion> i. Y i) F"
  thus "compatible (\<Squnion> i. Y i) (F x)"
    by (rule rho_F_compat_jfc''[OF focj'])
  next
  fix i
  show "closed_on (fix_join_compat'' (Y i) F) (\<lambda>x. Y i \<squnion> F x)"
    by (rule closed_on_jfc''[OF focj])
  next
  fix i
  show "closed_on (fix_join_compat'' (\<Squnion> i. Y i) F) (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
    by (rule closed_on_jfc''[OF focj'])
qed (intro subpcpo_jfc'' down_closed_jfc'' rho_F_compat_jfc'' closed_on_jfc'' assms)+

end
