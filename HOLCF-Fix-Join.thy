theory "HOLCF-Fix-Join"
  imports "HOLCF-Set" "HOLCF-Join" "HOLCF-Down-Closed"
begin

inductive_set fix_join_compat
  for \<rho> :: "'a::{Nonempty_Meet_cpo,pcpo}" and F :: "'a \<Rightarrow> 'a"
  where
  "\<bottom> \<in> fix_join_compat \<rho> F" |
  "x \<in> fix_join_compat \<rho> F \<Longrightarrow> F x \<in> fix_join_compat \<rho> F" |
  "x \<in> fix_join_compat \<rho> F \<Longrightarrow> compatible \<rho> x \<Longrightarrow> \<rho> \<squnion> x \<in> fix_join_compat \<rho> F" |
  "x \<in> fix_join_compat \<rho> F \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> fix_join_compat \<rho> F" |
  "chain Y \<Longrightarrow> (\<And>i. Y i \<in> fix_join_compat \<rho> F) \<Longrightarrow> (\<Squnion> i. Y i) \<in> fix_join_compat \<rho> F"

context
  fixes \<rho> :: "'a::{Nonempty_Meet_cpo,pcpo}" and F :: "'a \<Rightarrow> 'a" and S :: "'a set"
  defines "S \<equiv> fix_join_compat \<rho> F"
  assumes "cont F"
  assumes F_pres_compat: "\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
begin
  lemma subcpo_jfc: "subcpo S"
    unfolding S_def
    by (rule subcpoI, rule fix_join_compat.intros(5))

 lemma subpcpo_jfc: "subpcpo S"
    apply (rule subpcpoI2[OF subcpo_jfc, of \<bottom>])
    apply (auto intro: fix_join_compat.intros simp add: S_def )
    done

  lemma down_closed_jfc: "down_closed S"
    unfolding S_def
    by (rule down_closedI, rule fix_join_compat.intros(4))

  lemma compat_jfc: "x \<in> S \<Longrightarrow> compatible \<rho> x"
  proof (erule fix_join_compat.induct[of _ \<rho> F, unfolded S_def[symmetric], rule_format])
    show "compatible \<rho> \<bottom>" by simp
  next
  case (goal2 x)
    thus ?case by (metis F_pres_compat)
  next
  case (goal3 x)
    thus ?case by (metis join_above1 below.r_refl compatibleI)
  next
  case (goal4 x)
    thus ?case by (metis compatible_down_closed compatible_sym_iff)
  next
  case (goal5 Y)
    thus ?case by (metis admD[OF compatible_adm2])
  qed

  lemma compatible_F_jfc: "x \<in> S \<Longrightarrow> compatible \<rho> (F x)"
    by (metis F_pres_compat compat_jfc)

  lemma closed_jfc: "x \<in> S \<Longrightarrow> \<rho> \<squnion> F x \<in> S"
    by (metis S_def compat_jfc fix_join_compat.intros(2) fix_join_compat.intros(3))
end

lemma "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> fix_join_compat \<rho>' F \<subseteq> fix_join_compat \<rho> F"
  apply rule
  apply (erule fix_join_compat.induct)
  apply (auto intro: fix_join_compat.intros)
  oops

definition fix_join_compat' :: "'a::{Nonempty_Meet_cpo,pcpo} \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set"
  where "fix_join_compat' \<rho> F = {x. compatible \<rho> x}"

lemma fjc'_iff[iff]:
  "x \<in> fix_join_compat' \<rho> F \<longleftrightarrow> compatible \<rho> x"
  unfolding fix_join_compat'_def by auto

context
  fixes \<rho> :: "'a::{Nonempty_Meet_cpo,pcpo}" and F :: "'a \<Rightarrow> 'a" and S :: "'a set"
  defines "S \<equiv> fix_join_compat' \<rho> F"
  assumes "cont F"
  assumes F_pres_compat: "\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
begin
  lemma subcpo_jfc': "subcpo S"
    unfolding S_def
    apply (rule subcpoI)
    apply simp
    (* apply (rule admD[OF adm_subst[OF `cont F` compatible_adm2]])*)
    apply (rule admD[OF compatible_adm2])
    apply assumption+
    done

 lemma subpcpo_jfc': "subpcpo S"
    apply (rule subpcpoI2[OF subcpo_jfc', of \<bottom>])
    apply (auto simp add: S_def intro:F_pres_compat)
    done

  lemma down_closed_jfc': "down_closed S"
    unfolding S_def
    by (auto intro: down_closedI cont2monofunE[OF `cont F`] compatible_down_closed2)

  lemma compat_jfc': "x \<in> S \<Longrightarrow> compatible \<rho> x" unfolding S_def by simp

  lemma compatible_F_jfc': "x \<in> S \<Longrightarrow> compatible \<rho> (F x)"
    by (metis F_pres_compat compat_jfc')

  lemma closed_jfc': "x \<in> S \<Longrightarrow> \<rho> \<squnion> F x \<in> S"
    unfolding S_def
    apply auto
    by (metis "HOLCF-Join.join_above1" F_pres_compat below.r_refl compatibleI)
end

lemma subset_fjc': "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> fix_join_compat' \<rho>' F \<subseteq> fix_join_compat' \<rho> F"
  apply rule
  apply simp
  by (rule compatible_down_closed)

lemma fix_on_join_cont':
  fixes F :: "'a::pcpo \<Rightarrow> 'a"
  assumes pcpo_i: "\<And> i. subpcpo (S i)"
  assumes down_closed: "\<And> i. down_closed (S i)"
  assumes ss: "\<And> i j. S (j + i) \<subseteq> S i"
  assumes "chain Y"
  assumes "cont F"
  assumes compat: "\<And> i x. x \<in> S i \<Longrightarrow> compatible (Y i) (F x)"
  assumes cl: "\<And> i. closed_on (S i) (\<lambda>x. Y i \<squnion> F x)"

  shows "fix_on (\<Inter> i. S i) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (fix_on (S i) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on ?S _ \<sqsubseteq> Lub ?F")
proof-
  have same_bottoms: "\<And> i j. bottom_of (S i) = bottom_of (S j)"
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
  interpret down_closed ?S by (metis down_closed down_closed_Inter)

  have same_bottoms'[simp]: "\<And> i. bottom_of (S i) = bottom_of ?S"
    by (metis bottom_of_Inter pcpo_i same_bottoms)
  have ss': "\<And> i. ?S \<subseteq> S i"
    by (metis INF_lower UNIV_I)

  note compat' = admD[OF compatible_adm1 `chain Y` compat[OF subsetD[OF ss']]]

  have coF: "cont_on ?S F" by (rule cont_is_cont_on[OF `cont F`])

  have cl': "closed_on ?S (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
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

  have co': "cont_on ?S (\<lambda>x. (\<Squnion> i. Y i) \<squnion> F x)"
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

  have co'': "\<And> i. cont_on ?S (\<lambda>x. Y i \<squnion> F x)"
    by (rule cont_on_subset[OF co ss'])
  have cl'': "\<And> i. closed_on ?S (\<lambda>x. Y i \<squnion> F x)"
    by (rule closed_onI, rule down_closedE[OF
        closed_onE[OF cl']
        join_mono[OF
          compat[OF subsetD[OF ss']]
          compat'
          is_ub_thelub[OF `chain Y`]
          below_refl]])

  have compat'': "\<And>j i. compatible (Y j) (F (?F i))"
    apply (rule compat)
    apply (rule subsetD[OF ss'])
    apply (subst fix_on_same[OF pcpo_i subpcpo_axioms cl co cl'' co'' same_bottoms'])
    apply (rule fix_on_there[OF co'' cl''])
    done

  have  "fix_on ?S (\<lambda>x. (Lub Y) \<squnion> F x) \<in> ?S"
    by (rule fix_on_there[OF co' cl'])
  moreover
  have "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<sqsubseteq> fix_on ?S (\<lambda>x. (Lub Y) \<squnion> F x)"
    apply (rule fix_on_mono2[OF pcpo_i subpcpo_axioms cl co cl' co'])
    apply simp
    apply (erule (2) join_mono[OF
        compat
        compat'
        is_ub_thelub[OF `chain Y`]
        cont2monofunE[OF `cont F`]])
    done
  ultimately
  have F_in_S: "\<And> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x) \<in> ?S"
    by (rule down_closedE)

  have chF: "chain ?F"
    apply (rule chainI)
    apply (rule fix_on_mono2[OF pcpo_i pcpo_i cl co cl co ])
    apply simp
    by (rule join_mono[OF compat compat chainE[OF `chain Y`] cont2monofunE[OF `cont F`]])
  have cho: "chain_on ?S ?F"
    apply (rule chain_onI[OF _ F_in_S])
    apply (rule chainE[OF chF])
    done

  have c1: "\<And> j y. chain (\<lambda>i. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' chainE[OF `chain Y`] below_refl])
  have c2: "\<And> i. chain (\<lambda>j. Y i \<squnion> F (?F j))"
    by (rule chainI, rule join_mono[OF compat'' compat'' below_refl cont2monofunE[OF `cont F` chainE[OF chF]]])
  have c3: "chain (\<lambda>i. F (?F i))"
    by (rule ch2ch_cont[OF `cont F` chF])

  have "(\<Squnion> i. ?F i) \<in> ?S"
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
    by (subst subpcpo.fix_on_eq[symmetric, OF pcpo_i co cl], rule)
  also note calculation
  }
  hence "(\<Squnion> i. Y i) \<squnion> F (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x)) \<sqsubseteq> (\<Squnion> i. fix_on (S i) (\<lambda>x. Y i \<squnion> F x))"
    by simp
  ultimately
  show ?thesis
   by (rule fix_on_least_below[OF co' cl'])
qed

lemma fjc'_Inter:
  assumes "chain Y"
  shows "(\<Inter> i. (fix_join_compat' (Y i) F)) = fix_join_compat' (\<Squnion>i. Y i) F" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" by (auto intro: admD[OF compatible_adm1 `chain Y`])
next
  show "?R \<subseteq> ?L" by (auto elim: compatible_down_closed intro: is_ub_thelub[OF `chain Y`])
qed

lemma fix_on_join_cont'':
  assumes "chain Y"
  assumes "cont F"
  assumes F_pres_compat: "\<And> i x. compatible (Y i) x \<Longrightarrow> compatible (Y i) (F x)"

  shows "fix_on (fix_join_compat' (\<Squnion> i. Y i) F) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (fix_on (fix_join_compat' (Y i) F) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on ?S _ \<sqsubseteq> Lub ?F")
proof-
  have "fix_on (\<Inter> i. (fix_join_compat' (Y i) F)) (\<lambda> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (fix_on (fix_join_compat' (Y i) F) (\<lambda> x. Y i \<squnion> F x)))"
    (is "fix_on ?S _ \<sqsubseteq> Lub ?F")
  apply (rule fix_on_join_cont')
  apply (metis subpcpo_jfc' assms(2) assms(3))
  apply (metis down_closed_jfc' assms(2) assms(3))
  apply (metis subset_fjc'[OF chain_mono[OF `chain Y`]] le_add1 nat_add_commute)
  apply fact+
  apply (metis compatible_F_jfc' assms(2) assms(3))
  apply (metis closed_onI closed_jfc' assms(2) assms(3))
  done
  thus ?thesis unfolding fjc'_Inter[OF `chain Y`].
qed

end
