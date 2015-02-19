theory HSem
  imports "HeapToEnv" "AList-Utils-Nominal" "HOLCF-Fix-Join-Nominal" "FMap-Nominal-HOLCF" "HasESem" "FMap-Join"
begin

lemma fdom_fix_join_compat:
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_fjc fmap_below_dom subpcpo.bottom_of_minimal subpcpo_fjc to_bot_minimal)

subsubsection {* A locale for heap semantics, abstract in the expression semantics *}

text {*
The following theory about the semantics of a heap is abstract in the type and
semantics of expressions. Also, care is taken that lemmas required to prove
continuity of the heap semantics are provideded before requiring full
continuity of the expression semantics, to allow for a mutually recursive
proof.
*}

context has_ESem
begin

text {*
This definition captures the notion of compatible heaps and environments, i.e.\ those heaps where,
in the course of calculating the semantics, all joins exist.
*}

abbreviation HSem_cond' :: "('var \<times> 'exp) list \<Rightarrow> 'var f\<rightharpoonup> 'value \<Rightarrow> bool"
  where "HSem_cond' h \<rho> \<equiv>
      fix_join_cond (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) 
                        (\<lambda> \<rho>' . heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"

text {*
The following definition is in fact just
\[
@{text "\<lbrace>h\<rbrace>\<rho> = \<rho>'. \<rho> \<squnion> heapToEnv h (\<lbrakk>-\<rbrakk>\<^bsub>\<rho>'\<^esub>)"}
\]
with additional book-keeping for domain of the map and the condition that all joins exist.
*}

definition HSem :: "('var \<times> 'exp) list \<Rightarrow> 'var f\<rightharpoonup> 'value \<Rightarrow> 'var f\<rightharpoonup> 'value"
  where
  "HSem h \<rho> =
    (if HSem_cond' h \<rho>
    then fix_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>' . heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>))
      (\<lambda> \<rho>'. \<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
    else (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>))"

abbreviation HSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"

abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

text {*
Given the predcondition hold, we can unfold the definition directly.
*}

lemma HSem_def': "HSem_cond' \<Gamma> \<rho> \<Longrightarrow>
  HSem \<Gamma> \<rho> = fix_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) (\<lambda>\<rho>'. heapToEnv \<Gamma> (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>))
           (\<lambda>\<rho>'. \<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub> \<squnion> heapToEnv \<Gamma> (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>)
 "
  unfolding  HSem_def
  by (subst if_P, auto)

subsubsection {* Continutiy of the heap semantics *}

lemma HSem_mono:
  assumes cond1: "HSem_cond' h \<rho>"
  assumes cond2: "HSem_cond' h \<rho>'"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  shows "HSem h \<rho> \<sqsubseteq> HSem h \<rho>'"
    unfolding HSem_def
    unfolding if_P[OF cond1] if_P[OF cond2]
    apply (rule fix_on_mono2[OF fix_on_cond_fjc[OF cond1] fix_on_cond_fjc[OF cond2]])
    apply (simp add: bottom_of_fjc to_bot_fmap_def fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`])
    apply (erule (1) join_mono[OF rho_F_compat_fjc[OF cond1] rho_F_compat_fjc[OF cond2]])
    apply (subst fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`], rule cont2monofunE[OF cont2cont_fmap_expand[OF cont_id] assms(3)])
    apply (subst fmap_below_dom[OF `\<rho> \<sqsubseteq> \<rho>'`], rule cont2monofunE[OF cont2cont_fmap_expand[OF cont_id]])
    apply (erule cont2monofunE[rotated])
    apply (intro cont2cont cont2cont_fmap_expand cont2cont_heapToEnv) 
    done

lemma HSem_cont'':
  assumes cond1: "HSem_cond' h (\<Squnion> i. Y i)"
  assumes cond2: "\<And>i. HSem_cond' h (Y i)"
  assumes "chain Y"
  shows "HSem h (\<Squnion> i. Y  i) = (\<Squnion> i. HSem h (Y i))"
proof-
  have fdoms[simp]:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 

  have "fix_on       (fix_join_compat (\<Squnion> i. Y i\<^bsub>[?d \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[?d \<union> heapVars h]\<^esub>))
             (\<lambda>\<rho>'.                     (\<Squnion> i. Y i\<^bsub>[?d \<union> heapVars h]\<^esub>) \<squnion>
                      heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[?d \<union> heapVars h]\<^esub>) =
       (\<Squnion> i. fix_on  (fix_join_compat      (Y i\<^bsub>[?d \<union> heapVars h]\<^esub>)  (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot>  \<rho>')\<^bsub>[?d \<union> heapVars h]\<^esub>))
                                        (\<lambda>\<rho>'. Y i\<^bsub>[?d \<union> heapVars h]\<^esub> \<squnion>
                      heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[?d \<union> heapVars h]\<^esub>)) "
    by (rule fix_on_join_cont[OF 
          ch2ch_cont[OF fmap_expand_cont `chain Y`]
          cond2[unfolded fdoms]
          cond1[unfolded cont2contlubE[OF fmap_expand_cont `chain Y`]]
          ])
  thus ?thesis
    unfolding HSem_def
    unfolding if_P[OF cond1] if_P[OF cond2]
    by (simp add: cont2contlubE[OF fmap_expand_cont `chain Y`])
qed

subsubsection {* Disjoint heaps and environments are compatible *}

lemma disjoint_is_HSem_cond:
  "fdom \<rho> \<inter> heapVars h = {} \<Longrightarrow> HSem_cond' h \<rho>"
  apply (rule fix_join_condI)
  apply (intro cont2cont cont2cont_fmap_expand[OF cont2cont_heapToEnv])
  apply (rule compatible_fmapI)
  apply (case_tac "x \<in> fdom \<rho>")
  apply simp
  apply (subst lookup_fmap_expand2)
  apply auto
  done

subsubsection {* Inductions over the heap semantics *}

lemma HSem_ind':
  assumes "HSem_cond' h \<rho>"
  assumes "adm_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)) P"
  assumes "P (to_bot (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>))"
  assumes "\<And> y. y \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) \<Longrightarrow>
        P y \<Longrightarrow>
        P (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem e \<cdot> y)\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
  shows "P (HSem h \<rho>)"
  unfolding HSem_def
  apply (subst if_P[OF assms(1)])
  apply (rule fix_on_fjc_ind[OF assms(1)])
  apply fact
  apply (simp add:bottom_of_fjc)
  apply fact
  apply fact
  done

lemma HSem_ind:
  assumes "HSem_cond' h \<rho> \<Longrightarrow> adm_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)) P"
  assumes "HSem_cond' h \<rho> \<Longrightarrow> P (to_bot (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>))"
  assumes "\<And> y. HSem_cond' h \<rho> \<Longrightarrow>
        y \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) \<Longrightarrow>
        P y \<Longrightarrow>
        P (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem e \<cdot> y)\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
  assumes "P (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
  shows "P (HSem h \<rho>)"
  apply (cases "HSem_cond' h \<rho>")
  apply (rule HSem_ind'[OF _ assms(1,2,3)], assumption+)
  unfolding HSem_def
  apply (subst if_not_P, assumption)
  apply (rule assms(4))
  done

lemma parallel_HSem_ind:
  assumes cond1: "HSem_cond' h \<rho>"
  assumes cond2: "HSem_cond' h2 \<rho>2"
  assumes "adm_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda>\<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
                  \<times> fix_join_compat (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) (\<lambda>\<rho>'. heapToEnv h2 (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>))
                 (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
  assumes "\<And>y z. y \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
               (\<lambda>\<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) \<Longrightarrow>
          z \<in> fix_join_compat (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)
               (\<lambda>\<rho>'. heapToEnv h2 (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) \<Longrightarrow>
          P y z \<Longrightarrow>
          P (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem e \<cdot> y)\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
           (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub> \<squnion> heapToEnv h2 (\<lambda>e. ESem e \<cdot> z)\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) "
  shows "P (HSem h \<rho>) (HSem h2 \<rho>2)"
  unfolding HSem_def if_P[OF cond1] if_P[OF cond2]
  apply (rule parallel_fix_on_ind[OF fix_on_cond_fjc[OF cond1] fix_on_cond_fjc[OF cond2]])
  apply (rule assms(3))
  using assms(4) apply (simp add: bottom_of_fjc to_bot_fmap_def)
  by (rule assms(5))


lemma HSem_eq:
  assumes "HSem_cond' h \<rho>"
  shows "HSem h \<rho> = \<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem e \<cdot> (HSem h \<rho>))\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>"
  unfolding HSem_def
  using assms
  apply (simp)
  apply (erule fix_on_fjc_eq)
  done

lemma HSem_there:
  assumes "HSem_cond' h \<rho>"
  shows "HSem h \<rho> \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
  unfolding HSem_def
  apply (subst if_P[OF assms])
  apply (rule fix_on_there[OF fix_on_cond_fjc[OF assms]])
  done

lemma the_lookup_HSem_other:
  assumes "y \<notin> heapVars h"
  shows "(HSem h \<rho>) f! y = \<rho> f! y"
proof(cases "HSem_cond' h \<rho>")
  case True show ?thesis
    apply (subst HSem_eq[OF True])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF True HSem_there[OF True]]])
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms lookup_not_fdom)
    done
next
  case False show ?thesis
    unfolding HSem_def if_not_P[OF False]
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms  False lookup_not_fdom)
    done
qed

lemma fmap_lookup_bot_HSem_other:
  assumes "y \<notin> heapVars h"
  shows "(HSem h \<rho>) f!\<^sub>\<bottom> y = \<rho> f!\<^sub>\<bottom> y"
proof(cases "HSem_cond' h \<rho>")
  case True show ?thesis
    apply (subst HSem_eq[OF True])
    apply (subst fmap_lookup_bot_join[OF rho_F_compat_fjc[OF True HSem_there[OF True]]])
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms lookup_not_fdom)
    done
next
  case False show ?thesis
    unfolding HSem_def if_not_P[OF False]
    apply (cases "y \<in> fdom \<rho>")
    apply (auto simp add: assms  False lookup_not_fdom)
    done
qed


lemma the_lookup_HSem_both:
  assumes "HSem_cond' h \<rho>"
  assumes "y \<in> heapVars h"
  shows "HSem h \<rho> f! y =
    (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> f! y) \<squnion> ESem (the (map_of h y)) \<cdot> (HSem h \<rho>)"
  apply (subst HSem_eq[OF assms(1)])
  apply (subst the_lookup_join[OF rho_F_compat_fjc[OF assms(1) HSem_there[OF assms(1)]]])
  apply (subst (2) lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst lookupHeapToEnv[OF assms(2)])
  by (rule refl)

lemma the_lookup_HSem_both_compatible:
  assumes "HSem_cond' h \<rho>"
  assumes "y \<in> heapVars h"
  shows "compatible (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> f! y) (ESem (the (map_of h y)) \<cdot> (HSem h \<rho>))"
  using the_lookup_compatible[OF rho_F_compat_fjc[OF assms(1) HSem_there[OF assms(1)]], of y]
  apply (subst (asm) (2) lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst (asm) lookupHeapToEnv[OF assms(2)])
  .

lemma the_lookup_HSem_heap:
  assumes "HSem_cond' h \<rho>"
  assumes "y \<in> heapVars h"
  assumes "y \<notin> fdom \<rho>"
  shows "(HSem h \<rho>) f! y = ESem (the (map_of h y)) \<cdot> (HSem h \<rho>)"
  apply (subst HSem_eq[OF assms(1)])
  apply (subst the_lookup_join[OF rho_F_compat_fjc[OF assms(1) HSem_there[OF assms(1)]]])
  apply (subst lookup_fmap_expand2)
    using assms(2,3) apply auto[3]
  apply (subst lookup_fmap_expand1)
    using assms(2) apply auto[3]
  apply (subst lookupHeapToEnv[OF assms(2)])
  by (simp)

lemma HSem_refines:
  assumes "HSem_cond' h \<rho>"
  shows "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<sqsubseteq> HSem h \<rho>"
  apply (subst HSem_eq[OF assms(1)])
  apply (rule join_above1[OF rho_F_compat_fjc[OF assms HSem_there[OF assms]]])
done

lemma HSem_compatible[simp]:
  "compatible (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) (HSem \<Gamma> \<rho>)"
  apply (cases "HSem_cond' \<Gamma> \<rho>")
  apply (drule HSem_refines)
  apply (metis below.r_refl ub_implies_compatible)
  unfolding HSem_def
  apply simp
  done
  
lemma fdom_HSem[simp]:
  "fdom (HSem h \<rho>) = fdom \<rho> \<union> heapVars h"
  apply (rule HSem_ind)
  apply (rule adm_is_adm_on)
  apply simp
  apply simp
  apply (subst fdom_join)

  apply (rule compat_fjc)
  apply (erule rho_fjc)
  apply (erule (1) F_pres_compat'')
  apply simp+
  done


lemma HSem_cond'_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ; (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem e = ESem e) \<rbrakk>
      \<Longrightarrow>  HSem_cond' heap1 env1 \<longleftrightarrow> HSem_cond'  heap2 env2"
  by (auto cong:heapToEnv_cong)

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ; (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem e = ESem e) \<rbrakk>
      \<Longrightarrow> HSem heap1 env1 = HSem heap2 env2"
  unfolding HSem_def
  by (auto cong:heapToEnv_cong)


lemma fjc'_of_member:
  assumes "fix_join_cond \<rho> F"
  assumes "\<rho>' \<in> fix_join_compat \<rho> F" (is "_ \<in> ?S")
  assumes "to_bot \<rho> = to_bot \<rho>'"
  shows "fix_join_cond \<rho>' F"
proof (rule fix_join_condI)
case goal1
  have "cont F" by (rule cont_F_fjc[OF assms(1)])
  thus ?case by simp
case (goal2 i)
  show ?case
  apply (rule compat_fjc[OF assms(2) F_pres_compat''[OF assms(1)]])

  apply (induct_tac i)
  apply (simp only: funpow.simps id_apply fjc_iff)
  apply (rule to_bot_belowI)
  apply (simp add: assms(3))

  apply (simp only: funpow.simps o_apply id_apply)
  apply (erule join_fjc[OF assms(2) F_pres_compat''[OF assms(1)]])
  done
qed

lemma fjc'_of_fun_below:
  fixes \<rho> :: "'a\<Colon>{Bounded_Nonempty_Meet_cpo,subpcpo_partition}"
  assumes "fix_join_cond \<rho> F"
  assumes "G \<sqsubseteq> F"
  assumes "cont G"
  shows "fix_join_cond \<rho> G"
  apply (rule fix_join_condI[OF assms(3)])
  apply (rule compat_fjc[OF rho_fjc[OF assms(1)]])
  apply (rule down_closed_fjc[OF _ fun_belowD[OF assms(2)]])
  apply (rule F_pres_compat''[OF assms(1)])
  
  apply (induct_tac i)
  apply (simp only: funpow.simps id_apply fjc_iff)
  apply (rule to_bot_belowI)
  apply (simp add: assms(3))

  apply (simp only: funpow.simps o_apply id_apply)
  apply (rule join_fjc[OF rho_fjc[OF assms(1)]])
  apply (rule down_closed_fjc[OF _ fun_belowD[OF assms(2)]])
  apply (erule F_pres_compat''[OF assms(1)])
  done

lemma HSem_cond'_of_member:
  assumes "HSem_cond' \<Gamma> \<rho>"
  assumes "\<rho>' \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>)
                (\<lambda> \<rho>'.  heapToEnv \<Gamma> (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>)" (is "_ \<in> ?S")
  shows "HSem_cond' \<Gamma>  \<rho>'"
proof-
  let "fix_join_compat (\<rho>\<^bsub>[?d]\<^esub>) ?F" = "?S"
  have "fdom \<rho>' = ?d"
    using fdom_fix_join_compat[OF fix_on_cond_fjc[OF assms(1)] assms(2)]
    by auto
  have fdom[simp]:"fdom \<rho>' \<union> heapVars \<Gamma> = ?d"
    using fdom_fix_join_compat[OF fix_on_cond_fjc[OF assms(1)] assms(2)]
    by auto
  show ?thesis
    apply (rule fjc'_of_member)
    apply (rule assms(1)[unfolded fdom[symmetric]])
    apply (subst fmap_expand_noop)
    apply (metis `fdom \<rho>' = fdom \<rho> \<union> heapVars \<Gamma>` `fdom \<rho>' \<union> heapVars \<Gamma> =fdom \<rho> \<union> heapVars \<Gamma>`)
    apply (rule assms(2)[unfolded fdom[symmetric]])
    apply (simp add:to_bot_fmap_def)
    done
qed

subsubsection {* Reordering lemmas for HSem *}

lemma HSem_reorder:
  assumes "map_of \<Gamma> = map_of \<Delta>"
  shows "HSem \<Gamma> \<rho> = HSem \<Delta> \<rho>"
by (simp add: HSem_def heapToEnv_reorder[OF assms] assms dom_map_of_conv_heapVars[symmetric])

lemma HSem_reorder_head:
  assumes "x \<noteq> y"
  shows "HSem ((x,e1)#(y,e2)#\<Gamma>) \<rho> = HSem ((y,e2)#(x,e1)#\<Gamma>) \<rho>"
proof-
  have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
    by auto
  thus ?thesis      
    unfolding HSem_def heapToEnv_reorder_head[OF assms]
    by (simp add: heapVars_def)
qed

lemma HSem_reorder_head_append:
  assumes "x \<notin> heapVars \<Gamma>"
  shows "HSem ((x,e)#\<Gamma>@\<Delta>) \<rho> = HSem (\<Gamma> @ ((x,e)#\<Delta>)) \<rho>"
proof-
  have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
  thus ?thesis
    unfolding HSem_def heapToEnv_reorder_head_append[OF assms]
    by simp
qed  

subsubsection {* Substitution *}

lemma HSem_subst_exp:
  assumes cond1: "HSem_cond' ((x, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, e') # \<Gamma>) \<rho>"
  assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (heapVars ((x,e)#\<Gamma>)) \<Longrightarrow> ESem e \<cdot> \<rho>' = ESem e' \<cdot> \<rho>'"
  shows "HSem ((x,e)#\<Gamma>) \<rho> = HSem ((x,e')#\<Gamma>) \<rho>"
  apply (rule parallel_HSem_ind[OF cond1 cond2])
  apply (auto intro: adm_is_adm_on)[1]
  apply simp
  apply (subst heapToEnv_subst_exp)
  apply (rule assms(3))
  apply (drule fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond1]])
  apply simp
  apply simp
  done

subsubsection {* Refinement relations *}

lemma HSem_refines_lookup: "HSem_cond' \<Gamma> \<rho> \<Longrightarrow> x \<in> fdom \<rho> \<Longrightarrow> \<rho> f! x \<sqsubseteq> (HSem \<Gamma> \<rho>) f! x"
  apply (drule HSem_refines)
  apply (drule fmap_belowE[of _ _ x])
  apply simp
  done

lemma HSem_heap_below: "HSem_cond' \<Gamma> \<rho> \<Longrightarrow> x \<in> heapVars \<Gamma> \<Longrightarrow> ESem (the (map_of \<Gamma> x)) \<cdot> (HSem \<Gamma> \<rho>) \<sqsubseteq> (HSem \<Gamma> \<rho>) f! x"
  apply (subst the_lookup_HSem_both, assumption+)
  apply (rule join_above2)
  apply (rule the_lookup_HSem_both_compatible, assumption+)
  done

lemma fmap_restr_HSem_noop:
  assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  shows "fmap_restr (fdom \<rho>) (HSem \<Gamma> \<rho>) = \<rho>"
  apply (rule fmap_eqI)
  using assms apply auto[1]
  using assms apply auto[1]
  apply (subst the_lookup_HSem_other)
  apply auto
  done

lemma HSem_disjoint_less:
  assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  shows "\<rho> \<le> HSem \<Gamma> \<rho>"
  using assms
by (metis fmap_less_restrict fmap_restr_HSem_noop)
end

subsubsection {* Requiring continuity of the expression semantics *}

text {*
The lemmas above ought to be sufficient to prove continuity of the expression semantics. Hence, we
extend the locale by assuming this for alle expressions, and repeat some of the lemmas above, discharing
their more specific assumptions.
*}

context has_ESem
begin
  lemma HSem_below:
    assumes "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<sqsubseteq> r"
    assumes "\<And>x. x \<in> heapVars h \<Longrightarrow> ESem (the (map_of h x)) \<cdot> r \<sqsubseteq> r f! x"
    shows "HSem h \<rho> \<sqsubseteq> r"
  proof (rule HSem_ind)
    from fmap_below_dom[OF assms(1)]
    have [simp]:"fdom r = fdom \<rho> \<union> heapVars h" by simp
    {
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      show ?case
      apply (rule join_below[OF rho_F_compat_fjc[OF goal3(1) goal3(2)] assms(1)])
      apply (rule fmap_expand_belowI)
      apply simp
      apply (simp add: lookupHeapToEnv)
      by (rule below_trans[OF
            monofun_cfun_arg[OF goal3(3)]
            assms(2)])
    next
    case goal4 show ?case by fact
    }
  qed  

  lemma fempty_is_HSem_cond:
    "HSem_cond' h fempty"
      by (rule disjoint_is_HSem_cond, auto)

  lemma HSem_cond'_Nil[simp]:
    "HSem_cond' [] \<rho>"
    by (rule disjoint_is_HSem_cond, simp)
  
  lemma HSem_Nil[simp]: "HSem [] \<rho> = \<rho>"
    apply (subst HSem_eq[OF HSem_cond'_Nil])
    apply auto
    by (metis below.r_refl is_joinI to_bot_fmap_def to_bot_minimal)

subsubsection {* Re-calculating the semantics of the heap is idempotent *} 

  lemma HSem_redo:
    assumes "HSem_cond' (\<Gamma> @ \<Delta>) \<rho>"
    assumes "HSem_cond' \<Gamma> (fmap_restr (fdom \<rho> \<union> heapVars \<Delta>) (HSem (\<Gamma> @ \<Delta>) \<rho>))"
    shows "HSem \<Gamma> (fmap_restr (fdom \<rho> \<union> heapVars \<Delta>) (HSem (\<Gamma>@\<Delta>) \<rho>)) = HSem (\<Gamma> @ \<Delta>) \<rho>" (is "?LHS = ?RHS")
  proof (rule below_antisym)
    show "?LHS \<sqsubseteq> ?RHS"
    proof(rule HSem_below)
    case goal1
      show ?case
        apply (rule fmap_expand_fmap_restr_below)
        apply auto
        done
    case (goal2 x)
      hence "x \<in> heapVars (\<Gamma>@\<Delta>)" by auto
      show ?case
        apply (subst the_lookup_HSem_both[OF assms(1) `x \<in> heapVars (\<Gamma>@\<Delta>)`])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(1) `x \<in> heapVars (\<Gamma>@\<Delta>)`]]])
        using goal2 by (auto simp add: map_add_dom_app_simps dom_map_of_conv_image_fst dom_map_of_conv_heapVars[symmetric])
    qed
  
    show "?RHS \<sqsubseteq> ?LHS"
    proof(rule HSem_below)
    case goal1
      show ?case
        apply (rule fmap_expand_belowI)
          apply auto[1]
        apply (rule below_trans[OF _ HSem_refines_lookup[OF assms(2)]])
          prefer 2 apply simp
        apply (subst lookup_fmap_restr)
          apply auto[2]
        apply (erule HSem_refines_lookup[OF assms(1)])
        done
  
    case (goal2 x)
      show ?case
      proof(cases "x \<in> heapVars \<Gamma>")
      case True
        show ?thesis
          apply (subst the_lookup_HSem_both[OF assms(2) True])
          apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(2) True]]])
          using True by (auto simp add: map_add_dom_app_simps dom_map_of_conv_image_fst dom_map_of_conv_heapVars[symmetric])
      next
      case False
        hence delta: "x \<in> heapVars \<Delta>" using goal2 by auto
        show ?thesis
          apply (subst the_lookup_HSem_other[OF False])
          apply (subst lookup_fmap_restr)
            using delta apply auto[1]
          apply (subst the_lookup_HSem_both[OF assms(1) goal2])
          apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(1) `x \<in> heapVars (\<Gamma>@\<Delta>)`]]])
          apply (rule monofun_cfun_arg[OF `?LHS \<sqsubseteq> ?RHS`])
          done
      qed
    qed
  qed

subsubsection {* The heap semantics can also be defined inductively over the heap *}  

  lemma iterative_HSem:
    assumes "HSem_cond' ((x, e) # \<Gamma>) \<rho>"
    assumes "x \<notin> heapVars \<Gamma>"
    shows "HSem ((x,e) # \<Gamma>) \<rho> =
        fix_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>) (\<lambda> \<rho>'. heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>))
                (\<lambda> \<rho>'. (HSem \<Gamma> \<rho>')
                        \<squnion> ((f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)(x f\<mapsto> ESem e \<cdot> \<rho>') 
                        \<squnion> (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)))" (is "_ = fix_on ?S ?R")
  apply (subst HSem_def'[OF assms(1)])
  proof(rule below_antisym)
    interpret subpcpo ?S by (rule subpcpo_fjc)
  
    let "?d" = "fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"
  
    let "fix_on _ ?L" = "fix_on ?S
                         (\<lambda>\<rho>'. \<rho>\<^bsub>[?d]\<^esub> \<squnion>
                               heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)"
    let "(\<lambda> \<rho>'. ?L1 \<rho>' \<squnion> ?L2 \<rho>')" = ?L
    let "(\<lambda> \<rho>'. ?R1 \<rho>' \<squnion> (?R2 \<rho>' \<squnion> ?R3 \<rho>'))" = ?R
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      hence fdom1: "fdom \<rho>' = ?d"
      apply (subst (asm) fjc_iff)
      apply (drule fmap_below_dom)
      apply (subst (asm) fdom_fix_on[OF fix_on_cond_fjc[OF assms(1)], unfolded bottom_of_fjc])
      apply auto
      done
    } note fdom = this
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      have fdom1: "(fdom \<rho>' \<union> heapVars \<Gamma>) = ?d" using fdom[OF `\<rho>' \<in> ?S`] by auto
      have fdom2: "(fdom \<rho>' \<union> heapVars ((x,e) # \<Gamma>)) = ?d" using fdom1 by auto
      have "HSem_cond' ((x,e) # \<Gamma>) \<rho>'" by (rule HSem_cond'_of_member[OF assms(1) `\<rho>'\<in>?S`])
      from this[unfolded fdom2]
      have "HSem_cond' \<Gamma> \<rho>'"
        apply (subst (1 2) fdom1, rule fjc'_of_fun_below)
        apply (rule fun_belowI)
        apply (rule heapToEnv_mono)
        apply simp
        apply rule
        apply (simp add: assms(2))
        apply (intro cont2cont cont2cont_fmap_expand cont2cont_heapToEnv)
        done
    } note HSem_cond'_Gamma = this
  
    have closedL: "closed_on ?L"
      by (rule closed_on_fjc[OF assms(1)])
  
    have closedR1: "closed_on ?R1"
      apply (rule closed_onI)
         apply (rule HSem_ind)
        apply (rule adm_is_adm_on[OF subcpo_mem_adm[OF subcpo_fjc]])
        apply (rule down_closed_fjc, assumption)
        apply (frule fdom)
       apply (auto simp add:to_bot_fmap_def simp del:fjc_iff)[1]
        apply (rule join_fjc)
         apply (subst fmap_expand_noop)
        apply (frule fdom, auto)[1]
       apply assumption
       apply (rule down_closed_fjc[OF F_pres_compat''[OF assms(1)]], assumption) back
         apply (rule heapToEnv_mono)
        apply simp
       apply (frule fdom, auto)[1]
      apply (simp add: assms(2))
      apply (subst fmap_expand_noop)
       apply (frule fdom, auto)[1]
      apply assumption
      done
      
    have closedR2: "closed_on ?R2"
      apply (rule closed_onI)
      apply (rule down_closed_fjc[OF F_pres_compat''[OF assms(1)]], assumption)
      apply (rule fmap_belowI)
      apply (frule fdom, auto)[1]
      apply (case_tac "xaa = x", simp_all)
      done    
      
    have closedR3: "closed_on ?R3"
      apply (rule closed_onI)
      by (rule rho_fjc[OF assms(1)])
  
    have closedR: "closed_on ?R"
      by (rule closed_on_join_fjc[OF closedR1 closed_on_join_fjc[OF closedR2 closedR3]])
  
    have contL: "cont_on ?L"
      by (rule cont_on_fjc[OF assms(1)])
      
    have contR1: "cont_on ?R1"
      apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (2) HSem_mono[OF HSem_cond'_Gamma HSem_cond'_Gamma])
      apply (rule eq_imp_below[OF HSem_cont''])
      apply (erule HSem_cond'_Gamma[OF chain_on_lub_on])
      apply (erule HSem_cond'_Gamma[OF chain_on_is_on])
      apply (erule chain_on_is_chain)
      done
  
    have contR2: "cont_on ?R2"
      by (intro cont_is_cont_on fmap_upd_cont cont_const cont2cont)
  
    have contR3: "cont_on ?R3"
      by (rule cont_is_cont_on[OF cont_const])
  
    have contR: "cont_on ?R"
      apply (rule cont_on_join_fjc)
      apply (rule closedR1)
      apply (rule closed_on_join_fjc[OF closedR2 closedR3])
      apply (rule contR1)
      apply (rule cont_on_join_fjc)
      apply (rule closedR2)
      apply (rule closedR3)
      apply (rule contR2)
      apply (rule contR3)
      done
  
    note fix_on_condL = fix_on_cond_fjc[OF assms(1)]
  
    have fix_on_condR: "fix_on_cond ?S bottom_of ?R"
      by (rule fix_on_condI[OF subpcpo_fjc refl closedR contR])
  
    have R_there: "fix_on ?S ?R \<in> ?S"
      by (rule fix_on_there[OF fix_on_condR])
  
      
    have compatL: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?L1 x) (?L2 x)"
      by (rule compat_fjc[OF rho_fjc[OF assms(1)]  F_pres_compat''[OF assms(1)]])
      
    have compatR2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R2 x) (?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR2] closed_onE[OF closedR3]])
    have compatR1R2: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR1] closed_onE[OF closedR2]])
    have compatR1R2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x \<squnion> ?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR1] closed_onE[OF closed_on_join_fjc[OF closedR2 closedR3]]])
    have compatR1R2R3': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x \<squnion> ?R2 x) (?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closed_on_join_fjc[OF closedR1 closedR2]] closed_onE[OF closedR3]])
  
    show "fix_on ?S ?L \<sqsubseteq> fix_on ?S ?R"
    proof (rule fix_on_mono[OF fix_on_condL fix_on_condR])
      fix \<rho>'
      assume there: "\<rho>' \<in> ?S"
      hence [simp]:"fdom \<rho>' = ?d" by (rule fdom)
  
      have inner_cond: "HSem_cond' \<Gamma> \<rho>'"
        by (rule HSem_cond'_Gamma[OF there])
      have inner_refine: "\<rho>' \<sqsubseteq> HSem \<Gamma> \<rho>'"
        apply (insert HSem_refines[OF inner_cond])
        apply (subst (asm) fmap_expand_noop)
        apply auto
        done
  
      have belowL1: "?L1 \<rho>' \<sqsubseteq> ?R \<rho>'"
        by (rule below_trans[OF join_above2[OF compatR2R3[OF there]] join_above2[OF compatR1R2R3[OF there]]])
  
      have "?L2 \<rho>' \<sqsubseteq> ?R1 \<rho>' \<squnion> ?R2 \<rho>'"
      proof (rule fmap_belowI)
      case goal1 show ?case
        by (subst fdom_join[OF compatR1R2[OF there]], auto)
      case (goal2 x')
        hence "x' \<in> ?d" by simp
        show ?case
        proof(cases "x' = x")
        case True
          show ?thesis
            apply (subst the_lookup_join[OF compatR1R2[OF there]])
            apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
            apply (simp add: True)
            apply (erule join_above2)
            done
        next
        case False
          show ?thesis
          proof (cases "x' \<in> heapVars \<Gamma>")
          case True
            have "heapToEnv \<Gamma> (\<lambda>e. ESem e \<cdot> \<rho>') f! x' \<sqsubseteq> HSem \<Gamma> \<rho>' f! x'"
              apply (subst HSem_eq[OF inner_cond])
              apply (subst the_lookup_join[OF rho_F_compat_fjc[OF inner_cond  HSem_there[OF inner_cond]]])
              apply (insert the_lookup_compatible[OF rho_F_compat_fjc[OF inner_cond  HSem_there[OF inner_cond]], of x'])
              apply (subst (2) lookup_fmap_expand1)
              apply (simp_all add: True)[3]
              apply (subst (asm) (2) lookup_fmap_expand1)
              apply (simp_all add: True)[3]
              apply (erule below_trans[OF _ join_above2, rotated])
              apply (rule cont2monofunE[OF _ inner_refine])
              apply (intro cont2cont)
              done
            thus ?thesis
              apply (subst lookup_fmap_expand1)
              apply simp
              apply (simp add: True)
              apply (simp add: True)
              apply (subst the_lookup_join[OF compatR1R2[OF there]])
              apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
              apply (simp add: True False)
              done
          next
          case False
            show ?thesis
            apply (subst lookup_fmap_expand2)
            apply simp
            apply fact
            apply (simp add: False `x' \<noteq> x`)
            apply simp
            done
          qed
        qed
      qed
      hence belowL2: "?L2 \<rho>' \<sqsubseteq> ?R \<rho>'"
        apply (subst join_assoc[symmetric, OF compatR1R2[OF there] compatR1R2R3[OF there] compatR2R3[OF there]])
        apply (erule below_trans[OF _ join_above1[OF compatR1R2R3'[OF there]]])
        done
  
      show "?L \<rho>' \<sqsubseteq> ?R \<rho>'"
        apply (rule join_below[OF compatL[OF there]])
        apply (rule belowL1)
        apply (rule belowL2)
        done
    qed
  
    show "fix_on ?S ?R \<sqsubseteq> fix_on ?S ?L"
      unfolding bottom_of_fjc
      by (rule R_there[unfolded fjc_iff, unfolded bottom_of_fjc])
  qed

  (*  
  lemma iterative_HSem':
    assumes "HSem_cond' ((x, e) # \<Gamma>) \<rho>"
    assumes "x \<notin> heapVars \<Gamma>"
    shows "HSem ((x,e) # \<Gamma>) \<rho> =
        fix_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>) (\<lambda> \<rho>'. heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>))
                (\<lambda> \<rho>'. (HSem \<Gamma> (\<rho>' f|` (-heapVars \<Gamma>)))
                        \<squnion> ((f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)(x f\<mapsto> ESem e (HSem \<Gamma> (\<rho>' f|` (-heapVars \<Gamma>)))) 
                        \<squnion> (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)))" (is "_ = fix_on ?S ?R")
  apply (subst HSem_def'[OF assms(1)])
  proof(rule below_antisym)
    interpret subpcpo ?S by (rule subpcpo_fjc)
  
    let "?d" = "fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"

    have [simp]: "\<And> \<rho>. fdom (\<rho> f|` (- heapVars \<Gamma>)) \<union> heapVars \<Gamma> = fdom \<rho> \<union> heapVars \<Gamma>"
      by auto
    have [simp]: "insert x (fdom \<rho> \<union> heapVars \<Gamma>) \<inter> - heapVars \<Gamma> \<union> heapVars \<Gamma> =  insert x (fdom \<rho> \<union> heapVars \<Gamma>)"
      by auto
  
    let "fix_on _ ?L" = "fix_on ?S
                         (\<lambda>\<rho>'. \<rho>\<^bsub>[?d]\<^esub> \<squnion>
                               heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)"
    let "(\<lambda> \<rho>'. ?L1 \<rho>' \<squnion> ?L2 \<rho>')" = ?L
    let "(\<lambda> \<rho>'. ?R1 \<rho>' \<squnion> (?R2 \<rho>' \<squnion> ?R3 \<rho>'))" = ?R
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      hence fdom1: "fdom \<rho>' = ?d"
      apply (subst (asm) fjc_iff)
      apply (drule fmap_below_dom)
      apply (subst (asm) fdom_fix_on[OF fix_on_cond_fjc[OF assms(1)], unfolded bottom_of_fjc])
      apply auto
      done
    } note fdom = this
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      have fdom1: "(fdom \<rho>' \<union> heapVars \<Gamma>) = ?d" using fdom[OF `\<rho>' \<in> ?S`] by auto
      have fdom2: "(fdom \<rho>' \<union> heapVars ((x,e) # \<Gamma>)) = ?d" using fdom1 by auto
      have "HSem_cond' ((x,e) # \<Gamma>) \<rho>'" by (rule HSem_cond'_of_member[OF assms(1) `\<rho>'\<in>?S`])
      from this[unfolded fdom2]
      have "HSem_cond' \<Gamma> \<rho>'"
        apply (subst (1 2) fdom1, rule fjc'_of_fun_below)
        apply (rule fun_belowI)
        apply (rule heapToEnv_mono)
        apply simp
        apply rule
        apply (simp add: assms(2))
        apply (rule cont2cont_fmap_expand[OF  cont2cont_heapToEnv[OF ESem_cont]])
        done
    } note HSem_cond'_Gamma = this
  
    have closedL: "closed_on ?L"
      by (rule closed_on_fjc[OF assms(1)])
  
    have closedR1: "closed_on ?R1"
      apply (rule closed_onI)
         apply (rule HSem_ind)
        apply (rule adm_is_adm_on[OF subcpo_mem_adm[OF subcpo_fjc]])
        apply (rule down_closed_fjc, assumption)
        apply (frule fdom)
       apply (auto simp add:to_bot_fmap_def simp del:fjc_iff)[1]
        apply (rule join_fjc)
        apply (frule fdom)
        apply (erule down_closed_fjc)
       apply (auto intro: fmap_expand_fmap_restr_below)[1]
       apply (rule down_closed_fjc[OF F_pres_compat''[OF assms(1)]], assumption) back
         apply (rule heapToEnv_mono)
        apply simp
       apply (frule fdom, auto)[1]
      apply (simp add: assms(2))
      apply (frule fdom)
      apply (erule down_closed_fjc)
      apply (auto intro: fmap_expand_fmap_restr_below)[1]
      done
      
    have closedR2: "closed_on ?R2"
      apply (rule closed_onI)
      apply (rule down_closed_fjc[OF F_pres_compat''[OF assms(1)]], assumption)
      apply (rule fmap_belowI)
      apply (frule fdom, auto)[1]
      apply (case_tac "xaa = x", simp_all)
      done    
      
    have closedR3: "closed_on ?R3"
      apply (rule closed_onI)
      by (rule rho_fjc[OF assms(1)])
  
    have closedR: "closed_on ?R"
      by (rule closed_on_join_fjc[OF closedR1 closed_on_join_fjc[OF closedR2 closedR3]])
  
    have contL: "cont_on ?L"
      by (rule cont_on_fjc[OF assms(1)])
      
    have contR1: "cont_on ?R1"
      apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (2) HSem_monofun''[OF ESem_cont HSem_cond'_Gamma HSem_cond'_Gamma])
      apply (rule eq_imp_below[OF HSem_cont''[OF ESem_cont]])
      apply (erule HSem_cond'_Gamma[OF chain_on_lub_on])
      apply (erule HSem_cond'_Gamma[OF chain_on_is_on])
      apply (erule chain_on_is_chain)
      done
  
    have contR2: "cont_on ?R2"
      by (rule cont_is_cont_on[OF fmap_upd_cont[OF cont_const ESem_cont]])
  
    have contR3: "cont_on ?R3"
      by (rule cont_is_cont_on[OF cont_const])
  
    have contR: "cont_on ?R"
      apply (rule cont_on_join_fjc)
      apply (rule closedR1)
      apply (rule closed_on_join_fjc[OF closedR2 closedR3])
      apply (rule contR1)
      apply (rule cont_on_join_fjc)
      apply (rule closedR2)
      apply (rule closedR3)
      apply (rule contR2)
      apply (rule contR3)
      done
  
    note fix_on_condL = fix_on_cond_fjc[OF assms(1)]
  
    have fix_on_condR: "fix_on_cond ?S bottom_of ?R"
      by (rule fix_on_condI[OF subpcpo_fjc refl closedR contR])
  
    have R_there: "fix_on ?S ?R \<in> ?S"
      by (rule fix_on_there[OF fix_on_condR])
  
      
    have compatL: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?L1 x) (?L2 x)"
      by (rule compat_fjc[OF rho_fjc[OF assms(1)]  F_pres_compat''[OF assms(1)]])
      
    have compatR2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R2 x) (?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR2] closed_onE[OF closedR3]])
    have compatR1R2: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR1] closed_onE[OF closedR2]])
    have compatR1R2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x \<squnion> ?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closedR1] closed_onE[OF closed_on_join_fjc[OF closedR2 closedR3]]])
    have compatR1R2R3': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x \<squnion> ?R2 x) (?R3 x)"
      by (rule compat_fjc[OF closed_onE[OF closed_on_join_fjc[OF closedR1 closedR2]] closed_onE[OF closedR3]])
  
    show "fix_on ?S ?L \<sqsubseteq> fix_on ?S ?R"
    proof (rule fix_on_mono[OF fix_on_condL fix_on_condR])
      fix \<rho>'
      assume there: "\<rho>' \<in> ?S"
      hence [simp]:"fdom \<rho>' = ?d" by (rule fdom)
  
      have inner_cond: "HSem_cond' \<Gamma> \<rho>'"
        by (rule HSem_cond'_Gamma[OF there])
      have inner_refine: "\<rho>' \<sqsubseteq> HSem \<Gamma> \<rho>'"
        apply (insert HSem_refines[OF inner_cond])
        apply (subst (asm) fmap_expand_noop)
        apply auto
        done
  
      have belowL1: "?L1 \<rho>' \<sqsubseteq> ?R \<rho>'"
        by (rule below_trans[OF join_above2[OF compatR2R3[OF there]] join_above2[OF compatR1R2R3[OF there]]])
  
      have "?L2 \<rho>' \<sqsubseteq> ?R1 \<rho>' \<squnion> ?R2 \<rho>'"
      proof (rule fmap_belowI)
      case goal1 show ?case
        by (subst fdom_join[OF compatR1R2[OF there]], auto)
      case (goal2 x')
        hence "x' \<in> ?d" by simp
        show ?case
        proof(cases "x' = x")
        case True
          show ?thesis
            apply (subst the_lookup_join[OF compatR1R2[OF there]])
            apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
            apply (simp add: True)
            apply (erule join_above2)
            done
        next
        case False
          show ?thesis
          proof (cases "x' \<in> heapVars \<Gamma>")
          case True
            have "heapToEnv \<Gamma> (\<lambda>e. ESem e \<rho>') f! x' \<sqsubseteq> HSem \<Gamma> \<rho>' f! x'"
              apply (subst HSem_eq[OF inner_cond])
              apply (subst the_lookup_join[OF rho_F_compat_fjc[OF inner_cond  HSem_there[OF inner_cond]]])
              apply (insert the_lookup_compatible[OF rho_F_compat_fjc[OF inner_cond  HSem_there[OF inner_cond]], of x'])
              apply (subst (2) lookup_fmap_expand1)
              apply (simp_all add: True)[3]
              apply (subst (asm) (2) lookup_fmap_expand1)
              apply (simp_all add: True)[3]
              apply (erule below_trans[OF _ join_above2, rotated])
              apply (rule cont2monofunE[OF _ inner_refine])
              apply (intro cont2cont ESem_cont)
              done
            thus ?thesis
              apply (subst lookup_fmap_expand1)
              apply simp
              apply (simp add: True)
              apply (simp add: True)
              apply (subst the_lookup_join[OF compatR1R2[OF there]])
              apply (insert the_lookup_compatible[OF compatR1R2[OF there], of x'])
              apply (simp add: True False)
              done
          next
          case False
            show ?thesis
            apply (subst lookup_fmap_expand2)
            apply simp
            apply fact
            apply (simp add: False `x' \<noteq> x`)
            apply simp
            done
          qed
        qed
      qed
      hence belowL2: "?L2 \<rho>' \<sqsubseteq> ?R \<rho>'"
        apply (subst join_assoc[symmetric, OF compatR1R2[OF there] compatR1R2R3[OF there] compatR2R3[OF there]])
        apply (erule below_trans[OF _ join_above1[OF compatR1R2R3'[OF there]]])
        done
  
      show "?L \<rho>' \<sqsubseteq> ?R \<rho>'"
        apply (rule join_below[OF compatL[OF there]])
        apply (rule belowL1)
        apply (rule belowL2)
        done
    qed
  
    show "fix_on ?S ?R \<sqsubseteq> fix_on ?S ?L"
      unfolding bottom_of_fjc
      by (rule R_there[unfolded fjc_iff, unfolded bottom_of_fjc])
  qed
  *)

  subsubsection {* Substitution *}
  
  lemma HSem_subst_expr_below:
    assumes cond1: "HSem_cond' ((x, e1) # \<Gamma>) \<rho>"
    assumes cond2: "HSem_cond' ((x, e2) # \<Gamma>) \<rho>"
    assumes below: "ESem e1 \<cdot> (HSem ((x, e2) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e2 \<cdot> (HSem ((x, e2) # \<Gamma>) \<rho>)"
    shows "HSem ((x, e1) # \<Gamma>) \<rho> \<sqsubseteq> HSem ((x, e2) # \<Gamma>) \<rho>"
  proof (rule HSem_ind'[OF cond1])
  case goal1 show ?case by (auto intro: adm_is_adm_on)
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
    show ?case
      apply (subst HSem_eq[OF cond2])
      apply (rule join_mono[OF
        rho_F_compat_fjc[OF cond1 goal3(1)]
        rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]
        ])
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (simp del: heapToEnv.simps)
      apply (rule cont2monofunE[OF fmap_expand_cont])
      apply (rule fmap_upd_mono)
      apply (rule cont2monofunE[OF _ goal3(2)])
        apply (intro cont2cont)
      apply (rule below_trans[OF monofun_cfun_arg[OF goal3(2)] below])
      done
  qed    
  
  lemma HSem_subst_expr:
    assumes cond1: "HSem_cond' ((x, e1) # \<Gamma>) \<rho>"
    assumes cond2: "HSem_cond' ((x, e2) # \<Gamma>) \<rho>"
    assumes below1: "ESem e1 \<cdot> (HSem ((x, e2) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e2 \<cdot> (HSem ((x, e2) # \<Gamma>) \<rho>)"
    assumes below2: "ESem e2 \<cdot> (HSem ((x, e1) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e1 \<cdot> (HSem ((x, e1) # \<Gamma>) \<rho>)"
    shows "HSem ((x, e1) # \<Gamma>) \<rho> = HSem ((x, e2) # \<Gamma>) \<rho>"
    by (metis assms HSem_subst_expr_below below_antisym)

  subsubsection {* Lemmas specialized to @{text "\<rho> = f\<emptyset>"} *}
  
  lemma HSemb_def: "HSem h f\<emptyset> = fix_on {y. fdom y = heapVars h} (\<lambda> \<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>'))"
    by (simp add: HSem_def'[OF fempty_is_HSem_cond] bottom_of_fjc to_bot_fmap_def)

  lemma fix_on_cond_fempty:
    "fix_on_cond {y. fdom y = heapVars h}
       (subpcpo_syn.bottom_of {y. fdom y = heapVars h})
       (\<lambda>\<rho>'. heapToEnv h (\<lambda>e. ESem e \<cdot> \<rho>'))"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above[where x = "f\<emptyset>\<^bsub>[heapVars h]\<^esub>", simplified])
    apply (rule refl)
    apply auto[1]
    apply (intro cont_is_cont_on cont2cont)
    done
  
  lemma HSemb_ind':
    assumes "adm_on ({y . fdom y = heapVars h}) P"
    assumes "P (f\<emptyset>\<^bsub>[heapVars h]\<^esub>)"
    assumes "\<And> y. fdom y = heapVars h \<Longrightarrow> P y \<Longrightarrow> P (heapToEnv h (\<lambda>e. ESem e \<cdot> y))"
    shows "P (HSem h f\<emptyset>)"
    apply (subst HSemb_def)
    apply (rule fix_on_ind[OF fix_on_cond_fempty assms(1)])
    using assms apply auto
    done

  lemma HSemb_redo:
    assumes "HSem_cond' \<Gamma> (fmap_restr (heapVars \<Delta>) (HSem (\<Gamma> @ \<Delta>) f\<emptyset>))"
    shows "HSem \<Gamma> (fmap_restr (heapVars \<Delta>) (HSem (\<Gamma>@\<Delta>) f\<emptyset>)) = HSem (\<Gamma> @ \<Delta>) f\<emptyset>"
    apply (rule HSem_redo[OF fempty_is_HSem_cond, simplified (no_asm)])
    using assms by simp

  lemma HSemb_eq:
    shows "HSem h f\<emptyset> = heapToEnv h (\<lambda>e. ESem e \<cdot> (HSem h f\<emptyset>))"
    by (subst HSem_eq[OF fempty_is_HSem_cond], simp)

  lemma HSemb_heap_below: "x \<in> heapVars \<Gamma> \<Longrightarrow> ESem (the (map_of \<Gamma> x)) \<cdot> (HSem \<Gamma> f\<emptyset>) \<sqsubseteq> (HSem \<Gamma> f\<emptyset>) f! x"
    by (erule HSem_heap_below[OF fempty_is_HSem_cond])

  lemma HSemb_below:
    assumes "heapToEnv h (\<lambda>e. ESem e \<cdot> r) \<sqsubseteq> r"
    shows "HSem h f\<emptyset> \<sqsubseteq> r"
    apply (subst HSemb_def)
    apply (rule fix_on_least_below[OF fix_on_cond_fempty _ assms])
    using assms by (metis (full_types) fmap_below_dom heapToEnv_fdom mem_Collect_eq)

  lemmas the_lookup_HSem_fempty = the_lookup_HSem_heap[OF fempty_is_HSem_cond, simp]

end

locale has_ignore_fresh_ESem = has_ESem +
  assumes ESem_ignores_fresh: "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> ESem e \<cdot> \<rho>1 = ESem e \<cdot> \<rho>2"
begin

subsubsection {* Binding more variables increases knowledge *}

  lemma HSem_subset_below:
    assumes cond2: "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* \<Delta>" 
    assumes rho_fresh: "fdom \<rho> \<inter> heapVars (\<Gamma> @ \<Delta>) = {}"
    shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
  proof-
    have fdoms: "fdom \<rho> \<union> (heapVars \<Delta> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
      using fresh rho_fresh by (auto dest: fresh_distinct)
    
    have below: "\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>" (is "_ \<sqsubseteq> ?RHS")
    proof (rule HSem_below)
      show "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub> \<sqsubseteq> ?RHS"
      proof (rule fmap_expand_belowI)
        fix x
        assume "x \<in> fdom \<rho>"
        with fmap_belowE[OF HSem_refines[OF cond2], where x = x]
        show "\<rho> f! x \<sqsubseteq> ?RHS f! x" by simp
      qed simp
    next
    case (goal2 x)[simp]
      have "ESem (the (map_of \<Delta> x)) \<cdot> ?RHS = ESem (the (map_of \<Delta> x)) \<cdot> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)"
        apply (rule ESem_ignores_fresh[OF fmap_expand_less])
        apply simp
        apply auto[1]
        apply (simp add: fdoms)
        using fresh apply (metis fresh fresh_heap_expr'[OF _ the_map_of_snd[OF goal2]] fresh_star_def)
        done
      also have "\<dots> = ESem (the (map_of (\<Delta>@\<Gamma>) x)) \<cdot> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)"
        by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      also have "\<dots> \<sqsubseteq> ?RHS f! x"
        by (simp, rule HSem_heap_below[OF cond2, where x = x, simplified])
      finally
      show ?case.
    qed
  
    show ?thesis
    proof(rule fmap_expand_belowI)
    case (goal2 x) 
      with fmap_belowE[OF below, where x = x]
      show ?case by (cases "x\<in> fdom \<rho>", auto)
    qed auto
  qed

  subsubsection {* Additional, fresh bindings in one or two steps *}  

  lemma HSem_merge:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* \<Delta>"
    assumes rho_fresh: "fdom \<rho> \<inter> heapVars (\<Gamma> @ \<Delta>) = {}"
    shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof(rule below_antisym)
    from fresh rho_fresh
    have Gamma_fresh: "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
      by (auto dest: fresh_distinct)
    hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
      by auto

    have map_of_eq: "map_of (\<Delta> @ \<Gamma>) = map_of (\<Gamma> @ \<Delta>)"
    proof
      fix x
      show "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
      proof (cases "x \<in> heapVars \<Gamma>")
        case True
        hence "x \<notin> heapVars \<Delta>" by (metis Gamma_fresh IntI equals0D in_mono sup_ge2)
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      next
        case False
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      qed
    qed
  
    have cond1: "HSem_cond' \<Gamma> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
      apply (rule disjoint_is_HSem_cond)
      using Gamma_fresh by auto
    have cond2: "HSem_cond' (\<Gamma>@\<Delta>) \<rho>"
      apply (rule disjoint_is_HSem_cond)
      using rho_fresh by auto
    have cond2': "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
      apply (rule disjoint_is_HSem_cond)
      using rho_fresh by auto
    have cond3: "HSem_cond' \<Delta> \<rho>"
      apply (rule disjoint_is_HSem_cond)
      using rho_fresh by auto
  
    show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
    proof(rule HSem_below)
      have "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>"
        by (rule HSem_subset_below[OF cond2' fresh rho_fresh])
      also have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
        by (rule HSem_reorder[OF map_of_eq])
      finally
      show "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
        by simp
      
    case (goal2 x)[simp]
      have "ESem (the (map_of \<Gamma> x)) \<cdot> (\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) = ESem (the (map_of (\<Gamma>@\<Delta>) x)) \<cdot> (\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>)"
        by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      also have "\<dots> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> f! x"
        by (rule HSem_heap_below[OF cond2], simp)
      finally
      show ?case.
    qed
  
    show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    proof(rule HSem_below)
      have "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> = (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
        by (rule fmap_expand_idem[symmetric], auto)
      also have "... \<sqsubseteq> (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
        by (rule cont2monofunE[OF fmap_expand_cont HSem_refines[OF cond3]])
      also have "... = (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars (\<Gamma>)]\<^esub>"
        apply (rule arg_cong) back
        by auto
      also have "... \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
        by (rule HSem_refines[OF cond1])
      finally
      show "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> ".
    
    case (goal2 x)
      {
        assume x[simp]: "x \<in> heapVars \<Gamma>"
        have "ESem (the (map_of (\<Gamma> @ \<Delta>) x)) \<cdot> (\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) = ESem (the (map_of (\<Gamma>) x)) \<cdot> (\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>)"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
        also have "\<dots> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
          by (rule HSem_heap_below[OF cond1 x])
        finally have ?case.
      }
      moreover
      {
        assume [simp]:"x \<notin> heapVars \<Gamma>" and  "x \<in> heapVars \<Delta>"
        have "ESem (the (map_of (\<Gamma> @ \<Delta>) x)) \<cdot> (\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) = ESem (the (map_of \<Delta> x)) \<cdot> (\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>)"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
        also have "\<dots>  = ESem (the (map_of \<Delta> x)) \<cdot> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
          apply (rule ESem_ignores_fresh[symmetric])
          apply (rule HSem_disjoint_less)
            using Gamma_fresh apply auto[1]
          apply (simp add: fdoms)
            using fresh apply (metis fresh fresh_heap_expr'[OF _ the_map_of_snd[OF `x \<in> heapVars \<Delta>`]] fresh_star_def)
          done
        also have "\<dots> \<sqsubseteq> \<lbrace>\<Delta>\<rbrace>\<rho> f! x"
          by (rule HSem_heap_below[OF cond3 `x \<in> heapVars \<Delta>`])
        also have "\<dots> = \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
          by (rule the_lookup_HSem_other[symmetric, OF `x \<notin> heapVars \<Gamma>`])
        finally have ?case.
      }
      ultimately show ?case using goal2 by fastforce
    qed
  qed

subsubsection {* Adding a fresh variable to a heap does not affect its semantics *} 

  lemma HSem_add_fresh':
    assumes cond1: "HSem_cond' \<Gamma> \<rho>"
    assumes cond2: "HSem_cond' ((x,e) # \<Gamma>) \<rho>"
    assumes fresh: "atom x \<sharp> (\<rho>,\<Gamma>)"
    assumes step: "\<And>e \<rho>'. fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>) \<Longrightarrow> e \<in> snd ` set \<Gamma> \<Longrightarrow> ESem e \<cdot> \<rho>' = ESem e\<cdot>  (fmap_restr (fdom \<rho>' - {x}) \<rho>')"
    shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (HSem ((x, e) # \<Gamma>) \<rho>) = HSem \<Gamma> \<rho>"
  proof (rule parallel_HSem_ind[OF cond1 cond2])
  case goal1 show ?case by (auto intro:adm_is_adm_on)
  case goal2 show ?case by (auto)[1]
  case goal3
    have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>) = \<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>"
      apply (subst fmap_restr_fmap_expand2)
      by auto
    moreover
  
    have "x \<notin> fdom \<rho> \<union> heapVars \<Gamma>"
      using fresh
      apply (auto simp add: fresh_fmap_pure fresh_Pair)
      by (metis heapVars_not_fresh)
    hence [simp]:"fdom z - {x} = fdom \<rho> \<union> heapVars \<Gamma>"
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond2] goal3(2)]
      by auto
  
    have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<cdot> z)\<^bsub>[fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)]\<^esub>)
      =  heapToEnv \<Gamma> (\<lambda>e. ESem e \<cdot> y)\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub> "
      apply (subst fmap_restr_fmap_expand2)
        apply simp
        apply auto[1]
      apply (subst heapToEnv_remove_Cons_fmap_expand[OF _ `x \<notin> fdom \<rho> \<union> heapVars \<Gamma>`])
        apply simp
      apply (rule arg_cong[OF heapToEnv_cong[OF refl]])
      apply (subst step)
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond2] goal3(2)] apply simp
      apply assumption
      using `_ = y`[symmetric]
      apply simp
      done
    ultimately
    show ?case
      apply (subst fmap_restr_join[OF _ rho_F_compat_fjc[OF cond2 `z \<in> _`]])
      by simp+
  qed

  lemma HSem_add_fresh:
    assumes cond1: "HSem_cond' \<Gamma> \<rho>"
    assumes cond2: "HSem_cond' ((x,e) # \<Gamma>) \<rho>"
    assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
    shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
  proof(rule HSem_add_fresh'[OF assms])
  case (goal1 e \<rho>')
    assume "e \<in> snd ` set \<Gamma>"
    hence "atom x \<sharp> e"
      apply auto
      by (metis fresh fresh_PairD(2) fresh_list_elem)
  
    assume "fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"
    hence [simp]:"fdom \<rho>' - fdom \<rho>' \<inter> (fdom \<rho>' - {x}) = {x}" by auto
  
    show ?case
      apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
      apply (simp add: fresh_star_def)
      using `atom x \<sharp> e`.
  qed

end

lemma parallel_HSem_ind_different_ESem:
  assumes cond1: "has_ESem.HSem_cond' ESem1 h \<rho>"
  assumes cond2: "has_ESem.HSem_cond' ESem2 h2 \<rho>2"
  assumes "adm_on (fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda>\<rho>'. heapToEnv h (\<lambda>e. ESem1 e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
                  \<times> fix_join_compat (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) (\<lambda>\<rho>'. heapToEnv h2 (\<lambda>e. ESem2 e \<cdot> \<rho>')\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>))
                 (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
  assumes "\<And>y z. y \<in> fix_join_compat (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
               (\<lambda>\<rho>'. heapToEnv h (\<lambda>e. ESem1 e \<cdot> \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) \<Longrightarrow>
          z \<in> fix_join_compat (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)
               (\<lambda>\<rho>'. heapToEnv h2 (\<lambda>e. ESem2 e \<cdot> \<rho>')\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) \<Longrightarrow>
          P y z \<Longrightarrow>
          P (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<squnion> heapToEnv h (\<lambda>e. ESem1 e \<cdot> y)\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)
           (\<rho>2\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub> \<squnion> heapToEnv h2 (\<lambda>e. ESem2 e \<cdot> z)\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>) "
  shows "P (has_ESem.HSem ESem1 h \<rho>) (has_ESem.HSem ESem2 h2 \<rho>2)"
  unfolding has_ESem.HSem_def if_P[OF cond1] if_P[OF cond2]
  apply (rule parallel_fix_on_ind[OF fix_on_cond_fjc[OF cond1] fix_on_cond_fjc[OF cond2]])
  apply (rule assms(3))
  using assms(4) apply (simp add: bottom_of_fjc to_bot_fmap_def)
  by (rule assms(5))

lemma parallel_HSem_ind_different_ESem_disjoint:
  assumes disj1: "fdom \<rho> \<inter> heapVars h = {}"
  assumes disj2: "fdom \<rho>2 \<inter> heapVars h2 = {}"
  assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
  assumes "\<And>y z. P y z \<Longrightarrow> P (\<rho> f++ heapToEnv h (\<lambda>e. ESem1 e \<cdot> y)) (\<rho>2 f++ heapToEnv h2 (\<lambda>e. ESem2 e \<cdot> z))"
  shows "P (has_ESem.HSem ESem1 h \<rho>) (has_ESem.HSem ESem2 h2 \<rho>2)"
proof (rule parallel_HSem_ind_different_ESem)
  interpret HSem1: has_ESem ESem1.
  interpret HSem2: has_ESem ESem2.
  case goal1 from disj1 show ?case by (rule HSem1.disjoint_is_HSem_cond)
  case goal2 from disj2 show ?case by (rule HSem2.disjoint_is_HSem_cond)
  case goal3 from assms(3) show ?case by (rule adm_is_adm_on)
  case goal4 from assms(4) show ?case.
  case goal5
  note fmap_expand_join_disjunct[of \<rho> "heapToEnv h (\<lambda>e. ESem1 e \<cdot> y)", simplified, OF disj1]
  moreover
  note fmap_expand_join_disjunct[of \<rho>2 "heapToEnv h2 (\<lambda>e. ESem2 e \<cdot> z)", simplified, OF disj2]
  moreover  
  note assms(5)[OF goal5(3)] 
  ultimately
  show ?case by simp
qed

subsubsection {* Equivariance of @{term HSem} *}

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); env1 = env2 ; heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.HSem ESem1 heap1 env1 = has_ESem.HSem  ESem2 heap2 env2"
  unfolding has_ESem.HSem_def
  by (auto cong:heapToEnv_cong)

lemma HSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.HSem ESem h \<rho> = has_ESem.HSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> h) (\<pi> \<bullet> \<rho>)"
proof (cases "has_ESem.HSem_cond' ESem h \<rho>")
  case True
  hence True_permuted: "has_ESem.HSem_cond' (\<pi> \<bullet> ESem) (\<pi> \<bullet> h)  (\<pi> \<bullet> \<rho>)"
    by -(drule fix_join_cond_eqvt[where \<pi> = \<pi>], perm_simp, assumption)

  show ?thesis
   unfolding has_ESem.HSem_def
   apply (simp only: if_P[OF True] if_P[OF True_permuted])
   apply (subst fix_on_eqvt[OF fix_on_cond_fjc[OF True]])
   apply (subst bottom_of_eqvt[OF subpcpo_fjc])
   apply (subst fix_join_compat_eqvt[OF True])
   apply perm_simp
   apply rule
   done
next
case False 
  hence False_permuted: "\<not> has_ESem.HSem_cond' (\<pi> \<bullet> ESem) (\<pi> \<bullet> h) (\<pi> \<bullet> \<rho>)"
    apply -
    apply rule
    apply (erule notE)
    apply (drule fix_join_cond_eqvt[where \<pi> = "- \<pi>"])
    apply perm_simp
    by (metis (no_types) eqvt_bound pemute_minus_self unpermute_def)
  show ?thesis
   unfolding has_ESem.HSem_def
   apply (simp only: if_not_P[OF False] if_not_P[OF False_permuted])
   apply perm_simp
   apply rule
   done
qed

end
