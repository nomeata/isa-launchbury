theory HSemUpd
  imports "HeapToEnv" DistinctVars "HOLCF-Set" "HOLCF-Down-Closed"
begin

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


lemma sharp_star_Env': "atom ` fst ` set \<Gamma> \<sharp>* (\<rho> :: ('var::{cont_pt,at_base}, 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}) fmap) \<longleftrightarrow> fst ` set \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct \<Gamma>, auto simp add: fresh_star_def sharp_Env)

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> ('var::{cont_pt,at_base}, 'value) fmap \<Rightarrow> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}"
begin

definition HSem :: "('var \<times> 'exp) list \<Rightarrow> ('var, 'value) fmap \<Rightarrow> ('var, 'value) fmap"
  where
  "HSem h \<rho> = 
    (if (\<forall> e \<in> snd `set h. cont (ESem e))
     then  fix_on' (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. ESem e \<rho>'))
     else (fmap_bottom (fdom \<rho> \<union> fst ` set h)))"

lemma HSem_def'':
  assumes "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "HSem h \<rho> = fix_on' (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. ESem e \<rho>'))"
  unfolding HSem_def using assms by metis

lemma fix_on_cond_HSem':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "fix_on_cond {x. fmap_bottom (fdom \<rho> \<union> fst ` set h) \<sqsubseteq> x}
          (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. ESem e \<rho>'))"
  apply (rule fix_on_condI)
  apply (rule subpcpo_cone_above)
  apply (rule bottom_of_cone_above)
  apply (rule closed_onI, simp)
  apply (rule cont_onI)
  apply (rule contE[OF fmap_add_cont2cont[OF cont_const cont2cont_heapToEnv[OF assms]] chain_on_is_chain])
    apply assumption+
  done

lemma HSem_monofun'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  shows "HSem h \<rho> \<sqsubseteq> HSem h \<rho>'"
  apply (subst (1 2) HSem_def'')
  apply (erule cont)
  apply (rule fix_on_mono2[OF fix_on_cond_HSem'[OF cont] fix_on_cond_HSem'[OF cont]])
    apply assumption+
  apply (metis assms(2) below.r_refl fmap_below_dom)
  apply (rule fmap_add_mono[OF `\<rho> \<sqsubseteq> \<rho>'`])
  by (rule cont2monofunE[OF cont2cont_heapToEnv[OF cont]])

lemma HSem_cont'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "chain Y"
  shows "HSem h (\<Squnion> i. Y  i) \<sqsubseteq> (\<Squnion> i. HSem h (Y i))"
proof-
  have fdoms:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 
  show ?thesis
    apply (subst (1 2) HSem_def'')
    apply (erule cont)+
    unfolding fdoms
    proof (rule fix_on_cont[OF `chain Y`, where S = "{x . fmap_bottom (fdom (\<Squnion> i. Y i) \<union> fst `set h) \<sqsubseteq> x}"])
      show "cont (\<lambda>a b. a f++ heapToEnv h (\<lambda>e. ESem e b))"
        by (rule cont2cont_lambda[OF fmap_add_cont1])
      fix i
        from fix_on_cond_HSem'[OF cont, where \<rho> = "Y i", unfolded fdoms]
        show "fix_on_cond {x. fmap_bottom (fdom (\<Squnion> i. Y i) \<union> fst ` set h) \<sqsubseteq> x}
               (fmap_bottom (fdom (Lub Y) \<union> fst ` set h)) (\<lambda>a. Y i f++ heapToEnv h (\<lambda>e. ESem e a))"
           by metis
    qed
qed

end

locale has_cont_ESem = has_ESem +
  assumes ESem_cont: "\<And> e. cont (ESem e)"
begin

  lemma HSem_def':
    shows "HSem h \<rho> = fix_on' (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. ESem e \<rho>'))"
    unfolding HSem_def using ESem_cont by metis

  lemma fix_on_cond_HSem:
    shows "fix_on_cond {x. fmap_bottom (fdom \<rho> \<union> fst ` set h) \<sqsubseteq> x}
            (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. ESem e \<rho>'))"
    apply (rule fix_on_cond_HSem') using ESem_cont by metis

  lemma HSem_ind:
    assumes "adm P"
    assumes "P (fmap_bottom (fdom \<rho> \<union> fst ` set h))"
    assumes step: "\<And> y. fdom y = fdom \<rho> \<union> fst ` set h \<Longrightarrow>
          P y \<Longrightarrow>  P (\<rho> f++ (heapToEnv h (\<lambda>e. ESem e y)))"
    shows "P (HSem h \<rho>)"
    unfolding HSem_def'
    apply (rule fix_on_ind[OF fix_on_cond_HSem])
    apply (rule adm_is_adm_on[OF `adm P`])
    apply fact
    apply (rule step)
    apply simp
    apply assumption
    done
  
  lemma parallel_HSem_ind:
    assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
    assumes "P (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (fmap_bottom (fdom \<rho>2 \<union> fst ` set h2))"
    assumes step: "\<And>y z. fdom y = fdom \<rho> \<union> fst ` set h \<Longrightarrow>
            fdom z = fdom \<rho>2 \<union> fst ` set h2 \<Longrightarrow>
            P y z \<Longrightarrow>
            P (\<rho> f++ (heapToEnv h (\<lambda>e. ESem e y))) (\<rho>2 f++ (heapToEnv h2 (\<lambda>e. ESem e z)))"
    shows "P (HSem h \<rho>) (HSem h2 \<rho>2)"
    unfolding HSem_def'
    apply (rule parallel_fix_on_ind[OF fix_on_cond_HSem fix_on_cond_HSem])
    apply (rule adm_is_adm_on[OF `adm _`])
    apply fact
    apply (rule step)
    apply simp+
    done
  
  lemma HSem_eq:
    shows "HSem h \<rho> = \<rho> f++ (heapToEnv h (\<lambda>e. ESem e (HSem h \<rho>)))"
    unfolding HSem_def'
    by (rule fix_on_eq[OF fix_on_cond_HSem])  
  
  lemma the_lookup_HSem_other:
    assumes "y \<notin> fst ` set h"
    shows "the (lookup (HSem h \<rho>) y) = the (lookup \<rho> y)"
    apply (subst HSem_eq)
    using assms by simp
  
  lemma the_lookup_HSem_heap:
    assumes "y \<in> fst ` set h"
    shows "the (lookup (HSem h \<rho>) y) = ESem (the (map_of h y)) (HSem h \<rho>)"
    apply (subst HSem_eq)
    using assms by (simp add: lookupHeapToEnv)

  lemma fdom_HSem[simp]:
    "fdom (HSem h \<rho>) = fdom \<rho> \<union> fst ` set h"
    by (subst HSem_eq, simp)

  (*
  lemma HSem_refines:
    assumes "HSem_cond' h \<rho>"
    shows "fmap_expand \<rho> (fdom \<rho> \<union> fst `set h) \<sqsubseteq> HSem h \<rho>"
    apply (subst HSem_eq[OF assms(1)])
    apply (rule join_above1[OF rho_F_compat_jfc''[OF assms HSem_there[OF assms]]])
  done
  *)
  
  lemma HSem_add_fresh:
    assumes fresh: "atom x \<sharp> (\<rho>,\<Gamma>)"
    assumes step: "\<And>e \<rho>'. fdom \<rho>' = fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>) \<Longrightarrow> e \<in> snd ` set \<Gamma> \<Longrightarrow> ESem e \<rho>' = ESem e (fmap_restr (fdom \<rho>' - {x}) \<rho>')"
    shows  "fmap_restr (fdom \<rho> \<union> fst ` set \<Gamma>) (HSem ((x, e) # \<Gamma>) \<rho>) = HSem \<Gamma> \<rho>"
  proof (rule parallel_HSem_ind)
  case goal1 show ?case by auto
  case goal2 show ?case by auto
  case (goal3 y z)
    have "fmap_restr (fdom \<rho> \<union> fst ` set \<Gamma>) \<rho> = \<rho>"
      apply (rule fmap_restr_useless)
      by auto
    moreover
  
    have "x \<notin> fdom \<rho> \<union> fst ` set \<Gamma>"
      using fresh
      apply (auto simp add: sharp_Env fresh_Pair)
      by (metis fresh_PairD(1) fresh_list_elem not_self_fresh)
    hence [simp]:"fdom y - {x} = fdom \<rho> \<union> fst ` set \<Gamma>"
      by (metis Diff_insert_absorb List.set.simps(2) Un_insert_right fst_conv goal3(1) goal3(2) image_insert)
  
    have "fmap_restr (fdom \<rho> \<union> fst`set \<Gamma>) (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e y)) = heapToEnv \<Gamma> (\<lambda>e. ESem e z)"
      apply (subst heapToEnv_remove_Cons_fmap_restr[OF _ `x \<notin> fdom \<rho> \<union> fst \` set \<Gamma>`])
        apply simp
        apply simp
      apply (rule heapToEnv_cong[OF refl])
      apply (subst step)
      using goal3(1) apply simp      
      apply assumption
      using `_ = z`[symmetric]
      apply simp
      done
    ultimately
    show ?case
      by (simp add: fmap_restr_join)
  qed
  
  lemma HSem_reorder:
    assumes "distinctVars \<Gamma>"
    assumes "distinctVars \<Delta>"
    assumes "set \<Gamma> = set \<Delta>"
    shows "HSem \<Gamma> \<rho> = HSem \<Delta> \<rho>"
  by (simp add: HSem_def  heapToEnv_reorder[OF assms] assms(3))
  
  lemma HSem_reorder_head:
    assumes "x \<noteq> y"
    shows "HSem ((x,e1)#(y,e2)#\<Gamma>) \<rho> = HSem ((y,e2)#(x,e1)#\<Gamma>) \<rho>"
  proof-
    have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
      by auto
    thus ?thesis      
      unfolding HSem_def  heapToEnv_reorder_head[OF assms]
      by simp
  qed
  
  lemma HSem_reorder_head_append:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "HSem ((x,e)#\<Gamma>@\<Delta>) \<rho> = HSem (\<Gamma> @ ((x,e)#\<Delta>)) \<rho>"
  proof-
    have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
    thus ?thesis
      unfolding HSem_def  heapToEnv_reorder_head_append[OF assms]
      by simp
  qed  
  
  
  lemma HSem_subst_exp:
    assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (fst`set ((x,e)#\<Gamma>)) \<Longrightarrow> ESem e \<rho>' = ESem e' \<rho>'"
    shows "HSem ((x,e)#\<Gamma>) \<rho> = HSem ((x,e')#\<Gamma>) \<rho>"
    apply (rule parallel_HSem_ind)
    apply (auto)[1]
    apply simp
    apply (subst heapToEnv_subst_exp)
    apply (rule assms)
    apply simp+
    done
  
  (*
  lemma HSem_refines_lookup: "HSem_cond' \<Gamma> \<rho> \<Longrightarrow> x \<in> fdom \<rho> \<Longrightarrow> the (lookup \<rho> x) \<sqsubseteq> the (lookup (HSem \<Gamma> \<rho>) x)"
    apply (drule HSem_refines)
    apply (drule fmap_belowE[of _ _ x])
    apply simp
    done
  *)

  lemma HSem_heap_below: "x \<in> fst ` set \<Gamma> \<Longrightarrow> ESem (the (map_of \<Gamma> x)) (HSem \<Gamma> \<rho>) \<sqsubseteq> the (lookup (HSem \<Gamma> \<rho>) x)"
    apply (simp add: the_lookup_HSem_heap)
    done
  
  
  lemma fmap_restr_HSem_noop:
    assumes "fst`set \<Gamma> \<inter> fdom \<rho> = {}"
    shows "fmap_restr (fdom \<rho>) (HSem \<Gamma> \<rho>) = \<rho>"
    apply (rule fmap_eqI)
    using assms apply auto[1]
    using assms apply auto[1]
    apply (subst the_lookup_HSem_other)
    apply auto
    done
  
  lemma HSem_disjoint_less:
    assumes "fst`set \<Gamma> \<inter> fdom \<rho> = {}"
    shows "\<rho> \<le> HSem \<Gamma> \<rho>"
    using assms
  by (metis fdom_HSem fmap_less_restrict fmap_restr_HSem_noop sup_ge1)
  
  

  lemma HSem_below:
    assumes "fmap_expand \<rho> (fdom \<rho> \<union> fst ` set h) \<sqsubseteq> r"
    assumes "\<And>x. x \<in> fst ` set h \<Longrightarrow> ESem (the (map_of h x)) r \<sqsubseteq> the (lookup r x)"
    shows "HSem h \<rho> \<sqsubseteq> r"
  proof (rule HSem_ind)
    from fmap_below_dom[OF assms(1)]
    have [simp]:"fdom r = fdom \<rho> \<union> fst ` set h" by simp
    {
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      show ?case
      apply (rule fmap_add_belowI)
      apply (metis `fdom r = fdom \<rho> \<union> fst \` set h` heapToEnv_fdom)

      apply simp
      apply (subst lookupHeapToEnv, assumption)
      apply (erule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] assms(2)])
      
      apply (rule below_trans[OF eq_imp_below fmap_belowE[OF assms(1)]])
      apply simp
      done
    next
    }
  qed  

  lemma HSem_Nil[simp]: "HSem [] \<rho> = \<rho>"
    by (subst HSem_eq, simp)

  (*
  lemma HSem_redo:
    shows "HSem \<Gamma> (fmap_restr (fdom \<rho> \<union> fst ` set \<Delta>) (HSem (\<Gamma>@\<Delta>) \<rho>)) = HSem (\<Gamma> @ \<Delta>) \<rho>" (is "?LHS = ?RHS")
  proof (rule below_antisym)
    show "?LHS \<sqsubseteq> ?RHS"
    proof(rule HSem_below)
    case goal1
      show ?case
        apply (rule fmap_expand_fmap_restr_below)
        apply auto
        done
    case (goal2 x)
      hence "x \<in> fst ` set (\<Gamma>@\<Delta>)" by auto
      show ?case
        apply (subst the_lookup_HSem_both[OF assms(1) `x \<in> fst \` set (\<Gamma>@\<Delta>)`])
        apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(1) `x \<in> fst \` set (\<Gamma>@\<Delta>)`]]])
        using goal2 by (auto simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
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
      proof(cases "x \<in> fst ` set \<Gamma>")
      case True
        show ?thesis
          apply (subst the_lookup_HSem_both[OF assms(2) True])
          apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(2) True]]])
          using True by (auto simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
      next
      case False
        hence delta: "x \<in> fst ` set \<Delta>" using goal2 by auto
        show ?thesis
          apply (subst the_lookup_HSem_other[OF False])
          apply (subst lookup_fmap_restr)
            using delta apply auto[2]
          apply (subst the_lookup_HSem_both[OF assms(1) goal2])
          apply (rule below_trans[OF _ join_above2[OF the_lookup_HSem_both_compatible[OF assms(1) `x \<in> fst \` set (\<Gamma>@\<Delta>)`]]])
          apply (rule cont2monofunE[OF ESem_cont `?LHS \<sqsubseteq> ?RHS`])
          done
      qed
    qed
  qed
  *)

  lemma HSem_mono:
    assumes "\<rho>1 \<sqsubseteq> \<rho>2"
    shows "HSem \<Gamma> \<rho>1 \<sqsubseteq> HSem \<Gamma> \<rho>2"
    by(rule HSem_monofun''[OF ESem_cont assms])

  (*
  lemma iterative_HSem:
    assumes "HSem_cond' ((x, e) # \<Gamma>) \<rho>"
    assumes "x \<notin> fst `set \<Gamma>"
    shows "HSem ((x,e) # \<Gamma>) \<rho> =
        fix_on (fix_join_compat'' (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))) (\<lambda> \<rho>'.  fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<rho>')) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))))
                (\<lambda> \<rho>'. (HSem \<Gamma> \<rho>')
                        \<squnion> (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))(x f\<mapsto> ESem e \<rho>') 
                        \<squnion> (fmap_expand \<rho> (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))))" (is "_ = fix_on ?S ?R")
  apply (subst HSem_def'[OF assms(1)])
  proof(rule below_antisym)
    interpret subpcpo ?S by (rule subpcpo_jfc'')
  
    let "?d" = "fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)"
  
    let "fix_on _ ?L" = "fix_on ?S
                         (\<lambda>\<rho>'. fmap_expand \<rho> ?d \<squnion>
                               fmap_expand (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. ESem e \<rho>')) (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>)))"
    let "(\<lambda> \<rho>'. ?L1 \<rho>' \<squnion> ?L2 \<rho>')" = ?L
    let "(\<lambda> \<rho>'. ?R1 \<rho>' \<squnion> (?R2 \<rho>' \<squnion> ?R3 \<rho>'))" = ?R
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      hence fdom1: "fdom \<rho>' = ?d"
      apply (subst (asm) fjc''_iff)
      apply (drule fmap_below_dom)
      apply (subst (asm) fdom_fix_on[OF fix_on_cond_jfc''[OF assms(1)], unfolded bottom_of_jfc''])
      apply auto
      done
    } note fdom = this
  
    { fix \<rho>' assume "\<rho>' \<in> ?S"
      have fdom1: "(fdom \<rho>' \<union> fst ` set \<Gamma>) = ?d" using fdom[OF `\<rho>' \<in> ?S`] by auto
      have fdom2: "(fdom \<rho>' \<union> fst ` set ((x,e) # \<Gamma>)) = ?d" using fdom1 by auto
      have "HSem_cond' ((x,e) # \<Gamma>) \<rho>'" by (rule HSem_cond'_of_member[OF assms(1) `\<rho>'\<in>?S`])
      from this[unfolded fdom2]
      have "HSem_cond' \<Gamma> \<rho>'"
        apply (subst (1 2) fdom1, rule fjc'_of_fun_below)
        apply (rule fun_belowI)
        apply (rule heapToEnv_mono)
        apply simp
        apply rule
        apply (simp add: assms(2))
        apply (rule cont_compose[OF fmap_expand_cont cont2cont_heapToEnv[OF ESem_cont]])
        done
    } note HSem_cond'_Gamma = this
  
    have closedL: "closed_on ?L"
      by (rule closed_on_jfc''[OF assms(1)])
  
    have closedR1: "closed_on ?R1"
      apply (rule closed_onI)
      apply (rule HSem_ind)
      apply (rule adm_is_adm_on[OF subcpo_mem_adm[OF subcpo_jfc'']])
      apply (rule down_closed.down_closedE[OF down_closed_jfc''], assumption)
      apply (frule fdom)
      apply (auto simp add:to_bot_fmap_def simp del:fjc''_iff)[1]
      apply (rule join_jfc'')
       apply (subst fmap_expand_noop)
       apply (frule fdom, auto)[1]
       apply assumption
      
      apply (rule down_closed.down_closedE[OF down_closed_jfc'' F_pres_compat''[OF assms(1)]], assumption) back
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
      apply (rule down_closed.down_closedE[OF down_closed_jfc'' F_pres_compat''[OF assms(1)]], assumption)
      apply (rule fmap_belowI')
      apply (frule fdom, auto)[1]
      apply (case_tac "xaa = x", simp_all)
      done    
      
    have closedR3: "closed_on ?R3"
      apply (rule closed_onI)
      by (rule rho_jfc''[OF assms(1)])
  
    have closedR: "closed_on ?R"
      by (rule closed_on_join_jfc''[OF closedR1 closed_on_join_jfc''[OF closedR2 closedR3]])
  
    have contL: "cont_on ?L"
      by (rule cont_on_jfc''[OF assms(1)])
      
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
      apply (rule cont_on_join_jfc')
      apply (rule closedR1)
      apply (rule closed_on_join_jfc''[OF closedR2 closedR3])
      apply (rule contR1)
      apply (rule cont_on_join_jfc')
      apply (rule closedR2)
      apply (rule closedR3)
      apply (rule contR2)
      apply (rule contR3)
      done
  
    note fix_on_condL = fix_on_cond_jfc''[OF assms(1)]
  
    have fix_on_condR: "fix_on_cond ?S bottom_of ?R"
      by (rule fix_on_condI[OF subpcpo_jfc'' refl closedR contR])
  
    have R_there: "fix_on ?S ?R \<in> ?S"
      by (rule fix_on_there[OF fix_on_condR])
  
      
    have compatL: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?L1 x) (?L2 x)"
      by (rule compat_jfc''[OF rho_jfc''[OF assms(1)]  F_pres_compat''[OF assms(1)]])
      
    have compatR2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R2 x) (?R3 x)"
      by (rule compat_jfc''[OF closed_onE[OF closedR2] closed_onE[OF closedR3]])
    have compatR1R2: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x)"
      by (rule compat_jfc''[OF closed_onE[OF closedR1] closed_onE[OF closedR2]])
    have compatR1R2R3: "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x) (?R2 x \<squnion> ?R3 x)"
      by (rule compat_jfc''[OF closed_onE[OF closedR1] closed_onE[OF closed_on_join_jfc''[OF closedR2 closedR3]]])
    have compatR1R2R3': "\<And> x. x \<in> ?S \<Longrightarrow> compatible (?R1 x \<squnion> ?R2 x) (?R3 x)"
      by (rule compat_jfc''[OF closed_onE[OF closed_on_join_jfc''[OF closedR1 closedR2]] closed_onE[OF closedR3]])
  
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
      proof (rule fmap_belowI')
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
          proof (cases "x' \<in> fst ` set \<Gamma>")
          case True
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. ESem e \<rho>')) x') \<sqsubseteq> the (lookup (HSem \<Gamma> \<rho>') x')"
              apply (subst HSem_eq[OF inner_cond])
              apply (subst the_lookup_join[OF rho_F_compat_jfc''[OF inner_cond  HSem_there[OF inner_cond]]])
              apply (insert the_lookup_compatible[OF rho_F_compat_jfc''[OF inner_cond  HSem_there[OF inner_cond]], of x'])
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
      unfolding bottom_of_jfc''
      by (rule R_there[unfolded fjc''_iff, unfolded bottom_of_jfc''])
  qed
  *)
  
  lemma HSem_subst_expr_below:
    assumes below: "ESem e1 (HSem ((x, e2) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e2 (HSem ((x, e2) # \<Gamma>) \<rho>)"
    shows "HSem ((x, e1) # \<Gamma>) \<rho> \<sqsubseteq> HSem ((x, e2) # \<Gamma>) \<rho>"
  proof (rule HSem_ind[where h = "(x, e1) # \<Gamma>"])
  case goal1 show ?case by auto
  case goal2 show ?case by simp
  case (goal3 \<rho>')
    show ?case
      apply (subst HSem_eq)
      apply (rule fmap_add_mono)
      apply simp
      apply (subst (1 2) heapToEnv.simps)
      apply (rule fmap_upd_mono)
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      apply (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] below])
      done
  qed    
  
  lemma HSem_subst_expr:
    assumes below1: "ESem e1 (HSem ((x, e2) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e2 (HSem ((x, e2) # \<Gamma>) \<rho>)"
    assumes below2: "ESem e2 (HSem ((x, e1) # \<Gamma>) \<rho>) \<sqsubseteq> ESem e1 (HSem ((x, e1) # \<Gamma>) \<rho>)"
    shows "HSem ((x, e1) # \<Gamma>) \<rho> = HSem ((x, e2) # \<Gamma>) \<rho>"
    by (metis assms HSem_subst_expr_below below_antisym)

end

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); env1 = env2 ; heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.HSem ESem1 heap1 env1 = has_ESem.HSem  ESem2 heap2 env2"
  unfolding has_ESem.HSem_def
  by (auto cong:heapToEnv_cong)

lemma subcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subcpo S"
  shows "subcpo (\<pi> \<bullet> S)"
proof(rule subcpoI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
    hence "chain (-\<pi> \<bullet> Y)" by (rule chain_eqvt)
  moreover
  assume "\<And> i. Y i \<in> \<pi> \<bullet> S"
  hence "\<And> i. - \<pi> \<bullet> Y i \<in> S" by (metis (full_types) mem_permute_iff permute_minus_cancel(1))
  hence "\<And> i. (- \<pi> \<bullet> Y) i \<in> S" by (metis eqvt_apply permute_pure)
  ultimately
  have "(\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> S" by (metis subcpo.cpo'[OF assms])
  hence "\<pi> \<bullet> (\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> \<pi> \<bullet> S"  by (metis mem_permute_iff)
  find_theorems permute cont
  thus "(\<Squnion> i. Y i) \<in> \<pi> \<bullet> S"
    apply -
    apply (subst (asm) cont2contlubE[OF perm_cont `chain (-\<pi> \<bullet> Y)`])
    by (metis image_image permute_minus_cancel(1) permute_set_eq_image range_eqvt)
qed

lemma subpcpo_bot_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo_bot S b"
  shows "subpcpo_bot (\<pi> \<bullet> S) (\<pi> \<bullet> b)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo'[OF subcpo_eqvt[OF subpcpo_is_subcpo[OF subpcpo_bot_is_subpcpo[OF assms]]]])
  apply (metis bottom_of_subpcpo_bot_there[OF assms] mem_permute_iff)
  apply (metis (full_types) bottom_of_subpcpo_bot_minimal[OF assms] eqvt_bound mem_permute_iff perm_cont_simp)
  done

lemma subpcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo S"
  shows "subpcpo (\<pi> \<bullet> S)"
  by (rule subpcpo_bot_is_subpcpo[OF subpcpo_bot_eqvt[OF subpcpo_is_subpcpo_bot[OF assms]]])

lemma bottom_of_eqvt:
  assumes "subpcpo S"
  shows "\<pi> \<bullet> (bottom_of (S ::('a::cont_pt) set)) = bottom_of (\<pi> \<bullet> S)"
  by (rule bottom_of_subpcpo_bot[symmetric, OF subpcpo_bot_eqvt[OF  subpcpo_is_subpcpo_bot[OF assms]]])

(*
lemma fix_on_jfc'_eqvt:
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}"
  assumes "cont F"
  assumes F_pres_compat:"\<And> x. compatible \<rho> x \<Longrightarrow> compatible \<rho> (F x)"
  shows "\<pi> \<bullet> fix_on (fix_join_compat' \<rho>) (\<lambda> \<rho>'. \<rho> \<squnion> F \<rho>') = fix_on (fix_join_compat' (\<pi> \<bullet> \<rho>))  (\<lambda> \<rho>'. (\<pi> \<bullet> \<rho>) \<squnion> (\<pi> \<bullet> F) \<rho>')"
proof-
  have cont_permuted: "cont (\<pi> \<bullet> F)" 
    by (metis assms(1) perm_still_cont)
  have F_pres_compat_permuted: "(\<And> x. compatible (\<pi> \<bullet> \<rho>) x \<Longrightarrow> compatible (\<pi> \<bullet> \<rho>) ((\<pi> \<bullet> F) x))"
    by (metis assms(2) compatible_eqvt eqvt_bound eqvt_lambda unpermute_def)
  show ?thesis
    apply (rule parallel_fix_on_ind[OF subpcpo_jfc' subpcpo_jfc' _ closed_on_jfc'[OF assms] cont_on_jfc'[OF assms] closed_on_jfc'[OF cont_permuted F_pres_compat_permuted] cont_on_jfc'[OF cont_permuted F_pres_compat_permuted] ])
    apply (rule adm_is_adm_on)
    apply auto
    apply (subst bottom_of_eqvt[OF subpcpo_jfc'])
    apply (subst fix_join_compat'_eqvt, rule)
    apply perm_simp
    apply rule
    done
qed
*)

lemma closed_on_eqvt:
  "closed_on S F \<Longrightarrow> closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule closed_onI)
  apply (simp add: permute_set_def)
  by (metis closed_onE eqvt_apply)

lemma cont_eqvt[eqvt]:
  "cont (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont (\<pi> \<bullet> F)"
  apply (rule contI)
  apply (drule_tac Y = "unpermute \<pi> Y" in contE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done

lemma chain_on_eqvt:
  "chain_on (S::'a::cont_pt set) Y \<Longrightarrow> chain_on (\<pi> \<bullet> S) (\<pi> \<bullet> Y)"
  apply (rule chain_onI)
  apply (drule_tac i = i in chain_onE)
  apply (metis perm_cont_simp permute_fun_app_eq permute_pure)
  apply (drule_tac i = i in chain_on_is_on)
  by (metis (full_types) mem_permute_iff permute_fun_app_eq permute_pure)

lemma cont_on_eqvt:
  "cont_on S (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule cont_onI)
  apply (drule_tac Y = "unpermute \<pi> Y" in cont_onE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (metis chain_on_eqvt permute_minus_cancel(2))
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (drule chain_on_is_chain)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done


lemma fix_on_cond_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof
  from assms
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
    by (metis fix_on_cond.cases)+

  show "subpcpo (\<pi> \<bullet> S)" by (rule subpcpo_eqvt[OF pcpo1])
  show "bottom_of (\<pi> \<bullet> S) = \<pi> \<bullet> b" by (simp add: bottom_of_eqvt[OF pcpo1, symmetric])
  show "closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule closed_on_eqvt[OF closed])
  show "cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule cont_on_eqvt[OF cont])
qed

lemma fix_on_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "\<pi> \<bullet> (fix_on' b F) = fix_on' (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof-
  have permuted: "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
    by (rule fix_on_cond_eqvt[OF assms])
  show ?thesis
    apply (rule parallel_fix_on_ind[OF assms permuted])
    apply (rule adm_is_adm_on, auto)[1]
    by (auto simp add: eqvt_apply)
qed

lemma to_bot_eqvt[eqvt,simp]: "\<pi> \<bullet> to_bot (\<rho>::'a::{subpcpo_partition,cont_pt}) = to_bot (\<pi> \<bullet> \<rho>)"
proof(rule below_antisym)
  show "to_bot (\<pi> \<bullet> \<rho>) \<sqsubseteq> \<pi> \<bullet> to_bot \<rho>"
    by (metis perm_cont_simp to_bot_minimal unrelated)
  show "\<pi> \<bullet> to_bot \<rho> \<sqsubseteq> to_bot (\<pi> \<bullet> \<rho>)"
    by (metis eqvt_bound perm_cont_simp to_bot_minimal unrelated)
qed

lemma HSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.HSem ESem h \<rho> = has_ESem.HSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> h) (\<pi> \<bullet> \<rho>)"
proof(cases "\<forall> e \<in> snd ` set h.  cont (ESem e)")
case True
  from permute_boolI[OF this, where p = \<pi>]
  have True_permuted: "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e)"
    by perm_simp

  show ?thesis          
   unfolding has_ESem.HSem_def if_P[OF True]  if_P[OF True_permuted] 
   apply (subst fix_on_eqvt[OF has_ESem.fix_on_cond_HSem'])
   apply (metis True)
   apply (subst fmap_bottom_eqvt, simp)
   apply perm_simp
   apply rule
   done
next
case False 
  from permute_boolI[OF this, where p = \<pi>]
  have False_permuted: "\<not> (\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e))"
    by perm_simp
  show ?thesis
   unfolding has_ESem.HSem_def if_not_P[OF False]  if_not_P[OF False_permuted] 
   apply (subst fmap_bottom_eqvt, simp)
   apply perm_simp
   apply rule
   done
qed


end
