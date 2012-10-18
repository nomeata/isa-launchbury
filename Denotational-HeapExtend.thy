theory "Denotational-HeapExtend"
  imports "Denotational-Common" "HOLCF-Set" "HOLCF-Down-Closed"
begin

definition heapExtendJoin :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtendJoin \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>) )
    then fmap_join \<rho> (fixR (fmap_bottom (fst ` set h)) (\<lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_join \<rho> \<rho>'))))
    else fempty)"

lemma heapExtendJoin_def2:
  "heapExtendJoin \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>) )
    then (fixR (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>' . fmap_join \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>'))))
    else fempty)" (is "_ = (if _ then fixR ?x2 ?F2 else _)")
proof (cases "(\<forall> e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>))")
case True
  let "fixR ?x1 ?F1" = "fixR (fmap_bottom (fst ` set h)) (\<lambda> \<rho>'. heapToEnv h (\<lambda> e. eval e (fmap_join \<rho> \<rho>')))"
  show ?thesis
  proof(induct rule: below_antisym[case_names lt gt])
  case lt
    have "fmap_join \<rho> (fixR ?x1 ?F1) \<sqsubseteq> fixR (?F2 ?x2) ?F2"
      apply (rule parallel_fixR_ind)
      sorry also
    have "... = fixR ?x2 ?F2" sorry
    finally show ?case unfolding heapExtendJoin_def using True by auto
  next
  case gt
    have "fixR ?x2 ?F2  \<sqsubseteq> fmap_join \<rho> (fixR ?x1 ?F1)"
      sorry
    thus ?case unfolding heapExtendJoin_def using True by auto
  qed
next
case False
  thus ?thesis unfolding heapExtendJoin_def apply (subst if_not_P, assumption)+ ..
qed

definition heapExtendJoin_cond
  where "heapExtendJoin_cond h eval \<rho> = ((fdom \<rho> \<inter> fst ` set h) = {})"

consts compatible_with_heap_and_env :: "heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value) \<Rightarrow> Env \<Rightarrow> Env set"

lemma heapExtendJoin_def3:
  "heapExtendJoin \<rho> h eval =
    (if heapExtendJoin_cond h eval \<rho>
    then fix_on (compatible_with_heap_and_env h eval \<rho>) (\<lambda> \<rho>'. fmap_join \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>')))
    else fempty)"
sorry

lemma subpcpo_compat_h_e:
  "subpcpo (compatible_with_heap_and_env h ESem x)" sorry

lemma closed_on_compat_h_e:
  "closed_on (compatible_with_heap_and_env h ESem x)
     (\<lambda>\<rho>'. fmap_join x (heapToEnv h (\<lambda>e. ESem e \<rho>')))" sorry

lemma cont_on_compat_h_e:
  "cont_on (compatible_with_heap_and_env h ESem x)
     (\<lambda>\<rho>'. fmap_join x (heapToEnv h (\<lambda>e. ESem e \<rho>')))" sorry

lemma compt_h_eD:
  "\<rho> \<in> compatible_with_heap_and_env h ESem x \<Longrightarrow> compatible_fmap x (heapToEnv h (\<lambda>e. ESem e \<rho>))" sorry

lemma bottom_of_compat_h_e:
  "bottom_of (compatible_with_heap_and_env h ESem x) = fmap_bottom (fdom x \<union> fst ` set h)" sorry

lemma heapExtendJoin_mono':
  assumes "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "monofun (\<lambda>\<rho>. heapExtendJoin \<rho> h ESem)"
proof (rule monofunI)
case (goal1 x y)
  hence [simp]:"fdom y = fdom x"
    by (metis fmap_below_dom)
  have subset:
    "compatible_with_heap_and_env h ESem y \<subseteq> compatible_with_heap_and_env h ESem x" sorry
  have same_bottom:
    "bottom_of (compatible_with_heap_and_env h ESem x) = bottom_of (compatible_with_heap_and_env h ESem y)"
    by (simp add: bottom_of_compat_h_e)

  show ?case
  proof(cases "fdom x \<inter> (fst ` set h) = {}")
  case True[simp]
    show ?thesis
      unfolding heapExtendJoin_def3
      unfolding heapExtendJoin_cond_def
      apply (simp)
      apply (rule parallel_fix_on_ind[OF subpcpo_compat_h_e subpcpo_compat_h_e _ closed_on_compat_h_e cont_on_compat_h_e  closed_on_compat_h_e cont_on_compat_h_e])
      apply (rule adm_is_adm_on, simp)
      apply (subst same_bottom, rule below_refl)
      apply (drule compt_h_eD)+
      apply (erule (1) fmap_join_mono[OF _ _ `x \<sqsubseteq> y` ])
      apply (erule cont2monofunE[OF cont2cont_heapToEnv,rotated ])
      apply (erule assms(1))
      done
  next
  case False
    thus ?thesis
      unfolding heapExtendJoin_def3
      unfolding heapExtendJoin_cond_def
      by simp
  qed
qed

(* More special version first, just to check proof *)
lemma fix_join_cont':
  fixes F :: "'a::pcpo \<Rightarrow> 'a"
  assumes "chain Y"
  assumes "cont F"
  assumes "\<And> y::'a. cont (\<lambda>x. y \<squnion> x)"
  assumes "\<And> y::'a. cont (\<lambda>x. x \<squnion> y)"
  shows "(\<mu> x. (\<Squnion>i. Y i) \<squnion> F x) \<sqsubseteq> (\<Squnion> i. (\<mu> x. Y i \<squnion> F x))"
  apply (rule Fix.fix_least_below)
  apply (subst beta_cfun[OF cont_compose[OF assms(3) assms(2)]])
  apply (subst cont2contlubE[OF assms(2)])
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply (rule assms(4))
  
  apply (subst cont2contlubE[OF assms(3)])
  defer
  apply (subst cont2contlubE[OF assms(4) `chain Y`])
  apply (subst diag_lub)
  prefer 3
  apply (subst Fix.fix_eq) back
  apply (subst beta_cfun[OF cont_compose[OF assms(3) assms(2)]])
  apply (rule below_refl)
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF assms(3)])
  apply (rule cont_compose[OF `cont F`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply fact
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply fact
  apply (rule ch2ch_cont[OF _ `chain Y`])
  apply (rule cont_compose[OF `cont F`])
  apply (rule cont_compose[OF cont_Rep_cfun2 cont2cont_LAM]) 
  apply (rule cont_compose[OF assms(3) assms(2)])
  apply fact
  done

lemma "compatible_fmap a b \<Longrightarrow> compatible a b"
  unfolding compatible_def
  apply (rule exI[where x = "fmap_join a b"] )
  apply (rule is_lubI)
  apply (rule is_ubI)
  apply auto
  oops

lemma heapExtendJoin_cont':
  assumes "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "cont (\<lambda>\<rho>. heapExtendJoin \<rho> h ESem)"
proof (rule contI2)
case goal1 show ?case using assms by (metis heapExtendJoin_mono') 
next
case (goal2 Y)
  hence [simp]:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom)

  show ?case
  proof(cases "?d \<inter> (fst ` set h) = {}")
  case True[simp]
    (* Approach by finding compatible pcpo's: *)

    have "fix_on (compatible_with_heap_and_env h ESem (Lub Y)) (\<lambda>\<rho>'. fmap_join (Lub Y) (heapToEnv h (\<lambda>e. ESem e \<rho>'))) \<sqsubseteq>
      (\<Squnion> i. fix_on (compatible_with_heap_and_env h ESem (Lub Y)) (\<lambda>\<rho>'. fmap_join (Y i) (heapToEnv h (\<lambda>e. ESem e \<rho>'))))"
      apply (rule fix_on_cont''[OF `chain Y` subpcpo_compat_h_e])
      sorry

    show ?thesis
      unfolding heapExtendJoin_def3
      unfolding heapExtendJoin_cond_def
      apply (simp)
      apply (rule fix_on_cont'[OF `chain Y` subpcpo_compat_h_e closed_on_compat_h_e cont_on_compat_h_e])
      defer
      apply (simp add: bottom_of_compat_h_e)
      sorry
  next
  case False
    thus ?thesis
      unfolding heapExtendJoin_def3
      unfolding heapExtendJoin_cond_def
      by simp
  qed
qed


lemma heapExtendJoin_cont'':
  "\<lbrakk> (\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e));
    fdom (Y 0) \<inter> (fst ` set h) = {} \<rbrakk>
  \<Longrightarrow> range (\<lambda>i. heapExtendJoin (Y i) h ESem) <<| heapExtendJoin (\<Squnion> i. Y i) h ESem"
sorry


lemma heapExtendJoin_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtendJoin \<rho> h eval = heapExtendJoin (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "(\<forall> e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>))")
  case True
  moreover hence "(\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)) \<and> compatible_fmap (\<pi> \<bullet> \<rho>) (heapToEnv (\<pi> \<bullet> h) (\<lambda> e. (\<pi> \<bullet> eval) e (\<pi> \<bullet> \<rho>))) " sorry
  ultimately show ?thesis
   unfolding heapExtendJoin_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_join_eqvt)
   apply (subst fixR_eqvt)
   apply (auto simp add: fmap_bottom_eqvt)[1]
   apply perm_simp
   apply rule
   done
next
case False thus ?thesis
   unfolding heapExtendJoin_def
   apply (subst if_not_P, assumption)
   apply (subst if_not_P)
   apply  (rule notI)
   apply  (erule notE)
   apply  rule
   apply  (metis perm_still_cont4)
   apply  (erule conjE)
   apply  (drule compatible_fmap_eqvt[of _ _ "- \<pi>"])
   apply  (simp add: permute_fun_def heapToEnv_eqvt)
   apply (rule fempty_eqvt)
   done
qed

lemma heapExtendJoin_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtendJoin env1 heap1 eval1 = heapExtendJoin env2 heap2 eval2"
  unfolding heapExtendJoin_def
  by (auto cong:heapToEnv_cong)

definition heapExtend :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e))
    then fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h)) (\<Lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_update \<rho> \<rho>'))))
    else fempty)"


lemma heapExtend_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtend \<rho> h eval = heapExtend (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "\<forall> e \<in> snd ` set h. cont (eval e)")
  case True
  moreover hence "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)" by (simp only: perm_still_cont4 simp_thms(35))
  ultimately show ?thesis
   unfolding heapExtend_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_update_eqvt)
   apply (subst fix1_eqvt)
   apply (subst Lam_eqvt)
     apply (rule cont2cont)
     apply (rule cont_compose) back
     apply auto[1]
     apply auto[1]
    apply (auto simp add: fmap_bottom_eqvt)[1]
    apply perm_simp
    apply rule
    done
next
case False thus ?thesis
   unfolding heapExtend_def
   apply (simp_all only: if_not_P perm_still_cont4)
   apply auto
  done 
qed

lemma heapExtend_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtend env1 heap1 eval1 = heapExtend env2 heap2 eval2"
  unfolding heapExtend_def
  by (auto cong:heapToEnv_cong)


lemma heapExtend_cont[simp,cont2cont]: "cont (\<lambda>\<rho>. heapExtend \<rho> h eval)"
  unfolding heapExtend_def
  apply (cases "\<forall> e \<in> snd ` set h.  cont (eval e)")
  apply (simp_all only: if_P if_not_P perm_still_cont4 simp_thms(35) if_False)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply (subst beta_cfun)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply simp
  apply simp
  done
end
