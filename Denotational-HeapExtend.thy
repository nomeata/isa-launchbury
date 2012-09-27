theory "Denotational-HeapExtend"
  imports "Denotational-Common" "Denotational-Compatible"
begin

definition heapExtendMeet :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtendMeet \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>) )
    then fmap_meet \<rho> (fixR (fmap_bottom (fst ` set h)) (\<lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_meet \<rho> \<rho>'))))
    else fempty)"

lemma heapExtendMeet_def2:
  "heapExtendMeet \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>) )
    then (fixR (fmap_bottom (fdom \<rho> \<union> fst ` set h)) (\<lambda> \<rho>' . fmap_meet \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>'))))
    else fempty)" (is "_ = (if _ then fixR ?x2 ?F2 else _)")
proof (cases "(\<forall> e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>))")
case True
  let "fixR ?x1 ?F1" = "fixR (fmap_bottom (fst ` set h)) (\<lambda> \<rho>'. heapToEnv h (\<lambda> e. eval e (fmap_meet \<rho> \<rho>')))"
  show ?thesis
  proof(induct rule: below_antisym[case_names lt gt])
  case lt
    have "fmap_meet \<rho> (fixR ?x1 ?F1) \<sqsubseteq> fixR (?F2 ?x2) ?F2"
      apply (rule parallel_fixR_ind)
      sorry also
    have "... = fixR ?x2 ?F2" sorry
    finally show ?case unfolding heapExtendMeet_def using True by auto
  next
  case gt
    have "fixR ?x2 ?F2  \<sqsubseteq> fmap_meet \<rho> (fixR ?x1 ?F1)"
      sorry
    thus ?case unfolding heapExtendMeet_def using True by auto
  qed
next
case False
  thus ?thesis unfolding heapExtendMeet_def apply (subst if_not_P, assumption)+ ..
qed


definition heapExtendMeed_cond
  where "heapExtendMeed_cond h eval \<rho> = 
    (compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e (fmap_bottom (fdom \<rho> \<union> fst ` set h)))) \<and> 
    (\<forall> e \<in> snd ` set h. subpcpo (compatible_with_exp e (fdom \<rho> \<union> fst ` set h))) \<and>
    (\<forall> e \<in> snd ` set h. cont_on (compatible_with_exp e (fdom \<rho> \<union> fst ` set h)) (eval e)))"


lemma heapExtendMeet_def3:
  "heapExtendMeet \<rho> h eval =
    (if heapExtendMeed_cond h eval \<rho>
    then fix_on (compatible_with_heap_and_env h eval \<rho>) (\<lambda> \<rho>'. fmap_meet \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>')))
    else fempty)"
sorry


lemma heapExtendMeet_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtendMeet \<rho> h eval = heapExtendMeet (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "(\<forall> e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>))")
  case True
  moreover hence "(\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)) \<and> compatible_fmap (\<pi> \<bullet> \<rho>) (heapToEnv (\<pi> \<bullet> h) (\<lambda> e. (\<pi> \<bullet> eval) e (\<pi> \<bullet> \<rho>))) " sorry
  ultimately show ?thesis
   unfolding heapExtendMeet_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_meet_eqvt)
   apply (subst fixR_eqvt)
   apply (auto simp add: fmap_bottom_eqvt)[1]
   apply perm_simp
   apply rule
   done
next
case False thus ?thesis
   unfolding heapExtendMeet_def
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

lemma heapExtendMeet_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtendMeet env1 heap1 eval1 = heapExtendMeet env2 heap2 eval2"
  unfolding heapExtendMeet_def
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
