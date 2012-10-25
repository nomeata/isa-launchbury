theory "Denotational-Compatible"
  imports "Denotational" "HOLCF-Set-Nominal" "FMap-Nominal-HOLCF" "HOLCF-Down-Closed"
begin

definition
  compatible_with_heapExtend' :: "(exp \<Rightarrow> var list \<Rightarrow> Env set) \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value) \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> Env set"
where
  "compatible_with_heapExtend' compatible_with_exp eval d h =
  (if True
  then {\<rho>.
    (\<forall> e\<in> snd`set h . \<forall> i. ((\<lambda> \<rho>'. fmap_join \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>')))^^i) (fmap_bottom (set d)) \<in> compatible_with_exp e d) \<and>
    (\<forall>i. compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e (((\<lambda> \<rho>'. fmap_join \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>')))^^i) (fmap_bottom (set d)))))) }
  else {})"

lemma compatible_with_heapExtend'_cong[fundef_cong]:
  "\<lbrakk> \<And> e. e\<in> snd`set h2 \<Longrightarrow> compatible_with_exp1 e d1 = compatible_with_exp2 e d2 ;  eval1 = eval2; d1 = d2; h1 = h2 \<rbrakk>
    \<Longrightarrow>  compatible_with_heapExtend' compatible_with_exp1 eval1 d1 h1 = compatible_with_heapExtend' compatible_with_exp2 eval2 d2 h2"
unfolding compatible_with_heapExtend'_def by auto

lemma  compatible_with_heapExtend'_eqvt[eqvt]:
  "\<pi> \<bullet> compatible_with_heapExtend' compatible_with_exp eval d h = compatible_with_heapExtend' (\<pi> \<bullet> compatible_with_exp) (\<pi> \<bullet> eval) (\<pi> \<bullet> d) (\<pi> \<bullet> h)"
  unfolding compatible_with_heapExtend'_def
  unfolding fmap_bottom_l_def[symmetric]
  by (perm_simp,rule)  


definition heapExtendJoin_cond
  where "heapExtendJoin_cond compatible_with_exp h eval \<rho> = 
    (compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e (fmap_bottom (fdom \<rho> \<union> fst ` set h)))) \<and> 
    (\<forall> e \<in> snd ` set h. subpcpo (compatible_with_exp e (fdom \<rho> \<union> fst ` set h))) \<and>
    (\<forall> e \<in> snd ` set h. cont_on (compatible_with_exp e (fdom \<rho> \<union> fst ` set h)) (eval e)))"


lemma compatible_with_HeapExtend'_down_closed:
  "\<lbrakk> \<And> e. e \<in> snd ` set h \<Longrightarrow> nice_domain (compatible_with_exp eval e d) (fmap_bottom (set d)) \<rbrakk> 
  \<Longrightarrow> down_closed (compatible_with_heapExtend' (compatible_with_exp eval) eval d h)"
unfolding compatible_with_heapExtend'_def 
  apply (subst if_True)
  apply (subst Collect_conj_eq)
  apply (rule down_closed_inter)
  apply (subst Collect_ball_eq)
  apply (rule down_closed_ball)
  apply (subst Collect_all_eq)
  apply (rule down_closed_inter)
  apply (subst vimage_Collect_eq[symmetric]) back
  apply (rule down_closed_vimage)
  apply (auto dest: nice_domain_is_down_closed)[1]
  
  oops

lemma compatible_with_HeapExtend'_nice_domain:
  "\<lbrakk> \<And> e. e \<in> snd ` set h \<Longrightarrow> nice_domain (compatible_with_exp eval e d) (fmap_bottom (set d)) \<rbrakk> 
  \<Longrightarrow> nice_domain (compatible_with_heapExtend' (compatible_with_exp eval) eval d h) (fmap_bottom (set d))"
sorry



nominal_primrec
  compatible_with_exp :: "(exp \<Rightarrow> Env \<Rightarrow> Value) \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> Env set" 
where
  "compatible_with_exp eval (Var v) d = {\<rho>' . fmap_bottom_l d \<sqsubseteq> \<rho>'}" |
  "atom x \<sharp> d \<Longrightarrow>
    compatible_with_exp eval (Lam [x]. e) d =
      fmap_restr_l d ` compatible_with_exp eval e (x # d)" |
  "compatible_with_exp eval (App e x) d = compatible_with_exp eval e d" |
  "set (bn as) \<sharp>* d \<Longrightarrow>
    compatible_with_exp eval (Let as body) d =
      fmap_restr_l d ` (compatible_with_exp eval body (vars_as_l as @ d) \<inter> compatible_with_heapExtend' (compatible_with_exp eval) eval (vars_as_l as @ d)  (asToHeap as))"
proof-
case goal1 thus ?case
  unfolding compatible_with_exp_graph_def eqvt_def
  apply rule
  apply perm_simp
  apply rule
  done
next
case (goal3 P x)
  show ?case
  proof (cases x)
  case (fields eval e d)
    show ?thesis
      using fields goal3
      apply (rule_tac y=e in exp_assn.exhaust(1))
      apply blast+
      apply (rule_tac y=e and c = d in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton, metis)[1]
      apply (rule_tac y=e and c = d in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton, metis)[1]
      done
  qed
next
apply_end auto
  fix X show X X X X sorry
qed

termination(eqvt) by lexicographic_order


lemma fdom_subpcpo_bot:
  assumes "subpcpo_bot S b" and "x \<in> S"
  shows "fdom x = fdom b"
by (metis assms bottom_of_subpcpo_bot_minimal fmap_below_dom)


lemma True and
  frees_as_to_frees:
  "frees_as as \<subseteq> set d \<Longrightarrow> e \<in> snd ` set (asToHeap as) \<Longrightarrow> frees e \<subseteq> set d"
  by (induct and as arbitrary:d rule:exp_assn.inducts, auto)

lemma cont_if_incomp:
  assumes incomp: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> p a = p b"
  assumes "cont f"  and "cont g"
  shows "cont (\<lambda>x. if p x then f x else g x)"
proof (rule contI)
  case (goal1 Y )
  have [simp]: "\<And> i. p (Y i) = p (\<Squnion>i. Y i)" by (metis `chain Y` incomp is_ub_thelub)
  show ?case  by (auto intro: contE[OF assms(2) goal1] contE[OF assms(3) goal1])
qed

 

lemma ESem_cont: "cont (ESem e)"
proof(induct "ESem" e _ rule:compatible_with_exp.induct[case_names Var Lam App Let])
case (Var e d)
  show "cont (\<lambda>\<rho>. ESem (Var e) \<rho>)" by simp
next
case (App e x d)
  thus "cont (\<lambda> \<rho>. ESem (App e x) \<rho>)" by auto
next
case (Let v e)
  find_theorems cont "if _ then _ else _"
oops

lemma ESem_cont_induct_lemma:
  "frees e \<subseteq> set d \<Longrightarrow>
  nice_domain (compatible_with_exp ESem e d) (fmap_bottom_l d)
  &&&
  cont_on (compatible_with_exp ESem e d) (ESem e)"
proof(induct "ESem" e d rule:compatible_with_exp.induct[case_names Var Lam App Let])
  print_cases
  case (Var  v d)
    case 1 show ?case by (auto simp add: fmap_bottom_l_def intro: cone_above_bottom_is_nice)
    case 2
      have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
      thus ?case by (rule cont_is_cont_on) 
next
  case (App e x d)
    case 1
      hence f: "frees e \<subseteq> set d" by auto
      thus ?case using App by auto

      show "cont_on (compatible_with_exp ESem (App e x) d) (\<lambda> \<rho>. ESem (App e x) \<rho>)"
        apply (subst ESem.simps(2))
        apply (subst compatible_with_exp.simps(3))
        apply (rule subpcpo.cont_comp_cont_on2[OF nice_domain_is_subpcpo[OF App(1)[OF f]] _ _ App(2)[OF f]]) back  
        apply (metis cont_Rep_cfun cont_Rep_cfun2)
        apply (metis cont_Rep_cfun2)
        apply (rule cont_is_cont_on)
        by simp
next
  case (Lam x d e)
    case 1
      hence f: "frees e \<subseteq> set (x # d)" by auto
      
      from Lam(2)[OF f]
      have "nice_domain (fmap_restr_l d ` compatible_with_exp ESem e (x # d)) (fmap_restr_l d (fmap_bottom_l (x#d)))"
        unfolding fmap_restr_l_def
        apply (rule nice_domain_retrict_image)
        apply (rule fmap_below_dom[OF bottom_of_subpcpo_bot_minimal[OF nice_domain_is_subpcpo_bot[OF Lam(2)[OF f]]], unfolded fmap_bottom_l_def, symmetric])
        by auto
      thus nd: ?case using Lam(1)
        apply (auto simp add: fmap_restr_l_def fmap_bottom_l_def)
        by (metis inf_absorb1 subset_insertI)

      have "cont_on (compatible_with_exp ESem (Lam [x]. e) d) (\<lambda> \<rho>.  Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
        thm subpcpo.cont_comp_cont_on[OF nice_domain_is_subpcpo[OF nd]]
        apply (rule subpcpo.cont_comp_cont_on[OF nice_domain_is_subpcpo[OF nd] cont_Rep_cfun2]) 
        thm cont_on_comp[OF nice_domain_is_subpcpo[OF nd] _ cont_is_cont_on[OF fmap_upd_cont[OF cont_id cont_const]]]
        apply (rule cont_on_comp[OF nice_domain_is_subpcpo[OF nd] _ cont_is_cont_on[OF fmap_upd_cont[OF cont_id cont_const]]]) 
        using Lam(1)
        

        sorry
      thus "cont_on (compatible_with_exp ESem (Lam [x]. e) d) (\<lambda> \<rho>. ESem (Lam [x]. e) \<rho>)"
        apply (rule subst[OF subpcpo.cont_on_cong[OF nice_domain_is_subpcpo[OF nd]], rotated])
        apply (rule arg_cong[OF ESem.simps(1)])
        apply (drule fdom_subpcpo_bot[OF nice_domain_is_subpcpo_bot[OF nd]])
        apply (simp add: sharp_Env fmap_bottom_l_def )
        apply (metis Lam(1) finite_set fresh_finite_set_at_base fresh_set)
        done
next
  case (Let as d eval body)
    let "?d'" = "vars_as_l as @ d"
    case 1      
      hence f: "frees body \<subseteq> set ?d'" and f': "frees_as as \<subseteq> set ?d'" by auto 
      have f'': "vars_as as \<subseteq> set ?d'" by auto
      note f''' = frees_as_to_frees[OF f']

      have "nice_domain (compatible_with_exp eval body ?d')  (fmap_bottom_l ?d')"
        by (rule Let(2)[OF f])
      moreover
      have "nice_domain (compatible_with_heapExtend' (compatible_with_exp eval) eval ?d' (asToHeap as)) (fmap_bottom_l ?d')"
        unfolding fmap_bottom_l_def
        apply (rule compatible_with_HeapExtend'_nice_domain)
        by (rule Let(4)[OF _ f''', unfolded fmap_bottom_l_def])
      ultimately
      have "nice_domain
             (compatible_with_exp eval body ?d' \<inter>
               compatible_with_heapExtend' (compatible_with_exp eval) eval ?d' (asToHeap as))
             (fmap_bottom_l ?d')" by (rule nice_domain_inter)
      hence "nice_domain
             (fmap_restr_l d `
              (compatible_with_exp eval body?d' \<inter>
               compatible_with_heapExtend' (compatible_with_exp eval) eval ?d' (asToHeap as)))
             (fmap_restr_l d (fmap_bottom_l ?d'))"
        unfolding fmap_restr_l_def
        apply (rule nice_domain_retrict_image)
        apply (rule fmap_below_dom[OF bottom_of_subpcpo_bot_minimal[OF nice_domain_is_subpcpo_bot[OF Let(2)[OF f]]], unfolded fmap_bottom_l_def, symmetric])
        by auto
      hence "nice_domain
             (fmap_restr_l d `
              (compatible_with_exp eval body?d' \<inter>
               compatible_with_heapExtend' (compatible_with_exp eval) eval ?d' (asToHeap as)))
             (fmap_bottom_l d)"
        unfolding fmap_restr_l_def fmap_bottom_l_def apply auto by (metis inf_sup_absorb sup_commute)
      thus ?case
        apply (subst compatible_with_exp.simps(4)[OF Let(1)])
        .
    case 2 show ?case..
qed

(*

lemma heap_compat_subset:
   "e \<in> snd ` set h \<Longrightarrow> compatible_with_heap h d \<subseteq> compatible_with_exp e d" sorry

lemma compat_fdom [simp]: "\<rho> \<in> compatible_with_heap h d \<Longrightarrow> fdom \<rho> = fdom d" sorry

lemma compatible_with_heap_is_subpcpo:
  "subpcpo (compatible_with_heap h d)" sorry

lemma bottom_is_compatible:
  "fmap_bottom d \<in> compatible_with_exp e (fmap_bottom d)"
  "fmap_bottom d \<in> compatible_with_heap h (fmap_bottom d)" sorry

definition compatible_with_heap_and_env
  where "compatible_with_heap_and_env h eval \<rho> = {\<rho>' . \<rho>' \<in> compatible_with_heap h (fmap_bottom (fdom \<rho> \<union> (fst ` set h))) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>')) }"

lemma compatible_disjoint_is_subpcpo:
  fixes \<rho> :: "Env"
  and eval :: "exp \<Rightarrow> Env \<Rightarrow> Value"
  assumes bot: "compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e (fmap_bottom (fdom \<rho> \<union> fst ` set h))))"
  and e_sub: "\<And> e. e \<in> snd ` set h \<Longrightarrow> subpcpo (compatible_with_exp e (fmap_bottom (fdom \<rho> \<union> fst ` set h)))"
  and e_cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont_on (compatible_with_exp e (fmap_bottom (fdom \<rho> \<union> fst ` set h))) (eval e)"
  shows "subpcpo (compatible_with_heap_and_env h eval \<rho>)" (is "subpcpo ?S")
proof(rule subpcpoI)
  let ?dom = "fmap_bottom (fdom \<rho> \<union> fst ` set h)"
  fix Y :: "nat \<Rightarrow> Env"
  assume "chain Y"
  assume "\<And> i. Y i \<in> ?S"
  show "(\<Squnion> i. Y i) \<in> ?S"
  proof(subst compatible_with_heap_and_env_def, rule,rule)
    show "(\<Squnion> i. Y i) \<in> compatible_with_heap h ?dom"
      using `\<And> i. Y i \<in> ?S`
      by (auto simp add: compatible_with_heap_and_env_def subpcpo.pcpo[OF compatible_with_heap_is_subpcpo] `chain Y`)
    next
    show "compatible_fmap \<rho> (heapToEnv h (\<lambda>e. eval e (\<Squnion> i. Y i))) "
    proof(rule compatible_fmapI)
      fix v
      assume dom1: "v \<in> fdom \<rho>"
      assume dom2: "v \<in> fdom (heapToEnv h (\<lambda>e. eval e (\<Squnion> i. Y i)))"
      hence "v \<in> fst ` set h" by auto
      then obtain e where "(v, e) \<in> set h" and e: "\<And>\<rho>' . the (lookup (heapToEnv h (\<lambda>e. eval e \<rho>')) v) = eval e \<rho>'"
          by (metis lookupHeapToEnvE)
      hence "e \<in> snd ` set h" by (metis imageI snd_conv)
      then interpret subpcpo "compatible_with_exp e ?dom" by (rule e_sub)

      from `chain Y` and `\<And> i. Y i \<in> ?S`
      have "chain_on (compatible_with_exp e ?dom) Y"
        by (auto intro: chain_onI chainE[OF `chain Y`] subsetD[OF heap_compat_subset[OF `e \<in> _`]] simp add: compatible_with_heap_and_env_def)

      have "compatible (the (lookup \<rho> v)) (eval e (\<Squnion> i. Y i))"
      thm adm_onD admD
      proof (rule adm_onD)
        fix i
        have "Y i \<in> ?S" by fact
        hence "compatible_fmap \<rho> (heapToEnv h (\<lambda>e. eval e (Y i)))" by (auto simp add: compatible_fmap_def' compatible_with_heap_and_env_def)
        hence "compatible (the (lookup \<rho> v)) (the (lookup (heapToEnv h (\<lambda>e. eval e (Y i))) v))"
          unfolding compatible_fmap_def' using dom1 dom2 by auto
        thus "compatible (the (lookup \<rho> v)) (eval e (Y i))" using e by metis
        next
        show "adm_on (compatible_with_exp e ?dom) (\<lambda>a. compatible (the (lookup \<rho> v)) (eval e a))"
          by (rule adm_on_subst[OF subpcpo_axioms subpcpo_UNIV e_cont[OF `e \<in> _`] subset_UNIV subpcpo.adm_is_adm_on[OF subpcpo_UNIV compatible_adm]])          
      qed fact

      thus "compatible (the (lookup \<rho> v)) (the (lookup (heapToEnv h (\<lambda>e. eval e (\<Squnion> i. Y i))) v))"
        by (auto simp add: e)
    qed
  qed
next
  show "fmap_bottom (fdom \<rho> \<union> (fst ` set h)) \<in> ?S" (is "?bot \<in> _")
    by (auto intro: bottom_is_compatible bot simp add: compatible_with_heap_and_env_def)
  fix y
  assume "y \<in> ?S"
  thus "?bot \<sqsubseteq> y"
    by (auto intro: fmap_bottom_below simp add: compatible_with_heap_and_env_def)
qed
*)

end
