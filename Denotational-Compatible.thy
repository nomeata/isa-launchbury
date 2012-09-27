theory "Denotational-Compatible"
  imports "Denotational-Common" "HOLCF-Set-Nominal" "FMap-Nominal-HOLCF"
begin


lemmas fdom_perm_rev[eqvt]

lemma below_eqvt [eqvt]:
    "\<pi> \<bullet> (x \<sqsubseteq> y) = (\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> (y::'a::cont_pt))" by (auto simp add: permute_pure)

nominal_primrec
  compatible_with_exp :: "exp \<Rightarrow> Env \<Rightarrow> Env set" 
  and
  compatible_with_heap :: "heap \<Rightarrow> Env \<Rightarrow> Env set"
where
  "compatible_with_exp (Var v) d = {\<rho>' . d \<sqsubseteq> \<rho>'}" |
  "atom x \<sharp> d \<Longrightarrow> compatible_with_exp (Lam [x]. e) d = compatible_with_exp e d" |
  "compatible_with_exp (App e x) d = compatible_with_exp e d" |
  "compatible_with_exp (Let as body) d = compatible_with_exp body d \<inter> compatible_with_heap (asToHeap as) d" |

  "compatible_with_heap [] d = {\<rho>' . d \<sqsubseteq> \<rho>'}" |
  "compatible_with_heap (x # xs) d = compatible_with_heap xs d" (* TODO. Was hier? *)
proof-
case goal1 thus ?case
  unfolding compatible_with_exp_compatible_with_heap_graph_def eqvt_def
  apply rule
  apply perm_simp
  apply rule
  done
next
case (goal3 P x)
  show ?case
  proof (cases x)
  case (Inl y)
    show ?thesis
    proof(cases y)
    case (Pair e d)
      show ?thesis
      using Inl Pair goal3
        apply (rule_tac y=e in exp_assn.exhaust(1))
        apply blast+
        apply (rule_tac y=e and c = d in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton, metis)[1]
        done
    qed
  next
  case (Inr y)
    show ?thesis
    proof(cases y)
    case (Pair h d)
      show ?thesis
      apply (cases h)
      using Inr Pair goal3
      apply blast+
      done
   qed
qed
next
apply_end auto
next
  fix X show X X X X X X sorry
qed

termination(eqvt) by lexicographic_order

lemma ESem_cont_induct_lemma:
  "subpcpo (compatible_with_exp e d) &&& bottom_of (compatible_with_exp e d) = d"
  and
  "subpcpo (compatible_with_heap (asToHeap as) d) &&& bottom_of (compatible_with_heap (asToHeap as) d) = d"
proof(nominal_induct e and avoiding: d rule:exp_assn.strong_induct)
print_cases
  case (Var v d)
  show "subpcpo (compatible_with_exp (Var v) d)"
    by (simp, rule subpcpo_cone_above)
  show "bottom_of (compatible_with_exp (Var v) d) = d" by simp
next
  case (App e x d)
    case 1 thus ?case using App by auto
    case 2 thus ?case using App by auto
next
  case (Lam x e d)
    case 1 thus ?case using Lam by auto
    case 2 thus ?case using Lam by auto
next
  case (Let as body d)
    case 1 thus ?case
      using Let by (auto intro: subpcpo_inter)
    case 2 thus ?case using Let apply simp by (metis bottom_of_inter)
next
  case ANil
    case 1 thus ?case apply simp
qed

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


end
