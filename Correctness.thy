theory Correctness
  imports Denotational Launchbury
begin

lemma fdomIff [iff, simp del]: "(a : fdom m) = (lookup m a ~= None)"
 by (transfer, auto)

instantiation fmap :: (type,pcpo) order
begin
  definition "(\<rho>::('a,'b) fmap) \<le> \<rho>' = ((fdom \<rho> \<subseteq> fdom \<rho>') \<and> (\<forall>x \<in> fdom \<rho>. lookup \<rho> x \<noteq> Some \<bottom> \<longrightarrow> lookup \<rho> x = lookup \<rho>' x))"
  definition "(\<rho>::('a,'b) fmap) < \<rho>' = (\<rho> \<noteq> \<rho>' \<and> \<rho> \<le> \<rho>')"

lemma fmap_less_eqI[intro]:
  assumes assm1: "fdom (\<rho>::('a,'b) fmap) \<subseteq> fdom \<rho>'"
    and assm2:  "\<And> x. \<lbrakk> x \<in> fdom \<rho> ; x \<in> fdom \<rho>' ; lookup \<rho> x \<noteq> Some \<bottom> \<rbrakk> \<Longrightarrow> the (lookup \<rho> x) = the (lookup \<rho>' x) "
   shows "\<rho> \<le> \<rho>'"
 unfolding less_eq_fmap_def
 apply rule
 apply fact
 apply rule+
 apply (frule subsetD[OF `_ \<subseteq> _`])
 apply (frule (2) assm2)
 apply auto
 done

lemma fmap_less_eqD:
  assumes "(\<rho>::('a,'b) fmap) \<le> \<rho>'"
  assumes "x \<in> fdom \<rho>"
  assumes "lookup \<rho> x \<noteq> Some \<bottom>"
  shows "lookup \<rho> x = lookup \<rho>' x"
  using assms
  unfolding less_eq_fmap_def by auto


lemma fmap_antisym: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> x" shows "x = y "
proof(rule fmap_eqI[rule_format])
    show "fdom x = fdom y" using `x \<le> y` and `y \<le> x` unfolding less_eq_fmap_def by auto
    
    fix v
    assume "v \<in> fdom x"
    hence "v \<in> fdom y" using `fdom _ = _` by simp

    { assume "lookup x v \<noteq> Some \<bottom>"
      hence "the (lookup x v) = the (lookup y v)"
        using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by simp
    }
    moreover
    { assume "lookup y v \<noteq> Some \<bottom>"
      hence "the (lookup x v) = the (lookup y v)"
        using `y \<le> x` `v \<in> fdom y` unfolding less_eq_fmap_def by simp
    }
    ultimately
    show "the (lookup x v) = the (lookup y v)"
      using `v \<in> fdom x` `v \<in> fdom y`
      by (auto, blast)
  qed

lemma fmap_trans: assumes  "(x:: ('a,'b) fmap) \<le> y" and "y \<le> z" shows "x \<le> z"
proof
  show "fdom x \<subseteq> fdom z" using `x \<le> y` and `y \<le> z` unfolding less_eq_fmap_def
    by -(rule order_trans [of _ "fdom y"], auto)
  
  fix v
  assume "v \<in> fdom x" and "v \<in> fdom z"
  hence "v \<in> fdom y" using `x \<le> y`  unfolding less_eq_fmap_def by auto
  assume "lookup x v \<noteq> Some \<bottom>"
  hence "lookup y v = lookup x v"
    using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by auto
  moreover
  hence "lookup y v \<noteq> Some \<bottom>"
    using `lookup x v \<noteq> Some \<bottom>` by simp
  hence "lookup y v = lookup z v"
    by (rule fmap_less_eqD[OF `y \<le> z`  `v \<in> fdom y`])
  ultimately
  show "the (lookup x v) = the (lookup z v)" by auto
qed

instance
  apply default
  using fmap_antisym apply (auto simp add: less_fmap_def)[1]
  apply (auto simp add: less_eq_fmap_def)[1]
  using fmap_trans apply assumption
  using fmap_antisym apply assumption
  done
end

lemma HSem_fresh[simp]:
  assumes "atom x \<sharp> \<Gamma>"
  and "atom x \<sharp> \<rho>"
  shows "atom x \<sharp> \<lbrace>\<Gamma>\<rbrace>\<rho>" sorry

lemma[simp]: "S \<sharp>* \<rho> \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> the (lookup \<rho> y))" sorry

lemma[simp]: "fmap_bottom {} = fempty"
  by (rule, auto)

lemma[simp]: "(fix1 x (\<Lambda> _. x)) = x"
  by (rule fix1_ind, auto)

lemma [simp]: "fmap_update \<rho> fempty = \<rho>"
  by (transfer, auto)

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  unfolding HSem_def' heapToEnv.simps by auto


lemma[simp]:  "\<lbrakk> atom x \<sharp> \<rho> ; set (bn assn) \<sharp>* x  \<rbrakk> \<Longrightarrow> atom x \<sharp> \<lbrace>asToHeap (subst_assn assn x y)\<rbrace> \<rho>"
  unfolding sharp_Env
  sorry

lemma fresh_fmap_upd[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom a \<sharp> x ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)" sorry
lemma fresh_fmap_upd'[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom x \<sharp> a ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)" sorry

lemma [simp]: "a \<sharp> \<rho> \<Longrightarrow> a \<sharp> the (lookup \<rho> z)" sorry

lemma fmap_upd_twist: "a ~= c ==> (m(a f\<mapsto> b))(c f\<mapsto> d) = (m(c f\<mapsto> d))(a f\<mapsto> b)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply rule
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

lemma the_lookup_fmap_upd_other'[simp]:
  "atom x \<sharp> (y::var) \<Longrightarrow> the (lookup (\<rho>(x f\<mapsto> v)) y) = the (lookup \<rho> y) "
  by (auto simp add:fresh_at_base)
 
lemma [simp]:"atom x \<sharp> x \<longleftrightarrow> False" by (metis fresh_at_base(2))

lemma fdom_pred_adm[intro]: "adm (\<lambda> a. P (fdom a))" 
  by (rule admI, metis chain_fdom(2))

lemma fdom_fix1[simp]: assumes "x \<sqsubseteq> F\<cdot>x" shows "fdom (fix1 x F) = fdom x"
  apply (rule fix1_ind[OF fdom_pred_adm refl assms])
  using  fmap_below_dom[OF monofun_cfun_arg[of x _ F]]  fmap_below_dom[OF assms]
  by auto

lemma fmap_bottom_below[simp]:
  "S = fdom \<rho> \<Longrightarrow> fmap_bottom S \<sqsubseteq> \<rho>"
 by(rule fmap_belowI, auto)

lemma [simp]:"fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fst ` set \<Gamma> \<union> fdom \<rho>"
  by (subst HSem_def', auto)

lemma [simp]: "fst ` set (asToHeap as) = assn_vars as"
  by (induct as rule:asToHeap.induct, auto)

lemma [simp]: "set (bn as) \<sharp>* x \<Longrightarrow> assn_vars as[x::a=y] = assn_vars as"
  by (induct as rule:assn_vars.induct, auto simp add: exp_assn.bn_defs fresh_star_insert)

lemma fix1_cong: 
  assumes "a \<sqsubseteq> F \<cdot> a" and "a \<sqsubseteq> G \<cdot> a"
      and "\<And> x. fdom x = fdom a \<Longrightarrow> F\<cdot>x = G\<cdot>x"
  shows "fix1 a F = fix1 a G"
  apply (rule parallel_fix1_ind[OF _ assms(1) assms(2) refl])
  apply auto[1]
  by (metis fmap_below_dom assms(3))

lemma fmap_update_upd_swap: 
  "x \<notin> fdom \<rho>' \<Longrightarrow> fmap_update (\<rho>(x f\<mapsto> z)) \<rho>' = (fmap_update \<rho> \<rho>')(x f\<mapsto> z)"
  apply (rule fmap_eqI[rule_format])
  apply auto[1]
  apply (case_tac "x = xa")
  apply auto[1]
  apply (case_tac "xa \<in> fdom \<rho>'")
  apply (auto)
  done

lemma the_lookup_HSem_other:
  "y \<notin> fst ` set h \<Longrightarrow> the (lookup (\<lbrace>h\<rbrace>\<rho>) y) = the (lookup \<rho> y)"
  unfolding HSem_def'
  by (induct rule:fix1_ind, auto)

lemma ESem_subst: "atom x \<sharp> \<rho> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "atom x \<sharp> \<rho> \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> the (lookup \<rho> y))\<^esub>)
                    = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
proof (nominal_induct e and as  avoiding: \<rho> x y rule:exp_assn.strong_induct)
case (Var var \<rho> x y) thus ?case by auto
next
case (App exp var \<rho> x y) thus ?case by auto
next
case (Let as exp \<rho> x y)
  from `set (bn as) \<sharp>* x` `set (bn as) \<sharp>* y` 
  have "x \<notin> assn_vars as " "y \<notin> assn_vars as "
    by (induct as rule: assn_vars.induct, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"assn_vars (as[x::a=y]) = assn_vars as" 
     by (induct as rule: assn_vars.induct, auto)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>(x f\<mapsto> the (lookup \<rho> y))  = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap as)(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y))) \<rho>'a\<^esub>))))"
    apply (subst HSem_def') .. also
  have "... = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap as)(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)(x f\<mapsto> the (lookup (fmap_update \<rho> \<rho>'a) y))\<^esub>))))"
    apply (rule arg_cong)back
    using `x \<notin> _`  `y \<notin> _`
    apply (auto intro: fix1_cong simp add: fmap_update_upd_swap)
    done also
  have "... = fmap_update (\<rho>(x f\<mapsto> the (lookup \<rho> y)))
     (fix1 (fmap_bottom (fst ` set (asToHeap as)))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap (as[x ::a= y]))(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)\<^esub>))))"
      apply (rule arg_cong)back
      apply (rule fix1_cong)
      apply auto[2]
      apply simp
      apply (subst `_ \<Longrightarrow> heapToEnv _ _ = _`)
      using `atom x \<sharp> \<rho>` `x \<notin> assn_vars as`
      apply (auto simp add:sharp_Env)
    done also
  have "... = (fmap_update \<rho>
     (fix1 (fmap_bottom (fst ` set (asToHeap (as[x ::a= y]))))
       (\<Lambda> \<rho>'a. (heapToEnv (asToHeap (as[x ::a= y]))(\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_update \<rho> \<rho>'a)\<^esub>)))))(x f\<mapsto> the (lookup \<rho> y))"
       using `x \<notin> assn_vars as` by (auto simp add: fmap_update_upd_swap) also
  have "... = (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) (x f\<mapsto> the (lookup \<rho> y))"
    by (subst HSem_def', simp) also
  have "... = (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) (x f\<mapsto> the (lookup (\<lbrace> asToHeap as[x ::a= y]\<rbrace>\<rho>) y))"
    using `y \<notin> assn_vars as`
    by (auto simp add: the_lookup_HSem_other)
  finally
  have "\<lbrace>asToHeap as\<rbrace>(\<rho>(x f\<mapsto> the (lookup \<rho> y))) = (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>)(x f\<mapsto> the (lookup (\<lbrace>asToHeap (as[x ::a= y])\<rbrace>\<rho>) y))" .
  with Let
  show ?case
  by (auto simp add: fresh_star_Pair)
next
case (Lam var exp \<rho> x' y) thus ?case
  apply (auto simp add: fresh_star_Pair)
  apply (subst fmap_upd_twist)
  apply (auto)[1]
  apply (rule cfun_eqI) 
  apply (erule_tac x = "x'" in meta_allE)
  apply (erule_tac x = "\<rho>(var f\<mapsto> x)" in meta_allE)
  apply (erule_tac x = "y" in meta_allE)
  apply (auto simp add: pure_fresh )[1]
  done
next
case (ANil \<rho> x y) thus ?case by auto
next
case(ACons var exp as \<rho> x y)  thus ?case by auto
qed


theorem correctness:
  assumes "\<Gamma> : e \<Down> \<Delta> : z"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  using assms
thm reds.strong_induct
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
print_cases
case (Lambda \<Gamma> x e)
  case 1 show ?case by simp
  case 2 show ?case by simp
next
case (Application y \<Gamma> e x \<Delta> \<Theta> z e') case 1
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    sorry also
  have "... = (\<Lambda> v. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> v)\<^esub>)\<cdot>(\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` by simp also
  have "... = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> (\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))\<^esub>"
    by simp also
  have "... = \<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` by -(rule ESem_subst, simp) also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>_\<^esub> = _` by simp
  finally
  show ?case .
  case 2 show ?case using `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> _` `\<lbrace>\<Delta>\<rbrace>\<rho> \<le> _`  by simp
next


oops

end


