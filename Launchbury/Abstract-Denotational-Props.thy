theory "Abstract-Denotational-Props"
  imports "AbstractDenotational"
begin

context semantic_domain
begin

subsubsection {* The semantics ignores fresh variables *}

lemma ESem_considers_fv': "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"
proof (induct e arbitrary: \<rho> rule:exp_induct)
  case Var
  show ?case by simp
next
  have [simp]: "\<And> S x. S \<inter> insert x S = S" by auto
  case App
  show ?case
    by (simp, subst (1 2) App, simp)
next
  case (Lam x e)
  show ?case by simp
next
  case (Let as e)

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>(\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv e)\<^esub>"
    by (subst (1 2) Let(2)) (simp add: sup_commute)
  also
  have "fv (asToHeap as) \<subseteq> fv as \<union> fv e" using fv_asToHeap by auto
  hence "(\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv e) = \<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv e))"
     by (rule HSem_ignores_fresh_restr'[OF _ Let(1)])
  also
  have "\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv e)) = \<lbrace>asToHeap as\<rbrace>\<rho> f|` (fv as \<union> fv e - domA (asToHeap as))"
    by (rule HSem_restr_cong) (auto simp add: lookup_fmap_restr_eq)
  finally
  show ?case by simp
qed

sublocale has_ignore_fresh_ESem ESem
  by default (rule fv_supp_exp, rule ESem_considers_fv')

subsubsection {* Nicer equations for ESem, without freshness requirements *}

lemma ESem_Lam[simp]: "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
proof-
  have *: "\<And> v. ((\<rho> f|` (fv e - {x}))(x := v)) f|` fv e = (\<rho>(x := v)) f|` fv e"
    by (rule ext) (auto simp add: lookup_fmap_restr_eq)

  have "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>fmap_delete x \<rho>\<^esub>"
    by (rule ESem_fresh_cong) simp
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>(\<rho> f|` (fv e - {x}))(x := v)\<^esub>))"
    by simp
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>((\<rho> f|` (fv e - {x}))(x := v)) f|` fv e\<^esub>))"
    by (subst  ESem_considers_fv, rule)
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v) f|` fv e\<^esub>))"
    unfolding *..
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
    unfolding  ESem_considers_fv[symmetric]..
  finally show ?thesis.
qed
declare ESem.simps(1)[simp del]

lemma ESem_Let[simp]: "\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>)"
proof-
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` fv (Let as body))\<^esub>)" 
    by simp
  also have "\<lbrace>asToHeap as\<rbrace>(\<rho> f|` fv(Let as body)) = \<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv body))" 
    by (rule HSem_restr_cong) (auto simp add: lookup_fmap_restr_eq)
  also have "\<dots> = (\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv body)"
    by (rule HSem_ignores_fresh_restr'[symmetric, OF _ ESem_considers_fv]) simp
  also have "\<lbrakk>body\<rbrakk>\<^bsub>\<dots>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule ESem_fresh_cong) (auto simp add: lookup_fmap_restr_eq)
  finally show ?thesis.
qed
declare ESem.simps(4)[simp del]


subsubsection {* Denotation of Substitution *}

lemma ESem_subst_same: "\<rho> x = \<rho> y \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "\<rho> x = \<rho> y  \<Longrightarrow>  heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
proof (nominal_induct e and as avoiding: x y arbitrary: \<rho> and \<rho> rule:exp_assn.strong_induct)
case Var thus ?case by auto
next
case App
  from App(1)[OF App(2)] App(2)
  show ?case by auto
next
case (Let as exp x y \<rho>)
  from `set (bn as) \<sharp>* x` `set (bn as) \<sharp>* y` 
  have "x \<notin> domA (asToHeap as)" "y \<notin> domA (asToHeap as)"
    by (induct as rule: exp_assn.bn_inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"domA (asToHeap (as[x::a=y])) = domA (asToHeap as)" 
     by (induct as rule: exp_assn.bn_inducts, auto)

  from `\<rho> x = \<rho> y`
  have "(\<lbrace>asToHeap as\<rbrace>\<rho>) x = (\<lbrace>asToHeap as\<rbrace>\<rho>) y"
    using `x \<notin> domA (asToHeap as)` `y \<notin> domA (asToHeap as)`
    by (simp add: lookup_HSem_other)
  hence "\<lbrakk>exp\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from `\<rho> x = \<rho> y`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>" and "(\<lbrace>asToHeap as\<rbrace>\<rho>) x = (\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>) y"
    apply (induction rule: parallel_HSem_ind)
    apply (intro adm_lemmas cont2cont cont2cont_fun)
    apply simp
    apply simp
    apply simp
    apply (erule arg_cong[OF Let(3)])
    using `x \<notin> domA (asToHeap as)` `y \<notin> domA (asToHeap as)`
    apply simp
    done
  ultimately
  show ?case using Let(1,2,3) by (simp add: fresh_star_Pair)
next
case (Lam var exp x y \<rho>)
  from `\<rho> x = \<rho> y`
  have "\<And>v. (\<rho>(var := v)) x = (\<rho>(var := v)) y"
    using Lam(1,2) by (simp add: fresh_at_base)
  hence "\<And> v. \<lbrakk>exp\<rbrakk>\<^bsub>\<rho>(var := v)\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<rho>(var := v)\<^esub>"
    by (rule Lam)
  thus ?case using Lam(1,2) by simp
next
case ANil thus ?case by auto
next
case ACons
  from ACons(1,2)[OF ACons(3)] ACons(3)
  show ?case by auto
qed

lemma ESem_subst:
  assumes "x \<noteq> y"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
proof-
  have [simp]: "x \<notin> fv e[x::=y]" using assms by (auto simp add: fv_def supp_subst supp_at_base dest: set_mp[OF supp_subst]) 

  have "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub>"
    using assms(1)
    by (auto intro: ESem_subst_same simp add: Rep_cfun_inverse)
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
    by (rule ESem_fresh_cong) simp
  finally
  show ?thesis.
qed

end

end
