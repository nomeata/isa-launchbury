theory Denotational
  imports "Denotational-Common"
begin

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>heapExtendMeet \<rho> (asToHeap as) ESem\<^esub>"
proof-
case goal1 thus ?case
  unfolding eqvt_def ESem_graph_def
  apply rule
  apply perm_simp
  apply rule
  done
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Pair e \<rho>)
    show ?thesis 
      using Pair goal3
      apply (rule_tac y=e in exp_assn.exhaust(1))
      apply auto[1]
      apply blast
      prefer 2
      apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      done
  qed
next

case (goal4 x \<rho> e x' \<rho>' e')
  have all_fresh: "(atom x' \<rightleftharpoons> atom x) \<bullet> \<rho>' = \<rho>'" 
    using goal4
    by (auto simp add: swap_fresh_fresh)

  have tmp: "\<And> xa. ESem_sumC (e, (\<rho>(x f\<mapsto> xa))) = ESem_sumC (e', (\<rho>'(x' f\<mapsto> xa)))"
    using goal4
    apply (auto simp add: Abs1_eq_iff')

    apply (erule_tac x = xa in meta_allE)
    apply (erule_tac x = xa in meta_allE)
    apply (simp only: eqvt_at_def)
    apply auto

    apply (erule_tac x = "(atom x' \<rightleftharpoons> atom x)" in allE)
    apply (auto simp add: fmap_upd_eqvt permute_Value_def all_fresh)
    done
   thus ?case by simp
next

case (goal13 as \<rho> body as' \<rho>' body')
  assume eqvt1: "\<And> e x. e \<in> snd ` set (asToHeap as) \<Longrightarrow> eqvt_at ESem_sumC (e, x)"
    and eqvt2:"eqvt_at ESem_sumC (body, heapExtendMeet \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
    and eqvt3:"\<And>e x. e \<in> snd ` set (asToHeap as') \<Longrightarrow> eqvt_at ESem_sumC (e, x)"
    and eqvt4:"eqvt_at ESem_sumC (body', heapExtendMeet \<rho>' (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"

  assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
  assume "(Terms.Let as body, \<rho>) =  (Terms.Let as' body', \<rho>')"
  hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

  have "ESem_sumC (body, heapExtendMeet \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
        ESem_sumC (body', heapExtendMeet \<rho> (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
    apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem_sumC (body, heapExtendMeet \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))))" , OF tmp, simplified])
    apply (rule pure_fresh)+
    apply (erule conjE)
    using fresh2[unfolded rho]
    proof-
      fix \<pi>
      assume body: "\<pi> \<bullet> body = body'"
      assume as: "\<pi> \<bullet> as = as'"
      assume "set (bn as') \<sharp>* \<rho>" with fresh1
      have "(set (bn as) \<union> set (bn as')) \<sharp>* \<rho>" by (metis fresh_star_Un)
      moreover
      assume "supp \<pi> \<subseteq> set (bn as) \<union> set (bn as')"
      ultimately
      have "\<pi> \<bullet> \<rho> = \<rho>"
        using as
        apply -
        apply (rule perm_supp_eq)
        apply (auto intro: perm_supp_eq simp add: fresh_star_def)
        done            
      thus "\<pi> \<bullet> ESem_sumC (body, heapExtendMeet \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
             ESem_sumC (body', heapExtendMeet \<rho> (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
         using as body         
         apply (simp add: eqvt2[unfolded eqvt_at_def, simplified, rule_format]   asToHeap.eqvt heapExtendMeet_eqvt)
         apply (subst heapExtendMeet_cong)
         prefer 4
         apply (rule refl)+
         apply (simp add: permute_fun_def)
         apply rule
         apply (subst eqvt1[unfolded eqvt_at_def, simplified, rule_format])
         defer
         apply simp
         apply (subst mem_permute_iff[symmetric, of _ _ "\<pi>"])
         apply (simp add: image_eqvt)
         apply perm_simp
         using as
         apply simp
         done
    qed
  thus "ESem_sumC (body, heapExtendMeet \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
      ESem_sumC (body', heapExtendMeet \<rho>' (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))" using `\<rho>' = \<rho>`  by simp
qed auto

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by(induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order


lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and True
proof(nominal_induct e and avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (ESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    by (intro cont2cont cont_compose[OF `cont (ESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (ESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ Var.prems(2)])    
next
case (Let as e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)
  show ?case
    by (simp, intro contE[OF _ Let.prems(2)] cont2cont cont_compose[OF `cont (ESem e)`])
qed simp

lemma ESem_cont: "cont (ESem e)"  using ESem_cont'[OF refl] by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]


definition HSem ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> = heapExtend \<rho> \<Gamma> ESem"

lemma Esem_simps4[simp]: "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as \<rbrace>\<rho>\<^esub>"
  by (simp add: HSem_def)
lemma HSem_def': "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_update \<rho> (fix1 (fmap_bottom (fst ` set \<Gamma>)) (\<Lambda> \<rho>'. heapToEnv \<Gamma> (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>fmap_update \<rho> \<rho>'\<^esub>))) "
  unfolding HSem_def heapExtend_def by simp
declare ESem.simps(4)[simp del]

lemma HSem_cont2: "cont (\<lambda>y. HSem \<Gamma> y)"
  unfolding HSem_def' by auto

lemmas HSem_cont2cont[cont2cont,simp] = cont_compose[OF HSem_cont2]

lemma HSem_eqvt[eqvt]: "\<pi> \<bullet> (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<lbrace>\<pi> \<bullet> \<Gamma>\<rbrace>(\<pi> \<bullet> \<rho>)"
  unfolding HSem_def
  by (perm_simp, rule)

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  unfolding HSem_def' heapToEnv.simps by auto

lemma HSem_def'': "\<lbrace>\<Gamma>\<rbrace>\<rho> = fix1 (fmap_update \<rho> (fmap_bottom (fst ` set \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)))"
  unfolding HSem_def'
  apply (rule parallel_fix1_ind)
  by (auto intro: cont2monofunE[OF fmap_update_cont2])


lemma HSem_def''': "\<lbrace>\<Gamma>\<rbrace>\<rho> = fix1 ((fmap_bottom (fdom \<rho> \<union> fst ` set \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)))"
  unfolding HSem_def''
  apply (rule fix1_alt_start[symmetric])
  apply auto[1]
  apply simp
  apply (rule cont2monofunE[OF fmap_update_cont2])
  apply simp
  done

lemma [simp]:"fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fdom \<rho> \<union> fst ` set \<Gamma>"
  unfolding HSem_def' by auto

lemma [simp]: "x \<notin> fst ` set \<Gamma> \<Longrightarrow> lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x = lookup \<rho> x"
  unfolding HSem_def' by auto


lift_definition fmap_restr :: "'a set \<Rightarrow> ('a, 'b) fmap => ('a, 'b) fmap"
  is "\<lambda> S m. (if finite S then (restrict_map m S) else empty)" by auto

lemma lookup_fmap_restr: "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> the (lookup (fmap_restr S m) x) = the (lookup m x)"
  by (transfer, auto)

lemma [transfer_rule]:"(op = ===> set_rel op = ===> op =) op = op ="
  unfolding set_rel_eq fun_rel_eq by (rule refl)

lemma [transfer_rule]: "(op = ===> set_rel op = ===> set_rel op =) op \<inter> op \<inter> "
  unfolding set_rel_eq fun_rel_eq by (rule refl)

lemma fdom_fmap_restr[simp]: "finite S \<Longrightarrow> fdom (fmap_restr S m) = fdom m \<inter> S"
  by (transfer, simp)

lemma fdom_fmap_restr_Hsem[simp]: "fdom (fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>')) = fst ` set \<Gamma>"
  by auto

lemma fmap_restr_cont:  "cont (fmap_restr S)" sorry
lemmas fmap_restr_cont2cont[simp,cont2cont] = cont_compose[OF fmap_restr_cont]



lemma fmap_upd_fix1: 
  assumes above: "x0 \<sqsubseteq> F\<cdot>x0"
    and permute: "\<And>z. (F\<cdot>z)(x f\<mapsto> y) = F\<cdot>(z(x f\<mapsto> y))"
    shows "(fix1 x0 F) (x f\<mapsto> y) = fix1 (x0 (x f\<mapsto> y)) (\<Lambda> z. (F\<cdot>z)(x f\<mapsto> y))"
  apply (rule parallel_fix1_ind)
  apply auto[1]
  apply (rule above)
  apply simp
  apply (subst permute[symmetric])
  apply simp
  apply (rule cont2monofunE[OF fmap_upd_cont[OF cont_id cont_const]])
  apply (rule above)
  apply (rule refl)
  apply simp
  apply (subst (1 2) permute)
  apply (rule cfun_arg_cong[of _ _ F])
  apply (drule sym)
  apply simp
  done

lemma fmap_update_fix1: 
  assumes above: "x0 \<sqsubseteq> F\<cdot>x0"
    and permute: "\<And>z. fmap_update \<rho> (F\<cdot>z) = F \<cdot> (fmap_update \<rho> z)"
    shows "fmap_update \<rho> (fix1 x0 F) = fix1 (fmap_update \<rho> x0) (\<Lambda> z. fmap_update \<rho> (F\<cdot>z))"
  apply (rule parallel_fix1_ind)
  apply auto[1]
  apply (rule above)
  apply simp
  apply (subst permute[symmetric])
  apply simp
  apply (rule cont2monofunE[OF fmap_update_cont2cont[OF cont_const cont_id]])
  apply (rule above)
  apply (rule refl)
  apply simp
  apply (subst (1 2) permute)
  apply (rule cfun_arg_cong[of _ _ F])
  apply (drule sym)
  apply simp
  done


lemma tmp:"fmap_update \<rho> ((iterate i F) \<cdot> x) = (iterate i (\<Lambda> x. fmap_update \<rho> (F \<cdot> x))) \<cdot> (fmap_update \<rho> x)" sorry

lemmas tmp2 =  cont2contlubE[of "\<lambda> y. (iterate i (\<Lambda> \<rho>'. fmap_update \<rho> ((y)(x f\<mapsto> G \<rho>'))))\<cdot>x0", standard]
thm tmp2


lemma  fmap_update_belowI:
  assumes "fdom x \<union> fdom y = fdom z"
  and "\<And> a. a \<in> fdom y \<Longrightarrow> the (lookup y a) \<sqsubseteq> the (lookup z a)"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> a \<notin> fdom y \<Longrightarrow> the (lookup x a) \<sqsubseteq> the (lookup z a)"
  shows  "fmap_update x y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI)
  apply auto[1]
  by (metis fdomIff lookup_fmap_update1 lookup_fmap_update2 the.simps)

lemma HSem_unroll: "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_update \<rho> (heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>))"
  apply(subst (1 2) HSem_def''')
  apply(subst fix_eq)
  apply auto
  done

lemma iterative_HSem:
  assumes "x \<notin> fst ` set \<Gamma>"
  shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x,e) # \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))(x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)))" (is "_ = fix1 _ ?R")
apply (subst HSem_def''')
proof(rule below_antisym)
  let "fix1 ?x0 ?L" = "fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # \<Gamma>))) (\<Lambda> \<rho>'. fmap_update \<rho> (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)))"

  have "?x0 \<sqsubseteq> ?L\<cdot>?x0"
    by (auto intro: cont2monofunE[OF fmap_update_cont2])
  (* have "?x0 \<sqsubseteq> ?R\<cdot>?x0" 
    apply (rule fmap_bottom_below)
    by (auto)*)
  have "?x0 \<sqsubseteq> ?R\<cdot>?x0" 
    by simp

{
  show "fix1 ?x0 ?L \<sqsubseteq> fix1 ?x ?R"
  proof(rule fix_least_below[OF `?x0 \<sqsubseteq> ?L\<cdot>?x0`])
    let "?y" = "fix1 ?x ?R"
    show  "?x0 \<sqsubseteq> ?y"
      apply (rule start_below_fix1)
      apply (rule fmap_bottom_below)
      apply auto
      done

    have large_fdom[simp]: "fdom ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) = insert x (fst ` set \<Gamma>)"
      by simp

    have "?L\<cdot>?y \<sqsubseteq> ?R\<cdot>?y"
    proof (rule fmap_belowI')
      show "fdom (?L\<cdot>?y) = fdom (?R\<cdot>?y)" using fmap_below_dom[OF `?x0 \<sqsubseteq> ?y`] by auto
    next
      fix x'
      assume "x' \<in> fdom (?L\<cdot>?y)" and "x' \<in> fdom (?R\<cdot>?y)"
      show "the (lookup (?L\<cdot>?y) x') \<sqsubseteq> the (lookup (?R\<cdot>?y) x')"
      proof (cases "x' = x")
        case True thus ?thesis by auto
      next
        case False note F1 = this thus ?thesis
        proof (cases "x' \<in> fdom (heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>))")
        case True
          moreover
          hence "x' \<in> fdom ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>))" by auto
          moreover
          hence "x' \<in> fst ` set \<Gamma>" using F1 by auto
          moreover
          {
            (*
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x')  \<sqsubseteq>
              the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>)\<^esub>))\<^esub>)) x') "
              
              sorry
            also have "... \<sqsubseteq> the (lookup (fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>)\<^esub>))\<^esub>))) x')"
              using `x' \<in> fst \` set \<Gamma>` by simp
            also have "... = the (lookup (iterate (Suc 1) (\<Lambda> \<rho>'. fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)))\<cdot>(fmap_bottom (fdom ?y \<union> fst ` set \<Gamma>))) x')"
                (is "_ = the (lookup ?rhs _)")
              by simp
            also
            have "?rhs \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              unfolding HSem_def'''
              by (rule iterate_below_fix[of _ _ "Suc 1"], simp)
            have "?rhs \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              unfolding HSem_def'''
              by (rule iterate_below_fix[of _ _ "Suc 1"], simp)
            hence "the (lookup ?rhs x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')"
              apply (subst lookup_fmap_restr[OF _ `x' \<in> fst \` set \<Gamma>`])
              apply auto[1]              
              by (rule fmap_belowE)
            finally
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')".

            have "fmap_update ?y (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>?y"
              thm fix1_ind
              apply (rule fix1_ind[OF _ _ `?x0 \<sqsubseteq> ?R\<cdot>?x0`]) back back back back back
              apply auto[1]

              (* Base case *)
              apply (subst (2) HSem_unroll)
              apply (rule cont2monofunE) back back              
              apply auto[1]
              apply (rule fmap_bottom_below)
              apply auto[1]

              apply (subst (3) HSem_unroll)
              apply simp
              apply (rule cont2monofunE) back back
              apply auto[1]
              apply (erule rev_below_trans)
              




            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ((fmap_restr (fst ` set \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>?y))) x')"
              using  `x' \<in> fst \` set \<Gamma>`  `x' \<noteq> x`
              apply (subst (2) HSem_def'')
              apply simp
              apply (subst lookup_fmap_restr[OF _ `x' \<in> fst \` set \<Gamma>`])
              apply simp
              apply (rule fix1_ind) back
              defer
              apply (subst fix_eq)
              apply auto[1]
              apply simp
              apply (rule cont2monofunE) back back back
              apply simp
              apply (rule fmap_bottom_below)
              apply auto[1]
              apply (rule fmap_bottom_below)
              apply auto[1]
              
              apply (subst fix_eq) apply auto[1]
              
              apply simp
              apply (rule cont2monofunE) back back back 
              apply simp
              apply auto[1]
              thm fmap_belowE[OF below_trans[OF _ iterate_below_fix[of _ _ "1", simplified]]]
              apply (rule  fmap_belowE[OF below_trans[OF _ iterate_below_fix[of _ _ "1", simplified]]])
              apply simp
              find_theorems "fix"
              apply (subst (3) fix_eq)
              apply auto[1]
              apply simp
              sorry
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup ?y x')" sorry
            *)
            have "the (lookup (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>?y\<^esub>)) x') \<sqsubseteq> the (lookup (?R \<cdot> ?y) x')" sorry
          }
          ultimately
          show ?thesis using `x' \<noteq> x` by simp
        next
        case False with F1 show ?thesis by auto
        qed
      qed
    qed
    thus "?L\<cdot>?y \<sqsubseteq> ?y"
      apply (subst (asm)  fix_eq[symmetric])
      by (auto intro!:fmap_bottom_below)
  qed
next
  show "fix1 ?x0 ?R \<sqsubseteq> fix1 ?x0 ?L"
  proof (rule fix_least_below[OF `?x0 \<sqsubseteq> ?R\<cdot>?x0`])
    show "?x0 \<sqsubseteq> fix1 ?x0 ?L" by (rule start_below_fix1[OF `?x0 \<sqsubseteq> ?L\<cdot>?x0`])
  next
    show "?R\<cdot>(fix1 ?x0 ?L) \<sqsubseteq> fix1 ?x0 ?L"
    proof (rule fmap_belowI')
      show "fdom (?R\<cdot>(fix1 ?x0 ?L)) = fdom (fix1 ?x0 ?L)" by auto
    next
      fix x'
      assume "x' \<in> fdom (?R\<cdot>(fix1 ?x0 ?L))" and "x' \<in> fdom (fix1 ?x0 ?L)"
      show "the (lookup (?R\<cdot>(fix1 ?x0 ?L)) x') \<sqsubseteq> the (lookup ((fix1 ?x0 ?L)) x')"
      proof (cases "x' = x")
      case True thus ?thesis  by (subst (2) fix_eq, auto)
      next
      case False note F1 = this
        show ?thesis
        proof (cases "x' \<in> fst ` set \<Gamma>")
        case True
          from `x \<notin> fst \` set \<Gamma>`
          have "fmap_update (fix1 ?x0 ?L) (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>(fix1 ?x0 ?L)\<^esub>)) \<sqsubseteq> (fix1 ?x0 ?L)"
            apply -
            apply (rule fmap_update_belowI[OF _ _ below_refl])
            apply auto[1]
            apply (subst (2) fix_eq)
            apply auto[1]
            apply (subst beta_cfun)
            apply auto[1]
            apply (subgoal_tac "a \<noteq> x")
            apply auto
            done
          hence "fix1 (fmap_bottom (fdom ((fix1 ?x0 ?L)) \<union> fst ` set ((x, e) # \<Gamma>))) (\<Lambda> y. fmap_update (fix1 ?x0 ?L) (heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>))) \<sqsubseteq> (fix1 ?x0 ?L)"
            apply -
            apply (rule fix_least_below)
            apply (rule fmap_bottom_below)
            apply auto[1]
            apply (rule fmap_bottom_below)
            apply auto
            done
          hence "(\<lbrace>\<Gamma>\<rbrace>(fix1 ?x0 ?L)) \<sqsubseteq> (fix1 ?x0 ?L)"
            unfolding HSem_def'''
            by auto
          with True F1
          show ?thesis
            apply simp
            apply (subst lookup_fmap_restr)
            apply auto[2]
            apply (erule fmap_belowE)
            done
       next
       case False note F2 = this
         with F1 show ?thesis 
          apply (subst (2) fix_eq)
          apply auto[1]
          apply simp
          done
       qed
     qed
   qed
  qed
}
qed


lemma HSem_fdom[simp]:"fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fst ` set \<Gamma> \<union> fdom \<rho>"
  by (subst HSem_def', auto)

lemma the_lookup_HSem_other:
  "y \<notin> fst ` set h \<Longrightarrow> the (lookup (\<lbrace>h\<rbrace>\<rho>) y) = the (lookup \<rho> y)"
  unfolding HSem_def'
  by (induct rule:fix1_ind, auto)


lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt]
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]

lemma fresh_fmap_upd'[simp]: "\<lbrakk> atom a \<sharp> \<rho>; atom x \<sharp> a ; atom a \<sharp> v \<rbrakk> \<Longrightarrow> atom a \<sharp> \<rho>(x f\<mapsto> v)"
  by (metis fresh_at_base(2) fresh_fmap_upd)
  
lemma[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x  \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> the (lookup \<rho> y))"
  apply (auto simp add: fresh_star_def) 
  apply (rule fresh_fmap_upd)
  apply (auto simp add: pure_fresh)
  done    

lemma ESem_subst: "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> \<rho> \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> the (lookup \<rho> y))\<^esub>)
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
      apply (subst `_ \<Longrightarrow> _ \<Longrightarrow> heapToEnv _ _ = _`[OF `x \<noteq> y`])
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
  by (auto simp add: fresh_star_Pair fresh_at_base)
next
case (Lam var exp \<rho> x' y) thus ?case
  apply (auto simp add: fresh_star_Pair pure_fresh)
  apply (subst fmap_upd_twist)
  apply (auto)[1]
  apply (rule cfun_eqI) 
  apply (erule_tac x = "x'" in meta_allE)
  apply (erule_tac x = "y" in meta_allE)
  apply (erule_tac x = "\<rho>(var f\<mapsto> x)" in meta_allE)
  apply (auto simp add: pure_fresh fresh_at_base)[1]
  done
next
case (ANil \<rho> x y) thus ?case by auto
next
case(ACons var exp as \<rho> x y)  thus ?case by auto
qed


end
