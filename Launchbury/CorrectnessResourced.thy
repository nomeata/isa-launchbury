theory CorrectnessResourced
  imports "ResourcedDenotational" Launchbury
begin

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds.strong_induct)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  hence "y \<noteq> x" by (simp_all add: fresh_at_base)

  have Gamma_subset: "domA \<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Application.hyps(8)])

  case 1
  hence prem1: "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set (x#L)" by auto

  from 1 Gamma_subset have *: "x \<in> set L \<or> x \<in> domA \<Delta>" by auto

  have "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> (fv (\<Delta>, Lam [y]. e') - domA \<Delta>) \<union> {x}"
    by (auto dest!: set_mp[OF fv_subst_subset])
  also have "\<dots> \<subseteq> (fv (\<Gamma>, e) - domA \<Gamma>) \<union> {x}"
    using new_free_vars_on_heap[OF Application.hyps(8)] by auto
  also have "\<dots> \<subseteq> set L \<union> {x}" using prem1 by auto
  finally have "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> set L \<union> {x}". 
  with *
  have prem2: "fv (\<Delta>, e'[y::=x]) - domA \<Delta> \<subseteq> set L" by auto
  
  have *: "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> domA \<Gamma>")
    case True
    thus ?thesis
      using fun_belowD[OF Application.hyps(10)[OF prem1], where \<rho>1 = \<rho> and x = x]
      by simp
  next
    case False 
    from False reds_avoids_live[OF Application.hyps(8)]
    show ?thesis by (simp add: lookup_HSem_other)
  qed

  have "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<cdot>r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<cdot>r)"
    using Application.hyps(9)[OF prem1]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<cdot>r)"
    by (intro monofun_cfun_arg monofun_cfun_fun monofun_LAM *) simp_all
  also have "\<dots> = (\<Lambda> (C\<cdot>r). ((case r of C\<cdot>r \<Rightarrow> CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v|\<^bsub>r\<^esub>)\<^esub>)|\<^bsub>r\<^esub>)) \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<cdot>r)"
    by simp
  also have "\<dots> \<sqsubseteq>  (\<Lambda> (C\<cdot>r). (CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v|\<^bsub>r\<^esub>)\<^esub>)|\<^bsub>r\<^esub>) \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<cdot>r)"
    apply (rule cfun_belowI)
    apply (case_tac xa, simp)
    apply simp
    apply (case_tac Ca, simp)
    apply simp
    apply (rule monofun_cfun[OF cont2monofunE[OF _ below_C] below_C])
    apply simp
    done
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x|\<^bsub>r\<^esub>)\<^esub>)\<cdot>r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)\<^esub>) \<cdot> r)"
    apply (rule cont2monofunE[OF _ _]) back
    apply simp
    apply (rule cfun_belowI)
    apply simp
    apply (rule cont2monofunE[OF _ C_restr_below], simp)
    done
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>) \<cdot> r)"
    by (rule arg_cong[OF ESem_subst[OF `y \<noteq> x`]])
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    by (subst eta_cfun, rule C_case_below)
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    by (rule Application.hyps(12)[OF prem2])
  finally
  show ?case.
  
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)  f|` (domA \<Gamma>)"
    using Application.hyps(10)[OF prem1]
          fmap_restr_below_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule below_trans)
next
case (Variable \<Gamma> x e L \<Delta> z)
  hence [simp]:"x \<in> domA \<Gamma>"
    by (metis domA_from_set map_of_is_SomeD)

  case 2

  have "x \<notin> domA \<Delta>"
    by (rule reds_avoids_live[OF Variable.hyps(2)], simp_all)

  have subset: "domA (delete x \<Gamma>) \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Variable.hyps(2)])

  have "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF `map_of \<Gamma> x = Some e`])
  hence prem: "fv (delete x \<Gamma>, e) - domA (delete x \<Gamma>) \<subseteq> set (x # L)" using 2 by auto

  have fv_subset: "fv (delete x \<Gamma>, e) - domA (delete x \<Gamma>) \<subseteq> - (domA \<Delta> - domA \<Gamma>)"
    apply (rule subset_trans[OF prem])
    apply (rule subset_trans[OF reds_avoids_live'[OF Variable.hyps(2)]])
    by auto

  let "?new" = "domA \<Delta> - domA \<Gamma>"
  have "domA \<Gamma> \<subseteq> (-?new)" by auto

  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF map_of_delete_insert[symmetric, OF Variable(1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) \<sqsubseteq> (...) f|` (- ?new)" by (rule ssubst) (rule below_refl)
  also have "\<dots> \<sqsubseteq> (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) \<sqsubseteq> y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)"
      using fv_subset by (auto intro: ESem_fresh_cong_below HSem_fresh_cong_below  fmap_restr_below_subset[OF _ 3])
    from below_trans[OF this(1) Variable(3)[OF prem]] below_trans[OF this(2) Variable(4)[OF prem]]
    have  "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)".
    thus ?case
      using subset
      by (auto intro!: fun_belowI simp add: lookup_override_on_eq  lookup_fmap_restr_eq elim: fmap_restr_belowD)
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF `x \<notin> domA \<Delta>`])
  also have "\<dots> = (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF `x \<notin> domA \<Delta>`])
  finally
  show le: ?case by (rule fmap_restr_below_subset[OF `domA \<Gamma> \<subseteq> (-?new)`])

  have "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    apply (rule cfun_belowI)
    apply (case_tac xa)
    apply simp
    using fun_belowD[OF le, where x = x]
    apply (simp add: monofun_cfun_fun)
    done
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    apply (rule cfun_belowI)
    apply (case_tac xa)
    apply (auto simp add: lookup_HSem_heap  monofun_cfun_arg[OF below_C])
    done
  finally
  show "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>".
next
case (Let as \<Gamma> L body \<Delta> z)
  case 1
  { fix a
    assume a: "a \<in> domA (asToHeap as)"
    have "atom a \<sharp> \<Gamma>" 
      by (rule Let(1)[unfolded fresh_star_def set_bn_to_atom_domA, rule_format, OF imageI[OF a]])
    hence "a \<notin> domA \<Gamma>"
      by (metis domA_not_fresh)
  }
  note * = this

  
  have "fv (asToHeap as @ \<Gamma>, body) - domA (asToHeap as @ \<Gamma>) \<subseteq>  fv (\<Gamma>, Let as body) - domA \<Gamma>"
    by auto
  with 1 have prem: "fv (asToHeap as @ \<Gamma>, body) - domA (asToHeap as @ \<Gamma>) \<subseteq> set L" by auto
  
  have f1: "atom ` domA (asToHeap as) \<sharp>* \<Gamma>"
    using Let(1) by (simp add: set_bn_to_atom_domA)

  have "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    apply (rule cfun_belowI)
    apply (case_tac x)
    apply (simp_all add: monofun_cfun_arg[OF below_C])
    done
  also have "\<dots> =  \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq>  \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF prem])
  finally
  show ?case.

  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>asToHeap as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (domA \<Gamma>)"
    apply (rule fun_belowI)
    apply (case_tac "x \<in> domA (asToHeap as)")
    apply (auto simp add: lookup_HSem_other lookup_fmap_restr_eq *)
    done
  also have "\<dots> = (\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
    by (rule fmap_restr_below_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>".
qed


corollary correctness_empty_env:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>"
proof-
  from assms(2) have "fv (\<Gamma>, e) - domA \<Gamma> \<subseteq> set L" by auto
  note corr =  correctness[OF assms(1) this, where \<rho> = "\<bottom>"]

  show "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" using corr(1).

  have "\<N>\<lbrace>\<Gamma>\<rbrace> = (\<N>\<lbrace>\<Gamma>\<rbrace>) f|` domA \<Gamma> "
    using fmap_restr_useless[OF HSem_fdom_subset, where \<rho>1 = "\<bottom>"] by simp
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>) f|` domA \<Gamma>" using corr(2).
  also have "\<dots> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by (rule fmap_restr_below_itself)
  finally show "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>".
qed

end
