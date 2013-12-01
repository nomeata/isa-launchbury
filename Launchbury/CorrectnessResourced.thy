theory CorrectnessResourced
  imports "ResourcedDenotational" Launchbury
begin

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "distinctVars \<Gamma>"
  and     "fv (\<Gamma>, e) - heapVars \<Gamma> \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (heapVars \<Gamma>)"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds_distinct_strong_ind)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  hence "y \<noteq> x" by (simp_all add: fresh_at_base)

  have Gamma_subset: "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF distinct_redsD1[OF Application.hyps(8)]])

  case 1
  hence prem1: "fv (\<Gamma>, e) - heapVars \<Gamma> \<subseteq> set (x#L)" by auto

  from 1 Gamma_subset have *: "x \<in> set L \<or> x \<in> heapVars \<Delta>" by auto

  have "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> (fv (\<Delta>, Lam [y]. e') - heapVars \<Delta>) \<union> {x}"
    by (auto dest!: set_mp[OF fv_subst_subset])
  also have "\<dots> \<subseteq> (fv (\<Gamma>, e) - heapVars \<Gamma>) \<union> {x}"
    using new_free_vars_on_heap[OF distinct_redsD1[OF Application.hyps(8)]] by auto
  also have "\<dots> \<subseteq> set L \<union> {x}" using prem1 by auto
  finally have "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> set L \<union> {x}". 
  with *
  have prem2: "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> set L" by auto
  
  have *: "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> heapVars \<Gamma>")
    case True
    thus ?thesis
      using fun_belowD[OF Application.hyps(10)[OF prem1], where \<rho>1 = \<rho> and x = x]
      by simp
  next
    case False 
    from False reds_avoids_live[OF distinct_redsD1[OF Application.hyps(8)] _ False] 
    show ?thesis by (simp add: lookup_HSem_other)
  qed

  have "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x)) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)  x)) \<cdot> r)"
    using Application.hyps(9)[OF prem1]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)) \<cdot> r)"
    by (intro monofun_cfun_arg monofun_cfun_fun monofun_LAM *) simp_all
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (((\<Lambda> (C \<cdot> r). CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := C_restr\<cdot>r\<cdot>v)\<^esub>)))) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := C_restr\<cdot>r\<cdot>v)\<^esub>))) \<down>CFn C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)) \<cdot> r)"
    apply (rule cfun_belowI)
    apply (case_tac xa, simp)
    apply simp
    apply (case_tac Ca, simp)
    apply simp
    apply (rule monofun_cfun[OF cont2monofunE[OF _ below_C] below_C])
    apply simp
    done
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := C_restr\<cdot>r\<cdot>((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x))\<^esub>) \<cdot> r)"
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
  
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)  f|` (heapVars \<Gamma>)"
    using Application.hyps(10)[OF prem1]
          fmap_restr_below_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule below_trans)
next
case (Variable x e \<Gamma> L \<Delta> z)
  hence [simp]:"x \<in> heapVars \<Gamma>"
    by (metis heapVars_from_set)

  case 2

  have "x \<notin> heapVars \<Delta>"
    by (rule reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]], simp_all)

  have subset: "heapVars (delete x \<Gamma>) \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF distinct_redsD1[OF Variable.hyps(2)]])

  have "fv (delete x \<Gamma>, e) \<union> {x} = fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF `distinctVars \<Gamma>` `(x,e)\<in>set \<Gamma>`])
  hence prem: "fv (delete x \<Gamma>, e) - heapVars (delete x \<Gamma>) \<subseteq> set (x # L)" using 2 by auto

  have fv_subset: "fv (delete x \<Gamma>, e) - heapVars (delete x \<Gamma>) \<subseteq> - (heapVars \<Delta> - heapVars \<Gamma>)"
    apply (rule subset_trans[OF prem])
    apply (rule subset_trans[OF reds_avoids_live'[OF distinct_redsD1[OF Variable.hyps(2)]]])
    by auto

  let "?new" = "heapVars \<Delta> - heapVars \<Gamma>"
  have "heapVars \<Gamma> \<subseteq> (-?new)" by auto

  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF distinctVars_map_of_delete_insert[symmetric, OF Variable(5,1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>(heapVars (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>(heapVars (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) \<sqsubseteq> (...) f|` (- ?new)" by (rule ssubst) (rule below_refl)
  also have "\<dots> \<sqsubseteq> (\<mu> \<rho>'. (\<rho> f++\<^bsub>heapVars \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) \<sqsubseteq> y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` heapVars (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>') f|` heapVars (delete x \<Gamma>)"
      using fv_subset by (auto intro: ESem_fresh_cong_below HSem_fresh_cong_below  fmap_restr_below_subset[OF _ 3])
    from below_trans[OF this(1) Variable(3)[OF prem]] below_trans[OF this(2) Variable(4)[OF prem]]
    have  "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` heapVars (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` heapVars (delete x \<Gamma>)".
    thus ?case
      using subset
      by (auto intro!: fun_belowI simp add: lookup_fmap_add_eq  lookup_fmap_restr_eq elim: fmap_restr_belowD)
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>heapVars \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF `x \<notin> heapVars \<Delta>`])
  also have "\<dots> = (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF `x \<notin> heapVars \<Delta>`])
  finally
  show le: ?case by (rule fmap_restr_below_subset[OF `heapVars \<Gamma> \<subseteq> (-?new)`])

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
    assume a: "a \<in> heapVars (asToHeap as)"
    have "atom a \<sharp> \<Gamma>" 
      by (rule Let(1)[unfolded fresh_star_def set_bn_to_atom_heapVars, rule_format, OF imageI[OF a]])
    hence "a \<notin> heapVars \<Gamma>"
      by (metis heapVars_not_fresh)
  }
  note * = this

  
  have "fv (asToHeap as @ \<Gamma>, body) - heapVars (asToHeap as @ \<Gamma>) \<subseteq>  fv (\<Gamma>, Let as body) - heapVars \<Gamma>"
    by (auto dest: set_mp[OF fv_asToHeap])
  with 1 have prem: "fv (asToHeap as @ \<Gamma>, body) - heapVars (asToHeap as @ \<Gamma>) \<subseteq> set L" by auto
  
  have f1: "atom ` heapVars (asToHeap as) \<sharp>* \<Gamma>"
    using Let(1) by (simp add: set_bn_to_atom_heapVars)

  have "\<N>\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
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

  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>asToHeap as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (heapVars \<Gamma>)"
    apply (rule fun_belowI)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (auto simp add: lookup_HSem_other lookup_fmap_restr_eq *)
    done
  also have "\<dots> = (\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>)"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (heapVars \<Gamma>)"
    by (rule fmap_restr_below_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` heapVars \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` heapVars \<Gamma>".
qed


corollary correctness_empty_env:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "distinctVars \<Gamma>"
  and     "fv (\<Gamma>, e) \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>"
proof-
  from assms(3) have "fv (\<Gamma>, e) - heapVars \<Gamma> \<subseteq> set L" by auto
  note corr =  correctness[OF assms(1,2) this, where \<rho> = "\<bottom>"]

  show "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" using corr(1).

  have "\<N>\<lbrace>\<Gamma>\<rbrace> = (\<N>\<lbrace>\<Gamma>\<rbrace>) f|` heapVars \<Gamma> "
    using fmap_restr_useless[OF HSem_fdom_subset, where \<rho>1 = "\<bottom>"] by simp
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>) f|` heapVars \<Gamma>" using corr(2).
  also have "\<dots> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by (rule fmap_restr_below_itself)
  finally show "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>".
qed

end
