theory CorrectnessResourced
  imports "ResourcedDenotational" Launchbury
begin


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "distinctVars \<Gamma>"
  and     "fdom \<rho> - heapVars \<Gamma> \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "fmap_lookup_bot (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds_distinct_strong_ind)
case (Lambda \<Gamma> x e L)
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  hence "y \<noteq> x" by (simp_all add: fresh_at_base)

  case 1
  hence hyp1: "fdom \<rho> - heapVars \<Gamma> \<subseteq> set (x # L)" by auto
  have hyp2: "fdom \<rho> - heapVars \<Delta> \<subseteq> set L"
    using 1 reds_doesnt_forget[OF distinct_redsD1[OF Application.hyps(8)]]
    by auto

  have "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    using Application.hyps(9)[OF hyp1]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    using fun_belowD[OF Application.hyps(10)[OF hyp1]]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (((\<Lambda> (C \<cdot> r). CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>)))) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>))) \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    apply (rule cfun_belowI)
    apply (case_tac xa, simp)
    apply simp
    apply (case_tac Ca, simp)
    apply simp
    apply (rule monofun_cfun[OF cont2monofunE[OF _ below_C] below_C])
    apply simp
    done
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x))\<^esub>) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> \<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)\<^esub>) \<cdot> r)"
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
    by (rule Application.hyps(12)[OF hyp2])
  finally
  show ?case.
  
  show "op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)"
    using Application.hyps(10)[OF hyp1] Application.hyps(13)[OF hyp2]
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

  have new_fresh: "(heapVars \<Delta> - (heapVars \<Gamma> - {x})) \<inter> fdom \<rho> = {}"
    using reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]] 2
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by auto

  have [simp]: "insert x (fdom \<rho> \<union> heapVars \<Delta>) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by auto

  have [simp]: "(insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) \<inter> heapVars \<Delta>) = heapVars \<Gamma> - {x}"
    using new_fresh subset `x \<notin> _` by auto

  have [simp]:"\<And> x y . x \<union> y \<union> y = x \<union> y" "\<And> x y. (x \<union> y) \<inter> y = y"
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - (heapVars  \<Gamma> - {x}) = insert x (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have [simp]: "(heapVars \<Gamma> - {x}) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (heapVars \<Gamma> - {x})"
    by auto

  have [simp]: "(fdom \<rho> - heapVars \<Gamma>) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have condGamma: "fix_on_cond {\<rho>' . f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub> \<sqsubseteq> \<rho>'}
                               (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
     (\<lambda>a. (\<rho> f++ (\<N>\<lbrace>delete x \<Gamma>\<rbrace>a) f|` heapVars (delete x \<Gamma>))(x f\<mapsto> \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>a\<^esub>))"
     thm fix_on_cond_cong[OF iterative_HSem'_cond]
    by (rule fix_on_cond_cong[OF iterative_HSem'_cond], auto)
  have condDelta: "fix_on_cond {\<rho>' . f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub> \<sqsubseteq> \<rho>'}
                                    (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
                                    (\<lambda>\<rho>'. (\<rho> f++ (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>') f|` heapVars \<Delta>)(x f\<mapsto> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>))"
    using `x \<notin> heapVars \<Delta>` 
    by (rule fix_on_cond_cong[OF iterative_HSem'_cond]) auto

  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    apply (rule HSem_reorder)
    apply (rule distinctVars_map_of_delete_insert[symmetric, OF Variable(5,1)])
    done
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "fmap_lookup_bot (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> fmap_lookup_bot ..." by (rule ssubst) (rule below_refl)
  also have "\<dots> \<sqsubseteq> fmap_lookup_bot (fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
                          (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>' ))( x f\<mapsto> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)))"
    apply (rule parallel_fix_on_ind[OF condGamma condDelta])
    apply (intro adm_is_adm_on adm_lemmas fmap_lookup_bot_cont cont2cont_fmap_lookup_bot cont2cont_lambda cont2cont)
    apply simp
    apply (rule fun_belowI)
    apply (case_tac "xa = x")
    apply simp
    apply (rule below_trans[OF Variable.hyps(3)])
    using 2 apply auto[1]
    apply (erule ESem_mono_relaxed[OF HSem_monofun_relaxed])

    apply (case_tac "xa \<in> heapVars \<Gamma>")
    apply (subgoal_tac "xa \<in> heapVars \<Delta>")
      prefer 2
      using subset apply auto[1]
    apply simp
    using Variable.hyps(4)
    apply (erule_tac x = "y" in meta_allE)
    apply (elim meta_impE)
    using 2  `x \<notin> heapVars \<Delta>` apply auto[1]
    apply (drule_tac  x = xa in fun_belowD) back
    apply simp
    apply (erule below_trans)
    apply (drule HSem_monofun_relaxed)
    apply (drule_tac  x = xa in fun_belowD)
    apply simp

    apply (case_tac "xa \<in> fdom \<rho>")
    apply (subgoal_tac "xa \<notin> heapVars \<Delta>")
      prefer 2
      using new_fresh apply auto[1]
    apply simp
    apply simp
    done
  also have "\<dots> = fmap_lookup_bot (fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x f\<mapsto> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)))"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF `x \<notin> heapVars \<Delta>`])
  also have "\<dots> = fmap_lookup_bot (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF `x \<notin> heapVars \<Delta>`])
  finally
  show le: ?case.

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
    apply (auto simp add: the_lookup_HSem_heap  monofun_cfun_arg[OF below_C])
    done
  finally
  show "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>".
next
case (Let as \<Gamma> L body \<Delta> z)
  case 1
  { fix a
    assume a: "a \<in> heapVars (asToHeap as)"
    have "atom a \<sharp> L" 
      by (rule Let(2)[unfolded fresh_star_def set_bn_to_atom_heapVars, rule_format, OF imageI[OF a]])
    hence "a \<notin> set L"
      by (metis fresh_list_elem not_self_fresh)
    moreover
    have "atom a \<sharp> \<Gamma>" 
      by (rule Let(1)[unfolded fresh_star_def set_bn_to_atom_heapVars, rule_format, OF imageI[OF a]])
    hence "a \<notin> heapVars \<Gamma>"
      by (metis heapVars_not_fresh)
    ultimately
    have "a \<notin> fdom \<rho>" and "a \<notin> heapVars \<Gamma>"
      using 1 by auto
  }
  note * = this
  
  have hyp: "fdom \<rho> - heapVars (asToHeap as @ \<Gamma>) \<subseteq> set L"
    using 1 by auto

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
    by (rule Let.hyps(4)[OF hyp])
  finally
  show ?case.

  have "fmap_lookup_bot (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>asToHeap as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>))"
    apply (rule fun_belowI)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (auto simp add: the_lookup_HSem_heap the_lookup_HSem_other * fmap_lookup_bot_HSem_other)
    done
  also have "\<dots> = fmap_lookup_bot (\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)"
    by (rule Let.hyps(5)[OF hyp])
  finally
  show "op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)".
qed
end
