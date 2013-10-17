theory CorrectnessResourced
  imports "Resourced-Denotational-Props" Launchbury "HSem-Equivalences"
begin


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "distinctVars \<Gamma>"
  and     "fdom \<rho> \<subseteq> set L"
  and     "fdom \<rho> \<inter> heapVars \<Gamma> = {}"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "fmap_lookup_bot (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)"
  using assms
proof(nominal_induct avoiding: \<rho> rule:reds_distinct_strong_ind)
case (Lambda \<Gamma> x e L \<rho>)
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' \<rho>)
  hence "atom y \<sharp> \<N>\<lbrace>\<Delta>\<rbrace>\<rho>" and "y \<noteq> x"
    by (simp_all add: fresh_at_base)

  case 1
  hence hyp1: "fdom \<rho> \<subseteq> set (x # L)" by auto
  have hyp2: "fdom \<rho> \<subseteq> set L"
    using 1 reds_doesnt_forget[OF distinct_redsD1[OF Application.hyps(9)]]
    by auto

  from reds_avoids_live[OF distinct_redsD1[OF Application.hyps(9)]] Application.prems
  have prem2': "fdom \<rho> \<inter> heapVars \<Delta> = {}" by auto

  have "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    by simp
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    using Application.hyps(10)[OF hyp1 Application.prems(2)]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    using fun_belowD[OF Application.hyps(11)[OF hyp1 Application.prems(2)]]
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM)
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (((\<Lambda> (C \<cdot> r). CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>)))) \<cdot> r \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    by (simp add: Rep_cfun_inverse)
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((CFn \<cdot> (\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>))) \<down>CFn C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    apply (rule cfun_belowI)
    apply (case_tac xa, simp)
    apply simp
    apply (case_tac Ca, simp)
    apply simp
    apply (rule monofun_cfun[OF cont2monofunE[OF _ below_C] below_C])
    apply simp
    done
  (*
  also have "\<dots> \<sqsubseteq> (\<Lambda> (C\<cdot>r). ((CFn \<cdot> (\<Lambda> v.  C_restr\<cdot>r\<cdot>(\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>)))\<down>CFn  C_restr\<cdot>r\<cdot>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho> f!\<^sub>\<bottom> x)) \<cdot> r)"
    by (fastforce intro: monofun_cfun_arg monofun_cfun_fun monofun_LAM case_of_C_below)    
  *)
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
    by (rule arg_cong[OF CESem_subst[OF `y \<noteq> x` `atom y \<sharp> \<N>\<lbrace>\<Delta>\<rbrace>\<rho>`]])
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    by (metis C_case_below eta_cfun)
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    by (rule Application.hyps(13)[OF hyp2 prem2'])
  finally
  show ?case.
  
  case 2
  show ?case
    using Application.hyps(11)[OF hyp1 Application.prems(2)] Application.hyps(14)[OF hyp2 prem2']
    by (rule below_trans)
next
case (Variable x e \<Gamma> L \<Delta> z \<rho>)
  hence [simp]:"x \<in> heapVars \<Gamma>"
    by (metis heapVars_from_set)

  case 2

  have "x \<notin> heapVars \<Delta>"
    by (rule reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]], simp_all)

  have subset: "heapVars (delete x \<Gamma>) \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF distinct_redsD1[OF Variable.hyps(2)]])

  have new_fresh[simp]: "(heapVars \<Delta> - (heapVars \<Gamma> - {x})) \<inter> fdom \<rho> = {}"
    using reds_avoids_live[OF distinct_redsD1[OF Variable.hyps(2)]] 2
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]: "insert x (fdom \<rho> \<union> heapVars \<Delta>) - heapVars \<Delta> = insert x (fdom \<rho> - heapVars \<Gamma>)"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]: "(insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) \<inter> heapVars \<Delta>) = heapVars \<Gamma> - {x}"
    using new_fresh subset `x \<notin> _` by (auto simp del:new_fresh)

  have [simp]:"\<And> x y . x \<union> y \<union> y = x \<union> y" "\<And> x y. (x \<union> y) \<inter> y = y"
    by auto

  have [simp]: "insert x (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) - (heapVars  \<Gamma> - {x}) = insert x (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have [simp]: "(heapVars \<Gamma> - {x}) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (heapVars \<Gamma> - {x})"
    by auto

  have [simp]: "(fdom \<rho> - heapVars \<Gamma>) \<inter> (fdom \<rho> \<union> (heapVars \<Gamma> - {x})) = (fdom \<rho> - heapVars \<Gamma>)"
    by auto

  have disjoint2: "fdom \<rho> \<inter> heapVars ((x, z) # \<Delta>) = {}"
    using new_fresh Variable.prems
    by (auto simp del: new_fresh)

  have "has_cont_ESem CESem" by unfold_locales
  note iterative_HSem'_cond_join = "HSem-Equivalences.has_cont_ESem.iterative_HSem'_cond_join"[OF this]
  and  iterative_HSem_join =  "HSem-Equivalences.has_cont_ESem.iterative_HSem_join"[OF this]
  and iterative_HSem'_join =  "HSem-Equivalences.has_cont_ESem.iterative_HSem'_join"[OF this]


  have condGamma: "fix_on_cond {\<rho>' . f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub> \<sqsubseteq> \<rho>'}
                               (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
     (\<lambda>a. (\<rho> f++ (\<N>\<lbrace>delete x \<Gamma>\<rbrace>a f|` (- heapVars (delete x \<Gamma>))) f|` heapVars (delete x \<Gamma>))(x f\<mapsto> \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>a f|`(- heapVars (delete x \<Gamma>))\<^esub>))"
    by (rule fix_on_cond_cong[OF iterative_HSem'_cond_join]) auto
  have condDelta: "fix_on_cond {\<rho>' . f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub> \<sqsubseteq> \<rho>'}
                                    (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
                                    (\<lambda>\<rho>'. (\<rho> f++ (\<N>\<lbrace>\<Delta>\<rbrace>(\<rho>' f|` (- heapVars \<Delta>))) f|` heapVars \<Delta>)(x f\<mapsto> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>(\<rho>' f|` (- heapVars \<Delta>))\<^esub>))"
    using `x \<notin> heapVars \<Delta>` 
    by (rule fix_on_cond_cong[OF iterative_HSem'_cond_join]) auto

  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    apply (rule HSem_reorder)
    apply (rule distinctVars_map_of_delete_insert[symmetric, OF Variable(5,1)])
    done
  also have "\<dots> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>(\<rho> f|` (- heapVars ((x,e) # delete x \<Gamma>)))"
    apply (rule arg_cong[OF fmap_restr_useless[symmetric]])
    using Variable.prems by auto
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<N>\<lbrace>delete x \<Gamma>\<rbrace>(\<rho>' f|` (- heapVars (delete x \<Gamma>)))))( x f\<mapsto> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem_join, simp)
  also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars (delete x \<Gamma>))]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars (delete x \<Gamma>)) (\<N>\<lbrace>delete x \<Gamma>\<rbrace>(\<rho>' f|` (- heapVars (delete x \<Gamma>)))))( x f\<mapsto> \<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<N>\<lbrace>delete x \<Gamma>\<rbrace>(\<rho>' f|` (- heapVars (delete x \<Gamma>))))\<^esub>))"
    by (rule iterative_HSem'_join, simp)
  also have "fmap_lookup_bot \<dots> \<sqsubseteq> fmap_lookup_bot (fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
                          (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<N>\<lbrace>\<Delta>\<rbrace>(\<rho>' f|` (- heapVars \<Delta>))))( x f\<mapsto> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>(\<rho>' f|` (- heapVars \<Delta>))\<^esub>)))"
    apply (rule parallel_fix_on_ind[OF condGamma condDelta])
    apply (intro adm_is_adm_on adm_lemmas fmap_lookup_bot_cont cont2cont_fmap_lookup_bot cont2cont_lambda cont2cont)
    apply simp
    apply (rule fun_belowI)
    apply (case_tac "xa = x")
    apply simp
    apply (rule below_trans[OF Variable.hyps(3)])
    using 2 apply auto[2]
    apply (rule cont2monofunE[OF ESem_cont])
    apply (rule HSem_mono[OF disjoint_is_HSem_cond disjoint_is_HSem_cond])
    using 2 disjoint2 `x \<notin> heapVars \<Delta>` apply auto[2]
    apply (rule fmap_belowI)
    using 2 disjoint2 `x \<notin> heapVars \<Delta>` apply auto[1]
    apply (drule_tac  x = xaa in fun_belowD)
    apply (auto elim: fun_belowD)[1]

    apply (case_tac "xa \<in> heapVars \<Gamma>")
    apply simp
    apply (case_tac "xa \<in> heapVars \<Delta>")
    apply simp
    
    using  Variable.hyps(4)
    apply (erule_tac x = "y f|` insert x (- heapVars \<Gamma>)" in meta_allE)
    apply (elim meta_impE)
    using 2 disjoint2 `x \<notin> heapVars \<Delta>` apply auto[2]
    apply (drule_tac  x = xa in fun_belowD) back
    apply auto[1]
    apply (erule below_trans)
    apply (rule cont2monofunE[OF cont2cont_lookup[OF cont_id]])
    apply (rule HSem_mono[OF disjoint_is_HSem_cond disjoint_is_HSem_cond])
    using 2 disjoint2 `x \<notin> heapVars \<Delta>` apply auto[2]
    apply (rule fmap_belowI)
    using 2 disjoint2 `x \<notin> heapVars \<Delta>` apply auto[1]
    apply (drule_tac  x = xaa in fun_belowD)
    apply (auto elim: fun_belowD)[1]

    using subset apply auto[1]

    apply (case_tac "xa \<in> fdom \<rho>")
    apply simp
    apply (case_tac "xa \<in> heapVars \<Delta>")
    using subset disjoint2 apply auto[3]
    done
  also have "\<dots> = fmap_lookup_bot (fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Delta>)]\<^esub>)
    (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Delta>) (\<N>\<lbrace>\<Delta>\<rbrace>(\<rho>' f|` (- heapVars \<Delta>))))( x f\<mapsto> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)))"
    by (rule arg_cong[OF iterative_HSem'_join[symmetric], OF `x \<notin> heapVars \<Delta>`])
  also have "\<dots> = fmap_lookup_bot (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>(\<rho>  f|` (- heapVars ((x, z) # \<Delta>))))"
    by (rule arg_cong[OF iterative_HSem_join[symmetric], OF `x \<notin> heapVars \<Delta>`])
  also have "\<dots> = fmap_lookup_bot (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)"
    apply (rule arg_cong[OF fmap_restr_useless])
    using Variable.prems new_fresh by (auto simp del:new_fresh)
  finally
  show le: ?case.

  case 1
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
    apply simp
    using disjoint2
    apply (simp add: the_lookup_HSem_heap[OF disjoint_is_HSem_cond[OF disjoint2]]  monofun_cfun_arg[OF below_C])
    done
  finally
  show ?case.
next
case (Let as \<Gamma> L body \<Delta> z \<rho>)
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
  hence "set (bn as) \<sharp>* \<rho>"
    apply (subst fresh_star_def)
    apply (subst set_bn_to_atom_heapVars)
    apply (auto simp add: sharp_Env)
    done
  hence  [simp]: "set (bn as) \<sharp>* (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    using Let(1) by simp
  
  have f1: "atom ` heapVars (asToHeap as) \<sharp>* (\<Gamma>, \<rho>)"
    using Let(1) `_ \<sharp>* \<rho>`
    by (simp add: set_bn_to_atom_heapVars fresh_star_Pair)

  have disjoint: "fdom \<rho> \<inter> heapVars (asToHeap as @ \<Gamma>) = {}"
    using 1 * by auto

  have "\<N>\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    apply (rule cfun_belowI)
    apply (case_tac x)
    apply (simp_all add: monofun_cfun_arg[OF below_C])
    done
  also have "\<dots> =  \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1 disjoint]])
  also have "\<dots> \<sqsubseteq>  \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF Let.prems(1) disjoint])
  finally
  show ?case.

  case 2
  have "fmap_lookup_bot (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<sqsubseteq> fmap_lookup_bot ((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)\<^bsub>[fdom (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) \<union> heapVars (asToHeap as)]\<^esub>)"
    by (auto intro: fun_belowI)
  also have "\<dots> \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>asToHeap as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>))"
    apply (rule cont2monofunE[OF fmap_lookup_bot_cont HSem_refines[OF disjoint_is_HSem_cond]])
    using 1 * by auto
  also have "\<dots> = fmap_lookup_bot (\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>)"
    by (rule arg_cong[OF HSem_merge[OF f1 disjoint]])
  also have "\<dots> \<sqsubseteq> fmap_lookup_bot (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)"
    by (rule Let.hyps(5)[OF Let.prems(1) disjoint])
  finally
  show ?case.
qed
end
