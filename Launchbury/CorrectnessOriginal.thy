theory CorrectnessOriginal
imports "Denotational" "Launchbury"
begin

text {*
This is the main correctness theorem, Theorem 2 from \cite{launchbury}.
*}

(* Another possible invariant seems to be: "fdom \<rho> - heapVars \<Gamma> \<subseteq> set L" *)

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) - heapVars \<Gamma> \<subseteq> set L"
  shows   "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` heapVars \<Gamma> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` heapVars \<Gamma>"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds.strong_induct)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  hence "y \<noteq> x" by (simp_all add: fresh_at_base)

  have Gamma_subset: "heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF Application.hyps(8)])

  case 1
  hence prem1: "fv (\<Gamma>, e) - heapVars \<Gamma> \<subseteq> set (x#L)" by auto

  from 1 Gamma_subset have *: "x \<in> set L \<or> x \<in> heapVars \<Delta>" by auto

  have "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> (fv (\<Delta>, Lam [y]. e') - heapVars \<Delta>) \<union> {x}"
    by (auto dest!: set_mp[OF fv_subst_subset])
  also have "\<dots> \<subseteq> (fv (\<Gamma>, e) - heapVars \<Gamma>) \<union> {x}"
    using new_free_vars_on_heap[OF Application.hyps(8)] by auto
  also have "\<dots> \<subseteq> set L \<union> {x}" using prem1 by auto
  finally have "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> set L \<union> {x}". 
  with *
  have prem2: "fv (\<Delta>, e'[y::=x]) - heapVars \<Delta> \<subseteq> set L" by auto
  
  have *: "(\<lbrace>\<Gamma>\<rbrace>\<rho>) x = (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> heapVars \<Gamma>")
    case True
    from Application.hyps(10)[OF prem1, where \<rho> = \<rho>]
    have "((\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` heapVars \<Gamma>) x  = ((\<lbrace>\<Delta>\<rbrace>\<rho>) f|` heapVars \<Gamma>) x" by simp
    with True show ?thesis by simp
  next
    case False 
    from False reds_avoids_live[OF Application.hyps(8)] 
    show ?thesis by (simp add: lookup_HSem_other)
  qed

  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Gamma>\<rbrace>\<rho>) x"
    by simp
  also have "\<dots> = (\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Gamma>\<rbrace>\<rho>) x"
    using Application.hyps(9)[OF prem1] by simp
  also have "\<dots> = (\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
    unfolding *..
  also have "\<dots> = (Fn \<cdot> (\<Lambda> v. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v)\<^esub>)) \<down>Fn (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
    by simp
  also have "\<dots> = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<lbrace>\<Delta>\<rbrace>\<rho>) x)\<^esub>"
    by simp
  also have "\<dots> = \<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF ESem_subst[OF `y \<noteq> x`]])
  also have "\<dots> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    by (rule Application.hyps(12)[OF prem2])
  finally
  show ?case.
  
  show "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` heapVars \<Gamma> = (\<lbrace>\<Theta>\<rbrace>\<rho>) f|` heapVars \<Gamma>"
    using Application.hyps(10)[OF prem1]
          fmap_restr_eq_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule trans)
next
case (Variable \<Gamma> x e L \<Delta> z)
  hence [simp]:"x \<in> heapVars \<Gamma>" by (metis heapVars_from_set map_of_is_SomeD)

  case 2
  have "x \<notin> heapVars \<Delta>"
    by (rule reds_avoids_live[OF Variable.hyps(2)], simp_all)

  have subset: "heapVars (delete x \<Gamma>) \<subseteq> heapVars \<Delta>"
    by (rule reds_doesnt_forget[OF Variable.hyps(2)])

  have "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF `map_of \<Gamma> x = Some e`])
  hence prem: "fv (delete x \<Gamma>, e) - heapVars (delete x \<Gamma>) \<subseteq> set (x # L)" using 2 by auto

  have fv_subset: "fv (delete x \<Gamma>, e) - heapVars (delete x \<Gamma>) \<subseteq> - (heapVars \<Delta> - heapVars \<Gamma>)"
    apply (rule subset_trans[OF prem])
    apply (rule subset_trans[OF reds_avoids_live'[OF Variable.hyps(2)]])
    by auto

  let "?new" = "heapVars \<Delta> - heapVars \<Gamma>"
  have "heapVars \<Gamma> \<subseteq> (-?new)" by auto

  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF map_of_delete_insert[symmetric, OF Variable(1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>(heapVars (delete x \<Gamma>))\<^esub> (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>(heapVars (delete x \<Gamma>))\<^esub> (\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) = (...) f|` (- ?new)" by simp
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>heapVars \<Delta>\<^esub> (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) = y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` heapVars (delete x \<Gamma>) = (\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>') f|` heapVars (delete x \<Gamma>)"
      using fv_subset by (auto intro: ESem_fresh_cong HSem_fresh_cong  fmap_restr_eq_subset[OF _ 3])
    from trans[OF this(1) Variable(3)[OF prem]] trans[OF this(2) Variable(4)[OF prem]]
    have  "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` heapVars (delete x \<Gamma>) = (\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` heapVars (delete x \<Gamma>)".
    thus ?case
      using subset
      by (auto intro!: ext simp add: lookup_fmap_add_eq  lookup_fmap_restr_eq dest: fmap_restr_eqD )
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> f++\<^bsub>heapVars \<Delta>\<^esub> (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF `x \<notin> heapVars \<Delta>`])
  also have "\<dots> = (\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF `x \<notin> heapVars \<Delta>`])
  finally
  show le: ?case by (rule fmap_restr_eq_subset[OF `heapVars \<Gamma> \<subseteq> (-?new)`])

  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    using fmap_restr_eqD[OF le, where x = x]
    by simp
  also have "\<dots> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (auto simp add: lookup_HSem_heap)
  finally
  show "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>".
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

  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (simp)
  also have "\<dots> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF prem])
  finally
  show ?case.

  have "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>) = (\<lbrace>asToHeap as\<rbrace>(\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (heapVars \<Gamma>)"
    apply (rule ext)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (auto simp add: lookup_HSem_other lookup_fmap_restr_eq *)
    done
  also have "\<dots> = (\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>) f|` (heapVars \<Gamma>)"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (heapVars \<Gamma>)"
    by (rule fmap_restr_eq_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` heapVars \<Gamma> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` heapVars \<Gamma>".
qed

end
