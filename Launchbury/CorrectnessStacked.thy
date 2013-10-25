theory CorrectnessStacked
  imports "Denotational" LaunchburyStacked
begin

text {* This is the main correctness theorem for the stacked semantics. *}

theorem correctness:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<lbrace>\<Gamma>'@\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>'@\<Delta>\<rbrace>"
  using assms
proof(induct rule:reds_distinct_ind)

case (Lambda x y e \<Gamma> \<Gamma>')
  show ?case by simp
  -- "The lambda-case is trival"
next

case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z  e')
  let "?restr \<rho>" = "fmap_restr (insert x (heapVars \<Gamma>' \<union> heapVars \<Gamma>)) (\<rho>::Env)"
  let "?restr2 \<rho>" = "fmap_restr (insert x (heapVars \<Delta>' \<union> heapVars \<Delta>)) (\<rho>::Env)"

  have "n \<noteq> z" using Application by (simp add: fresh_Pair fresh_at_base)

  from stack_unchanged[OF distinct_redsD1[OF Application.hyps(8)]]
  have "\<Delta>' = \<Gamma>'" by simp
  hence [simp]:"atom n \<sharp> \<Delta>'"  using Application by (simp add: fresh_Pair)+
  
  have "atom n \<sharp> (\<Gamma>, e)" using Application by (simp add: fresh_Pair)
  note reds_fresh[OF Application(8) this]
  hence "atom n \<sharp> (\<Delta>, Lam [z]. e')"
    using Application(5)
    by (metis (hide_lams, no_types) Application(1) fresh_Pair heapVars_not_fresh)
  with `n \<noteq> z`
  have [simp]: "atom n \<sharp> \<Delta>" "atom n \<sharp> e'"
    by (auto simp add: fresh_Pair)

  note subset1 = reds_doesnt_forget'(1)[OF Application.hyps(8), unfolded append_Cons]
  from reds_doesnt_forget'(2)[OF Application.hyps(8), unfolded append_Cons]
  have subset2: "heapVars ((x, App (Var n) y) # \<Gamma>') \<subseteq> heapVars ((x, App (Var n) y) # \<Delta>')"
    apply (rule distinctVars_Cons_subset)
    apply (metis Application(4) distinctVars_appendD1)
    apply (metis Application(5) distinctVars_appendD1)
    done

  have "n \<noteq> x" 
    by (metis Application(1) fresh_PairD(1) fresh_PairD(2) not_self_fresh)

  have "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> = (\<lbrace>(x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by simp
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    -- {* Adding a fresh variable *}
    thm UHSem_add_fresh[symmetric]
    apply (subst UHSem_add_fresh[of n "f\<emptyset>" "(x, App e y) # \<Gamma>' @ \<Gamma>" e , symmetric])
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    done
  also have  "... = ?restr (\<lbrace>(x, App e y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (rule arg_cong[OF UHSem_reorder_head[OF `n \<noteq> x`]])
  also
  have "... = ?restr (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    -- {* Substituting the variable *}
    apply (rule arg_cong[OF HSem_subst_var_app[symmetric]])
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (simp add: UHSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... \<le> ?restr2  (\<lbrace>(n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Induction hypothesis"
    apply (rule fmap_restr_le[OF Application.hyps(9)[simplified]])
    using subset1 subset2 by auto
  also
  have "... \<le> ?restr2  (\<lbrace>(x, App (Var n) y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: UHSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = ?restr2 (\<lbrace>(x, App (Lam [z]. e') y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Substituting the variable again"
    apply (rule arg_cong[OF HSem_subst_var_app])
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr2 (\<lbrace>(n, Lam [z]. e') # (x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: UHSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = (\<lbrace>(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Removing the fresh variable"
    apply (subst UHSem_add_fresh[of n fempty "(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>" "Lam [z]. e'", symmetric])
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    done
  also
  have "... =  \<lbrace>(x, e'[z::=y]) # \<Delta>' @ \<Delta>\<rbrace>"
    -- "Semantics of application"
    apply (rule UHSem_subst_exp)
    apply (subgoal_tac "atom z \<sharp> \<rho>'")
    (* HOLCF simpproc looping bug:
    apply (simp only: AESem.simps Fn_project.simps (* beta_cfun CESem_cont2cont fmap_upd_cont cont_const cont_id*))
    apply (subst beta_cfun)
    apply (thin_tac ?x)+
    using [[simp_trace]] [[simp_trace_depth_limit=1000]]
    apply (simp del: fmap_upd_noop)
    *)
    apply (simp only: AESem.simps Fn_project.simps beta_cfun CESem_cont2cont fmap_upd_cont cont_const cont_id)
    apply (rule ESem_subst[simplified])
      using Application(2)
      apply (auto simp add: sharp_Env fresh_Pair heapVars_not_fresh)
    done
  also
  have "... \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>"
    -- "Induction hypothesis"
    by (rule Application.hyps(11)[simplified])
  finally
  show "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>".

next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have "x \<noteq> y" using Variable(3) by (auto simp add: distinctVars_Cons distinctVars_append)
  have [simp]: "y \<notin> heapVars \<Delta>'" using Variable(4) by (simp add: distinctVars_Cons)

  have map_of_eq1: "map_of (((x, Var y) # \<Gamma>') @ \<Gamma>) =  map_of (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)"
    apply (subst distinctVars_map_of_delete_insert[symmetric,OF Variable(2), where x = y and e = e])
    using `(y, e) \<in> set \<Gamma>` Variable(3)
    by (auto simp add: distinctVars_Cons delete_no_there)
  have map_of_eq2: "map_of (((y, z) # (x, z) # \<Delta>') @ \<Delta>) = map_of (((x, z) # \<Delta>') @ (y, z) # \<Delta>)"
    by (auto simp add: map_add_upd_left dom_map_of_conv_heapVars)

  have "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>\<rbrace>"
    by (rule UHSem_reorder[OF map_of_eq1])
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  also
  have "... =  \<lbrace>(y, z) # (x, Var y) # \<Delta>' @ \<Delta>\<rbrace>"
    by simp
  also
  have "... =  \<lbrace>(x, Var y) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: UHSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>(x, z) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    -- {* Substituting the variable @{term y} *}
    apply (rule HSem_subst_var_var)
    using `x \<noteq> y` by (simp add: fresh_Pair fresh_at_base)
  also
  have "... =  \<lbrace>(y, z) # (x, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: UHSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>((y, z) # (x, z) # \<Delta>') @ \<Delta>\<rbrace>"
    by simp
  also
  have "... = \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by (rule UHSem_reorder[OF map_of_eq2])
  finally
  show "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>".

next
case (Let as \<Gamma> x \<Gamma>' body \<Delta>' \<Delta>)
  have d1: "distinctVars (asToHeap as @ ((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
    by (metis Let(1) Let(2) distinctVars_append_asToHeap fresh_star_list(1,2) fresh_star_Pair let_binders_fresh)
  hence d3: "distinctVars ((x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>)"
    and d4: "distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    and d5: "distinctVars ((x, body) # \<Gamma>' @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)

  have map_of_eq: "map_of ((x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>) = map_of (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    apply (auto simp add: map_add_upd_left dom_map_of_conv_heapVars)
    apply (subst (1 2) map_add_assoc[symmetric])
    apply (rule arg_cong[OF map_add_comm])
    using d1 by (auto simp add: distinctVars_append distinctVars_Cons dom_map_of_conv_heapVars[symmetric])

  have "\<lbrace>((x, Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>(x, Let as body) # \<Gamma>' @ \<Gamma>\<rbrace>"
    by simp
  also
  have "... \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>\<rbrace>"
    -- "Semantics of let"
    apply (rule HSem_unfold_let[OF d5])
    using Let(1) by (auto simp add: fresh_star_Pair fresh_star_list)
  also
  have "... = \<lbrace>((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>\<rbrace>"
    by (rule UHSem_reorder[OF map_of_eq])
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>".
qed
end

