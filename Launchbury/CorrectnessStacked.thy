theory CorrectnessStacked
  imports "Denotational" LaunchburyStacked
begin

subsubsection {* The semantics of let only adds new bindings *}

text {*
The following lemma is not as general as possible and specialized to @{text "\<rho> = fempty"}, as that is
the only case required later on, and easier to prove.
*}

lemma HSem_unfold_let:
  assumes distinct: "distinctVars ((x, body) # \<Gamma>)"
  assumes fresh: "set (bn as) \<sharp>* (x, Let as body, \<Gamma>)"
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> = (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)f|` (insert x (heapVars \<Gamma>))"
proof-
  from fresh
  have fresh_Gamma: "atom ` heapVars (asToHeap as) \<sharp>* \<Gamma>"
    by (metis fresh_star_Pair set_bn_to_atom_heapVars)

  from fresh
  have "set (bn as) \<sharp>* ((x, Let as body) # \<Gamma>)"
    by (auto simp add: fresh_star_def fresh_Pair fresh_Cons)
  from fresh_assn_distinct[OF this]
  have disjoint: "heapVars (asToHeap as) \<inter> insert x (heapVars \<Gamma>) = {}"
     by auto
  hence x_not_as: "x \<notin> heapVars (asToHeap as)"
    by auto

  {
    fix x' e
    assume "e \<in> snd ` set \<Gamma>"

    have simp1: " fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<inter> insert x (heapVars \<Gamma>) = insert x (heapVars \<Gamma>)"
      by auto

    have simp2: "fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) - insert x (heapVars \<Gamma>) = heapVars (asToHeap as)"
      using disjoint
      by auto

    have fresh_e: "atom ` heapVars (asToHeap as) \<sharp>* e"
      by (rule fresh_star_heap_expr'[OF fresh_Gamma `_ \<in> snd\` set \<Gamma>`])

    have "\<lbrakk> e \<rbrakk>\<^bsub>fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
      apply (rule ESem_ignores_fresh_restr'[symmetric])
      apply (subst simp2)
      apply (rule fresh_e)
      done
  } note Gamma_eq = this

case goal1
  have "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> = fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)"
  proof(rule below_antisym)
    show "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> \<sqsubseteq> fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)" (is "_ \<sqsubseteq> ?r")
    proof (rule HSem_fempty_below)
      fix x'
      assume "x' \<in> heapVars ((x, Terms.Let as body) # \<Gamma>)"
      hence x': "x' \<in> insert x (heapVars \<Gamma>)" by simp

      hence x'_not_as:"x' \<notin> heapVars (asToHeap as)"
        using disjoint
        by auto
      show "\<lbrakk> the (map_of ((x, Terms.Let as body) # \<Gamma>) x') \<rbrakk>\<^bsub>?r\<^esub> \<sqsubseteq> ?r f! x'"
      proof(cases "x' = x")
      case True 
        have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>?r\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>?r\<^esub>" by simp
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>))\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<^esub>"
          by (rule arg_cong[OF HSem_redo[where \<rho> = "f\<emptyset>" and \<Delta> = "(x, body) # \<Gamma>", simplified]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
          by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as], symmetric])
        finally
        show ?thesis using True x' by (simp add: lookup_HSem_heap)
      next
        case False thus ?thesis
        apply (subst (2) HSem_eq)
        using x'
        apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as] lookupHeapToEnv Gamma_eq[OF the_map_of_snd])
        done
      qed
    qed auto

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>" (is "_ \<sqsubseteq> ?r")
    proof (rule HSem_fempty_below)
      fix x'
      assume "x' \<in> heapVars ((x, body) # asToHeap as @ \<Gamma>)"
      hence x': "x' = x \<or> x' \<in> heapVars (asToHeap as) \<or> x' \<in> heapVars \<Gamma>" by simp

      show "\<lbrakk> the (map_of ((x, body) # asToHeap as @ \<Gamma>) x') \<rbrakk>\<^bsub>?r\<^esub> \<sqsubseteq> ?r f! x'"
      proof(cases "x' = x")
        assume "x' = x"
        thus ?thesis
          by (simp add: lookup_HSem_other[OF x_not_as] lookup_HSem_heap)
      next
        have merged_r: "?r = \<lbrace>asToHeap as @ ((x, Let as body) # \<Gamma>)\<rbrace>"
          apply (rule HSem_merge)
            using disjoint distinct apply (auto simp add: distinctVars_Cons distinctVars_append)[1]
            using fresh apply (metis fresh_star_list(2) fresh_star_Pair set_bn_to_atom_heapVars)              
          done

        assume "x' \<noteq> x"

        hence map_of_reorder: "map_of ((x, body) # asToHeap as @ \<Gamma>) x' = map_of (asToHeap as @ ((x, Let as body) # \<Gamma>)) x'"
          apply simp
          apply (subst map_add_upd_left)
          apply (metis dom_map_of_conv_heapVars x_not_as)
          apply simp
          done

        show ?thesis
          unfolding merged_r
          apply (subst lookup_HSem_heap)
          using x' apply simp[1]
          unfolding map_of_reorder
          apply (rule below_refl)
          done
      qed
    qed auto
    thus "fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_HSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>", simplified (no_asm)])
      using disjoint apply auto
      done
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed


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
    apply (subst HSem_add_fresh[of n "(x, App e y) # \<Gamma>' @ \<Gamma>" "f\<emptyset>"  e , symmetric])
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    apply simp
    done
  also have  "... = ?restr (\<lbrace>(x, App e y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (rule arg_cong[OF HSem_reorder_head[OF `n \<noteq> x`]])
  also
  have "... = ?restr (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    -- {* Substituting the variable *}
    apply (rule arg_cong[OF HSem_subst_var_app[symmetric]])
    using Application(1) apply (simp add: fresh_Pair)
    apply simp
    done
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... \<le> ?restr2  (\<lbrace>(n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Induction hypothesis"
    apply (rule fmap_restr_le[OF Application.hyps(9)[simplified]])
    using subset1 subset2 by auto
  also
  have "... \<le> ?restr2  (\<lbrace>(x, App (Var n) y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = ?restr2 (\<lbrace>(x, App (Lam [z]. e') y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Substituting the variable again"
    apply (rule arg_cong[OF HSem_subst_var_app])
    using Application(1) apply (simp add: fresh_Pair)
    apply simp
    done
  also
  have "... = ?restr2 (\<lbrace>(n, Lam [z]. e') # (x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = (\<lbrace>(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Removing the fresh variable"
    apply (subst HSem_add_fresh[of n  "(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>" fempty "Lam [z]. e'", symmetric])
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    apply simp
    done
  also
  have "... =  \<lbrace>(x, e'[z::=y]) # \<Delta>' @ \<Delta>\<rbrace>"
    -- "Semantics of application"
    apply (rule HSem_subst_exp)
    apply simp
    apply (rule ESem_subst[simplified])
      using Application(2)
      apply (auto simp add: fresh_Pair heapVars_not_fresh)
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
    by (rule HSem_reorder[OF map_of_eq1])
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  also
  have "... =  \<lbrace>(y, z) # (x, Var y) # \<Delta>' @ \<Delta>\<rbrace>"
    by simp
  also
  have "... =  \<lbrace>(x, Var y) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>(x, z) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    -- {* Substituting the variable @{term y} *}
    apply (rule HSem_subst_var_var)
    using `x \<noteq> y` apply (simp add: fresh_Pair fresh_at_base)
    apply simp
    done
  also
  have "... =  \<lbrace>(y, z) # (x, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>((y, z) # (x, z) # \<Delta>') @ \<Delta>\<rbrace>"
    by simp
  also
  have "... = \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by (rule HSem_reorder[OF map_of_eq2])
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
    by (rule HSem_reorder[OF map_of_eq])
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>".
qed
end

