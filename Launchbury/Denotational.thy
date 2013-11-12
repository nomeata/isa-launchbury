theory Denotational
  imports "Denotational-Common" "Value-Meet" "HSemUpd" "Abstract-Denotational-Props"
begin

interpretation semantic_domain Fn Fn_project "\<Lambda> x. x".

abbreviation ESem_syn'' ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation HSem_syn' ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>f\<emptyset>"


subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed


subsubsection {* The semantics of let only adds new bindings *}

text {*
The following lemma is not as general as possible and specialized to @{text "\<rho> = fempty"}, as that is
the only case required later on, and easier to prove.
*}

lemma HSem_unfold_let:
  assumes distinct: "distinctVars ((x, body) # \<Gamma>)"
  assumes fresh: "set (bn as) \<sharp>* (x, Let as body, \<Gamma>)"
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> = (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)f|` (insert x (heapVars \<Gamma>))"
sorry
(*
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
        show ?thesis using True x' by (simp add: the_lookup_HSem_heap)
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
          by (simp add: the_lookup_HSem_other[OF x_not_as] the_lookup_HSem_heap)
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
          apply (subst the_lookup_HSem_heap)
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
*)


end
