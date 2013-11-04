
theory Denotational
  imports "Denotational-Common" "Value-Meet" "HSemUpd" "Abstract-Denotational-Props"
begin

interpretation semantic_domain "\<lambda>x. Fn$x" "\<lambda>x y. Fn_project$x$y" "\<lambda> x. x".
interpretation cont_semantic_domain "\<lambda>x. Fn$x" "\<lambda>x y. Fn_project$x$y" "\<lambda> x. x"
  by unfold_locales simp_all
declare cont_semantic_domain_conts[simp del, cont2cont del]


abbreviation ESem ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> AESem e \<rho>"

(*
lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt']
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt']
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]
*)


notation AHSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60)
notation AHSem_fempty ("\<lbrace>_\<rbrace>"  [60] 60)

subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule UHSem_subst_expr)
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair fresh_fmap_pure fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst UHSem_eq, simp)
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst UHSem_eq, simp)
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule UHSem_subst_expr)
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair fresh_fmap_pure fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst UHSem_eq, simp)
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst UHSem_eq, simp)
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
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>"
proof (rule iffD2[OF fmap_less_restrict])
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
    proof (rule UHSem_fempty_below)
      have "fdom ?r = insert x (heapVars \<Gamma>)" by auto
      hence [simp]: "set (bn as) \<sharp>* ?r" using disjoint by (auto simp add: set_bn_to_atom_heapVars fresh_star_def fresh_fmap_pure)

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
          by (rule arg_cong[OF UHSem_reorder_head_append[OF x_not_as]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<^esub>"
          by (rule arg_cong[OF UHSem_redo[where \<rho> = "f\<emptyset>" and \<Delta> = "(x, body) # \<Gamma>", simplified]])
        also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
          by (rule arg_cong[OF UHSem_reorder_head_append[OF x_not_as], symmetric])
        finally
        show ?thesis using True x' by (simp add: the_lookup_UHSem_heap)
      next
        case False thus ?thesis
        apply (subst (2) UHSem_eq)
        using x'
        apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as] lookupHeapToEnv Gamma_eq[OF the_map_of_snd])
        done
      qed
    qed auto

    have [simp]: "set (bn as) \<sharp>* (\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>)"
      apply (rule HSem_fresh_star)
      using fresh by (auto simp add: fresh_star_Pair fresh_star_list)

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>" (is "_ \<sqsubseteq> ?r")
    proof (rule UHSem_fempty_below)
      fix x'
      assume "x' \<in> heapVars ((x, body) # asToHeap as @ \<Gamma>)"
      hence x': "x' = x \<or> x' \<in> heapVars (asToHeap as) \<or> x' \<in> heapVars \<Gamma>" by simp

      show "\<lbrakk> the (map_of ((x, body) # asToHeap as @ \<Gamma>) x') \<rbrakk>\<^bsub>?r\<^esub> \<sqsubseteq> ?r f! x'"
      proof(cases "x' = x")
        assume "x' = x"
        thus ?thesis
          by (simp add: the_lookup_UHSem_other[OF x_not_as] the_lookup_UHSem_heap)
      next
        have merged_r: "?r = \<lbrace>asToHeap as @ ((x, Let as body) # \<Gamma>)\<rbrace>"
          apply (rule UHSem_merge)
            using disjoint distinct apply (auto simp add: distinctVars_Cons distinctVars_append)[1]
            using fresh apply (metis fresh_star_list(2) fempty_fresh_star fresh_star_Pair set_bn_to_atom_heapVars)              
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
          apply (subst the_lookup_UHSem_heap)
          using x' apply simp[1]
          unfolding map_of_reorder
          apply (rule below_refl)
          done
      qed
    qed auto
    thus "fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_UHSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>", simplified (no_asm)])
      using disjoint apply auto
      done
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed



end
