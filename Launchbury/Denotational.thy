theory Denotational
  imports "Denotational-Common" "Value-Meet" "HSem"  "Abstract-Denotational-Props"
begin

(*

subsubsection {* The denotational semantics for expressions *}

definition fun_restr :: "var set \<Rightarrow> (var \<Rightarrow> 'a::{pure_cpo,pcpo}) \<Rightarrow> (var \<Rightarrow> 'a)"
  where "fun_restr S f v = (if v \<in> S then f v else \<bottom>)"

abbreviation fun_restr_syn ("_|\<^bsub>_\<^esub>" [111,0]) where "f|\<^bsub>S\<^esub> \<equiv> fun_restr S f"

term "x |` y"
lemma fun_restr_eqvt[eqvt]: "\<pi> \<bullet> (f|\<^bsub>S\<^esub> v) = (\<pi> \<bullet> f)|\<^bsub>\<pi> \<bullet> S\<^esub> (\<pi> \<bullet> v)"
  unfolding fun_restr_def by auto

nominal_primrec
  ESem :: "exp \<Rightarrow> (var \<Rightarrow> Value) \<Rightarrow> Value" ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^bsub>fv (Lam [x]. e)\<^esub>(x := v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<rho> x"
| "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = undefined"
(* | "set (bn as) \<sharp>* \<rho> \<Longrightarrow>
  \<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem ESem (asToHeap as) \<rho>\<^esub>" *)
proof-
txt {* The following proofs discharge technical obligations generated by the Nominal package. *}

case goal1 thus ?case
  unfolding eqvt_def ESem_graph_aux_def by simp
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Pair e \<rho>)
    show ?thesis
      using Pair goal3
      by (metis (full_types) exp_assn.exhaust(1))
  qed
next

case (goal4 x e \<rho> x' e' \<rho>')
  from goal4(5)
  have "\<rho> = \<rho>'" by simp

  from goal4(5)
  have "(x = x' \<and> e = e' \<or> x \<noteq> x' \<and> e = (x \<leftrightarrow> x') \<bullet> e' \<and> atom x \<sharp> e')"
    by (simp only: Pair_eq exp_assn.eq_iff(4) Abs1_eq_iff)
  thus ?case
  proof (elim conjE disjE)
    assume "x \<noteq> x'"
    assume "e = (x \<leftrightarrow> x') \<bullet> e'"
    hence "(x' \<leftrightarrow> x) \<bullet> e = e'" by simp
    assume "atom x \<sharp> e'" 
    hence "x \<notin> fv e'" unfolding fv_not_fresh.

    { fix xa
      have "ESem_sumC (e, ((fun_restr (fv (Lam [x]. e)) \<rho>)(x := xa))) = (x' \<leftrightarrow> x) \<bullet> (ESem_sumC (e, ((fun_restr (fv (Lam [x]. e)) \<rho>)(x := xa))))" by (simp add: permute_pure)
      also have "\<dots> = ESem_sumC ((x' \<leftrightarrow> x) \<bullet> ((e, (fun_restr (fv (Lam [x]. e)) \<rho>)(x := xa))))"
        using goal4(1) by (metis eqvt_at_def)
      also have "\<dots> = ESem_sumC ((x' \<leftrightarrow> x) \<bullet> e, (fun_restr (fv ((x' \<leftrightarrow> x) \<bullet> e) - {x'}) ((x' \<leftrightarrow> x) \<bullet> \<rho>))(x' := xa))"
        by simp
      also note `_ = e'`
      also have "fun_restr (fv e' - {x'}) ((x' \<leftrightarrow> x) \<bullet> \<rho>) = fun_restr (fv e' - {x'}) \<rho>'"
        apply rule
        apply (auto simp add: fun_restr_def `\<rho> = \<rho>'`)
        by (metis eqvt_bound eqvt_lambda flip_at_base_simps(3) permute_flip_cancel2 permute_pure  `x \<notin> fv e'`)
      also have "fv e' - {x'} = fv (Lam [x']. e')" by simp
      finally
      have "ESem_sumC (e, ((fun_restr (fv (Lam [x]. e)) \<rho>)(x := xa))) = ESem_sumC (e', (fun_restr (fv (Lam [x']. e')) \<rho>')(x' := xa))".
    }
    thus ?thesis by simp
  qed (simp add: `\<rho> = \<rho>'`)
next
thm Abs_eq_iff
thm Abs_eq_iff[unfolded alpha_lst.simps]
*)

interpretation semantic_domain "\<lambda>x. Fn$x" "\<lambda>x y. Fn_project$x$y" "\<lambda> x. x".
interpretation cont_semantic_domain "\<lambda>x. Fn$x" "\<lambda>x y. Fn_project$x$y" "\<lambda> x. x"
  by unfold_locales simp_all

abbreviation ESem ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> AESem e \<rho>"

(*
lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt']
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt']
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]
*)

(* Re-Do the abbreviation from inside the the locale, as abbreviations are not exported *)
abbreviation HSem_cond''
  where "HSem_cond'' h \<rho> \<equiv>
      fix_join_cond (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) 
                        (\<lambda> \<rho>' . heapToEnv h (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"


notation HSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60)
notation HSem_fempty ("\<lbrace>_\<rbrace>"  [60] 60)

subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes cond1: "HSem_cond' ((x, App (Var n) y) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, App e y) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes cond1: "HSem_cond' ((x, Var n) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, e) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
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
      apply (rule ESem_ignores_fresh[OF fmap_restr_less])
      apply (subst fdom_fmap_restr)
      apply (subst simp1)
      apply (subst simp2)
      apply (rule fresh_e)
      done
  } note Gamma_eq = this

case goal1
  have "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> = fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)"
  proof(rule below_antisym)
    show "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> \<sqsubseteq> fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)" (is "_ \<sqsubseteq> ?r")
    proof (rule HSemb_below[OF eq_imp_below])

      have "fdom ?r = insert x (heapVars \<Gamma>)" by auto
      hence [simp]: "set (bn as) \<sharp>* ?r"
        using disjoint
        by (auto simp add: set_bn_to_atom_heapVars fresh_star_def sharp_Env)

      show "heapToEnv ((x, Terms.Let as body) # \<Gamma>) (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>?r\<^esub>) = ?r"
      proof
      case goal1 show ?case by auto
      case (goal2 x')
        hence x': "x' \<in> insert x (heapVars \<Gamma>)" by simp

        hence x'_not_as:"x' \<notin> heapVars (asToHeap as)"
          using disjoint
          by auto

        show ?case
        proof(cases "x' = x")
        case True 
          have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>?r\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>?r\<^esub>" by simp
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>))\<^esub>"
            by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as]])
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<^esub>"
            apply (rule arg_cong) back
            apply (rule HSemb_redo[where \<Delta> = "(x, body) # \<Gamma>", OF disjoint_is_HSem_cond, simplified (no_asm)])
            using disjoint by auto
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
            by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as], symmetric])
          finally
          show ?thesis using True x' by simp
        next
          case False thus ?thesis
          apply (subst (2) HSemb_eq)
          using x'
          apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as] lookupHeapToEnv Gamma_eq[OF the_map_of_snd])
          done
        qed
      qed
    qed
  
    have [simp]: "set (bn as) \<sharp>* (\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>)"
      apply (rule HSem_fresh_star)
      using fresh by (auto simp add: fresh_star_Pair fresh_star_list)

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>" (is "_ \<sqsubseteq> ?r")
    proof (rule HSemb_below[OF eq_imp_below])
      show "heapToEnv ((x, body) # asToHeap as @ \<Gamma>) (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>?r\<^esub>) = ?r"
      proof(rule fmap_eqI)
      case goal1 show ?case by auto
      next
      case (goal2 x')
        from goal2 have x': "x' = x \<or> x' \<in> heapVars (asToHeap as) \<or> x' \<in> heapVars \<Gamma>" by simp
        show ?case
        proof(cases "x' = x")
          assume "x' = x"
          thus ?case
            by (simp add: the_lookup_HSem_other[OF x_not_as])
        next
          have merged_r: "?r = \<lbrace>asToHeap as @ ((x, Let as body) # \<Gamma>)\<rbrace>"
            apply (rule HSem_merge)
              using disjoint distinct apply (auto simp add: distinctVars_Cons distinctVars_append)[1]
              using fresh apply (metis fresh_star_list(2) fempty_fresh_star fresh_star_Pair set_bn_to_atom_heapVars)              
              apply simp
           done

          assume "x' \<noteq> x"
          hence map_of_reorder: "map_of ((x, body) # asToHeap as @ \<Gamma>) x' = map_of (asToHeap as @ ((x, Let as body) # \<Gamma>)) x'"
            apply simp
            apply (subst map_add_upd_left)
            apply (metis dom_map_of_conv_heapVars x_not_as)
            apply simp
            done

          show ?case
            unfolding merged_r
            apply (subst (2) HSemb_eq)
            apply (subst (1 2) lookupHeapToEnv)  using x' apply simp_all[2]
            apply (rule arg_cong[OF map_of_reorder])
            done 
        qed
      qed
    qed  
    thus "fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_HSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>", simplified (no_asm)])
      using disjoint apply auto
      done 
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed


end
