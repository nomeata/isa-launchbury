theory AbstractDenotational
imports Terms Heap "HeapSemantics"
begin


subsubsection {* The denotational semantics for expressions *}

locale semantic_domain =
  fixes Fn :: "('Value \<rightarrow> 'Value) \<rightarrow> ('Value::{pcpo_pt,pure})"
  fixes Fn_project :: "'Value \<rightarrow> ('Value \<rightarrow> 'Value)"
  fixes tick :: "'Value \<rightarrow> 'Value"
begin

nominal_primrec
  ESem :: "exp \<Rightarrow> (var \<Rightarrow> 'Value) \<rightarrow> 'Value"
where
  (* Restrict \<rho> to avoid having to demand atom x \<sharp> \<rho> *)
 "ESem (Lam [x]. e) = (\<Lambda> \<rho>. tick \<cdot> (Fn \<cdot> (\<Lambda> v. ESem e \<cdot> ((\<rho> f|` fv (Lam [x]. e))(x := v)))))"
  (* Do not use \<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>  in the rule for App; it costs an additional
     resource and makes the adequacy proof difficult. *)
| "ESem (App e x) = (\<Lambda> \<rho>. tick \<cdot> (Fn_project \<cdot> (ESem e \<cdot> \<rho>) \<cdot> (\<rho> x)))"
| "ESem (Var x) = (\<Lambda> \<rho>. tick \<cdot> (\<rho> x))"
  (* Restrict \<rho> to avoid having to demand set (bn as) \<sharp>* \<rho> *)
| "ESem (Let as body) = (\<Lambda> \<rho>. tick \<cdot> (ESem body \<cdot> (has_ESem.HSem ESem (asToHeap as) \<cdot>  (\<rho> f|` fv (Let as body)))))"
proof-
txt {* The following proofs discharge technical obligations generated by the Nominal package. *}

case goal1 thus ?case
  unfolding eqvt_def ESem_graph_aux_def
  apply rule
  apply (perm_simp)
  apply (simp add: Abs_cfun_eqvt)
  done
next
case (goal3 P x)
  thus ?case by (metis (no_types) exp_assn.strong_exhaust(1))
next

case (goal4 x e x' e')
  from goal4(5)
  have "(x = x' \<and> e = e' \<or> x \<noteq> x' \<and> e = (x \<leftrightarrow> x') \<bullet> e' \<and> atom x \<sharp> e')"
    by (simp only: Pair_eq exp_assn.eq_iff(4) Abs1_eq_iff)
  thus ?case
  proof (elim conjE disjE)
    assume "x \<noteq> x'"
    assume "e = (x \<leftrightarrow> x') \<bullet> e'"
    hence [simp]: "(x' \<leftrightarrow> x) \<bullet> e = e'" by simp
    assume "atom x \<sharp> e'" 
    hence "x \<notin> fv e'" unfolding fv_not_fresh.

    { fix xa \<rho>
      have "ESem_sumC e \<cdot> ((\<rho> f|` fv (Lam [x]. e))(x := xa)) = (x' \<leftrightarrow> x) \<bullet> ESem_sumC e \<cdot> ((\<rho> f|` fv (Lam [x]. e))(x := xa))" by (simp add: permute_pure)
      also have "\<dots> = ((x' \<leftrightarrow> x) \<bullet> ESem_sumC) e' \<cdot> ((((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` (fv e' - {x'}))(x' := xa))" by simp
      also have "((x' \<leftrightarrow> x) \<bullet> ESem_sumC) e' = ESem_sumC e'"
        by (rule eqvt_at_apply[OF goal4(2)])
      also have "((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` (fv e' - {x'}) = \<rho> f|` (fv e' - {x'})"
        by (rule fmap_restr_flip) (auto simp add: `x \<notin> fv e'`)
      also have "fv e' - {x'} = fv (Lam [x']. e')" by simp
      finally
      have "ESem_sumC e\<cdot>((\<rho> f|` fv (Lam [x]. e))(x := xa)) = ESem_sumC e'\<cdot>((\<rho> f|` fv (Lam [x']. e'))(x' := xa))".
    }
    thus ?thesis by simp
  qed simp
next

case (goal13 as body as' body')
  assume eqvt1: "\<And> x e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> eqvt_at ESem_sumC e"
    and eqvt2: "\<And> x. eqvt_at ESem_sumC body"
    and eqvt3:"\<And> x e. e \<in> snd ` set (asToHeap as') \<Longrightarrow> eqvt_at ESem_sumC e"
    and eqvt4:"\<And> x. eqvt_at ESem_sumC body'"

  (* assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'" *)
  assume "Let as body = Let as' body'"
  hence "[bn as]lst. (body, as) = [bn as']lst. (body', as')" by auto
  then obtain p
    where "(supp (body', as') - set (bn as')) \<sharp>* p"
    and [simp]: "p \<bullet> body = body'"
    and [simp]: "p \<bullet> as = as'"
    unfolding  Abs_eq_iff(3) alpha_lst.simps by auto

  from this(1)
  have *: "supp p \<sharp>* (fv (Terms.Let as' body') :: var set)"
    by (auto simp add: fresh_star_def fresh_def supp_finite_set_at_base supp_Pair fv_supp_exp fv_supp_as set_bn_to_atom_domA)

  { fix \<rho>
  have "ESem_sumC body \<cdot> (has_ESem.HSem ESem_sumC (asToHeap as) \<cdot> (\<rho> f|` fv (Let as body)))
      = p \<bullet> ESem_sumC body \<cdot> (has_ESem.HSem ESem_sumC (asToHeap as) \<cdot> (\<rho> f|` fv (Let as body)))"
    by (rule permute_pure[symmetric])
  also have "\<dots> = (p \<bullet> ESem_sumC) body' \<cdot> (has_ESem.HSem (p \<bullet> ESem_sumC) (asToHeap as') \<cdot>  ((p \<bullet> \<rho>) f|` fv (Let as' body')))"
    by simp
  also have "has_ESem.HSem (p \<bullet> ESem_sumC) (asToHeap as') = has_ESem.HSem ESem_sumC (asToHeap as')"
    by (rule HSem_cong[OF eqvt_at_apply[OF eqvt3] refl])
  also have "(p \<bullet> \<rho>) f|` fv (Let as' body') = \<rho> f|`  fv (Let as' body')"
    by (rule fmap_restr_perm[OF *], simp)
  also have "(p \<bullet> ESem_sumC) body' = ESem_sumC body'"
    by (rule eqvt_at_apply[OF eqvt4])
  finally
  have "ESem_sumC body\<cdot>(has_ESem.HSem ESem_sumC (asToHeap as)\<cdot>(\<rho> f|` fv (Terms.Let as body))) =
        ESem_sumC body'\<cdot>(has_ESem.HSem ESem_sumC (asToHeap as')\<cdot>(\<rho> f|` fv (Terms.Let as' body')))".
  }
  thus ?case  by simp
qed auto
termination (in semantic_domain) (eqvt) by lexicographic_order

sublocale has_ESem ESem.

abbreviation ESem_syn' ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation EvalHeapSem_syn'  ("\<^bold>\<lbrakk> _ \<^bold>\<rbrakk>\<^bsub>_\<^esub>"  [0,0] 110)  where "\<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> evalHeap \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
abbreviation AHSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation AHSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>\<bottom>"

subsubsection {* Equivariance of the semantics *}

lemma permute_ESem: "\<pi> \<bullet> ESem = ESem"
  by (perm_simp, rule)

lemmas HSem_eqvt' = HSem_eqvt[of _ ESem, unfolded permute_ESem]

lemmas asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   asToHeap_fresh_star[simp] = eqvt_fresh_star_cong1[of asToHeap, OF asToHeap.eqvt]
(* and   fresh_fun_upd[simp] = eqvt_fresh_cong3[of fun_upd, OF fun_upd_eqvt] *)

end

end

