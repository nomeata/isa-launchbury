theory DenotationalUpd
  imports "Denotational-Common" "Value-Meet" "HSemUpd"
begin

subsubsection {* The denotational semantics *}

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "atom x \<sharp> \<rho> \<Longrightarrow> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<rho> f!\<^sub>\<bottom> x"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem ESem (asToHeap as) \<rho>\<^esub>"
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
      by (metis (full_types) "Nominal-Utils.fresh_star_singleton" exp_assn.strong_exhaust(1) supp_atom)
  qed
next

case (goal4 x \<rho> e x' \<rho>' e')
  have all_fresh: "(x' \<leftrightarrow> x) \<bullet> \<rho>' = \<rho>'"  and [simp]:"\<rho> = \<rho>'"
    using goal4
    by (auto simp add: flip_fresh_fresh)

  from goal4(7)
  have "(x' \<leftrightarrow> x) \<bullet> e = e'"
    apply (simp only: Pair_eq exp_assn.eq_iff(4) Abs1_eq_iff)
    by auto

  { fix xa
    have "ESem_sumC (e, (\<rho>(x f\<mapsto> xa))) = (x' \<leftrightarrow> x) \<bullet> (ESem_sumC (e, (\<rho>(x f\<mapsto> xa))))" by (simp add: permute_Value_def)
    also have "\<dots> = ESem_sumC ((x' \<leftrightarrow> x) \<bullet> ((e, (\<rho>(x f\<mapsto> xa)))))"
      using goal4(1) by (metis eqvt_at_def)
    also have "\<dots> = ESem_sumC ((x' \<leftrightarrow> x) \<bullet> e, \<rho>(x' f\<mapsto> xa))"
      by (simp add: all_fresh)
    also have "\<dots> = ESem_sumC (e', \<rho>'(x' f\<mapsto> xa))"
      by (simp only: `(x' \<leftrightarrow> x) \<bullet> e = e'` `\<rho> = \<rho>'`)
    finally
    have "ESem_sumC (e, (\<rho>(x f\<mapsto> xa))) = ESem_sumC (e', (\<rho>'(x' f\<mapsto> xa)))".
  }
  thus ?case by simp
next

case (goal13 as \<rho> body as' \<rho>' body')
  assume eqvt1: "\<And> e x. e \<in> snd ` set (asToHeap as) \<Longrightarrow> eqvt_at ESem_sumC (e, x)"
    and eqvt2:"eqvt_at ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>)"
    and eqvt3:"\<And>e x. e \<in> snd ` set (asToHeap as') \<Longrightarrow> eqvt_at ESem_sumC (e, x)"
    and eqvt4:"eqvt_at ESem_sumC (body', has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as') \<rho>')"

  assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
  assume "(Terms.Let as body, \<rho>) =  (Terms.Let as' body', \<rho>')"
  hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

  have "ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>) =
        ESem_sumC (body', has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as') \<rho>)"
  proof (rule Abs_lst_fcb[where ba = bn and f = "(\<lambda> as (body, as'). ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>))", OF tmp pure_fresh pure_fresh, simplified])
    fix p
    assume "p \<bullet> body = body' \<and> p \<bullet> as = as'" hence "p \<bullet> body = body'" and "p \<bullet> as = as'" by auto
    assume "supp p \<subseteq> set (bn as) \<union> set (bn as')"
    have "p \<bullet> \<rho> = \<rho>"
      apply (rule perm_supp_eq)
      using fresh1 fresh2
      apply (simp add: fresh_star_def)
      by (metis (full_types) Un_iff `supp p \<subseteq> set (bn as) \<union> set (bn as')` rho set_mp)

    have "(p \<bullet> ESem_sumC) (body', has_ESem.HSem (\<lambda>x xa. (p \<bullet> ESem_sumC) (x, xa)) (asToHeap as') (p \<bullet> \<rho>)) =
          (p \<bullet> ESem_sumC) (body', has_ESem.HSem (\<lambda>x xa. ESem_sumC (x, xa)) (asToHeap as') (p \<bullet> \<rho>))"
      apply (rule arg_cong[OF HSem_cong[OF _ refl refl]])
      apply (subst eqvt_at_apply[OF eqvt3], assumption)
      by rule
    also have "\<dots> = (p \<bullet> ESem_sumC) (body', has_ESem.HSem (\<lambda>x xa. ESem_sumC (x, xa)) (asToHeap as') \<rho>')"
      by (simp add: `p \<bullet> \<rho> = \<rho>` `\<rho>' = \<rho>`)
    also have "\<dots> = ESem_sumC (body', has_ESem.HSem (\<lambda>x xa. ESem_sumC (x, xa)) (asToHeap as') \<rho>')"
      by (rule eqvt_at_apply[OF eqvt4])
    also have "\<dots> = ESem_sumC (body', has_ESem.HSem (\<lambda>x xa. ESem_sumC (x, xa)) (asToHeap as') \<rho>)"
      by (simp add: `\<rho>' = \<rho>`)
    finally
    show "(p \<bullet> ESem_sumC) (body', has_ESem.HSem (\<lambda>x xa. (p \<bullet> ESem_sumC) (x, xa)) (asToHeap as') (p \<bullet> \<rho>)) =
               ESem_sumC (body', has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as') \<rho>)".
  qed
  thus "ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>) =
      ESem_sumC (body', has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as') \<rho>')" using `\<rho>' = \<rho>`  by simp
qed auto

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by(induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order

interpretation has_ESem ESem.

subsubsection {* Equivariance of the semantics *}

lemma permute_ESem: "\<pi> \<bullet> ESem = ESem"
  by (perm_simp, rule)

lemmas HSem_eqvt' = HSem_eqvt[of _ ESem, unfolded permute_ESem]

lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt']
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt']
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]
 and   fresh_star_fmap_upd[simp] = eqvt_fresh_star_cong3[of fmap_upd, OF fmap_upd_eqvt]

end
