theory DenotationalUpd
  imports "Denotational-Common" "Value-Meet" "HSemUpd"
begin

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "atom x \<sharp> \<rho> \<Longrightarrow> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<rho> f! x"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem ESem (asToHeap as) \<rho>\<^esub>"
proof-
case goal1 thus ?case
  unfolding eqvt_def ESem_graph_def
  apply rule
  apply perm_simp
  apply rule
  done
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Pair e \<rho>)
    show ?thesis 
      using Pair goal3
      apply (rule_tac y=e in exp_assn.exhaust(1))
      apply auto[1]
      apply blast
      prefer 2
      apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      done
  qed
next

case (goal4 x \<rho> e x' \<rho>' e')
  have all_fresh: "(atom x' \<rightleftharpoons> atom x) \<bullet> \<rho>' = \<rho>'" 
    using goal4
    by (auto simp add: swap_fresh_fresh)

  have tmp: "\<And> xa. ESem_sumC (e, (\<rho>(x f\<mapsto> xa))) = ESem_sumC (e', (\<rho>'(x' f\<mapsto> xa)))"
    using goal4
    apply (auto simp add: Abs1_eq_iff')

    apply (erule_tac x = xa in meta_allE)
    apply (erule_tac x = xa in meta_allE)
    apply (simp only: eqvt_at_def)
    apply auto

    apply (erule_tac x = "(atom x' \<rightleftharpoons> atom x)" in allE)
    apply (auto simp add: fmap_upd_eqvt permute_Value_def all_fresh)
    done
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
    apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>))" , OF tmp, simplified])
    apply (rule pure_fresh)+
    apply (subst spec[OF iffD1[OF meta_eq_to_obj_eq[OF eqvt_at_def] eqvt2]])
    apply (simp add:
        HSem_eqvt eqvt_apply[of _ asToHeap]
        permute_pure
        spec[OF iffD1[OF meta_eq_to_obj_eq[OF eqvt_def] asToHeap_eqvt]]
        asToHeap_eqvt)
    apply (rule arg_cong[OF HSem_cong[OF _ _ refl, rotated]])

    apply (rule perm_supp_eq)
    using fresh1 fresh2
    apply (auto simp add: fresh_star_def rho)[1]

    apply (auto simp add: permute_fun_def)
    apply (subst spec[OF iffD1[OF meta_eq_to_obj_eq[OF eqvt_at_def] eqvt1]])
    apply (subst mem_permute_iff[symmetric, of _ _ "p"])
    apply (simp add: image_eqvt)
    apply perm_simp
    apply (metis (full_types) imageI snd_conv)
    apply simp
    done
  thus "ESem_sumC (body, has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as) \<rho>) =
      ESem_sumC (body', has_ESem.HSem (\<lambda>x0 x1. ESem_sumC (x0, x1)) (asToHeap as') \<rho>')" using `\<rho>' = \<rho>`  by simp
qed auto

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by(induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order

interpretation has_ESem ESem.

lemma permute_ESem: "\<pi> \<bullet> ESem = ESem"
  by (perm_simp, rule)

lemmas HSem_eqvt' = HSem_eqvt[of _ ESem, unfolded permute_ESem]

lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt']
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt']
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]
 and   fresh_star_fmap_upd[simp] = eqvt_fresh_star_cong3[of fmap_upd, OF fmap_upd_eqvt]

end
