theory Denotational
  imports "Denotational-Common"
begin

term heapExtend
lemma heapExtend_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtend env1 heap1 eval1 = heapExtend env2 heap2 eval2"
      sorry

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk> Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Let as body\<rbrakk>\<^bsub>heapExtend \<rho> (asToHeap as) ESem\<^esub>"
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
  assume eqvt: "\<And> a b. eqvt_at ESem_sumC (a, b)"
  assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
  assume "(Terms.Let as body, \<rho>) =  (Terms.Let as' body', \<rho>')"
  hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

  thm Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem_sumC (Let as' body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))))" , OF tmp, simplified]
  thm Abs_lst_fcb2[of "(bn as)" _ "(bn as')"]
  have "ESem_sumC (Terms.Let as body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
        ESem_sumC (Terms.Let as' body', heapExtend \<rho> (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
    apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem_sumC (Let as' body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))))" , OF tmp, simplified])
    apply (rule pure_fresh)+
    using fresh2[unfolded rho]
    apply (clarify)
    proof-
      fix \<pi>
      assume "set (bn (\<pi> \<bullet> as)) \<sharp>* \<rho>" with fresh1
      have "(set (bn as) \<union> set (bn (\<pi> \<bullet> as))) \<sharp>* \<rho>" by (metis fresh_star_Un)
      moreover
      assume "supp \<pi> \<subseteq> set (bn as) \<union> set (bn (\<pi> \<bullet> as))"
      ultimately
      have "\<pi> \<bullet> \<rho> = \<rho>"
        apply -
        apply (rule perm_supp_eq)
        apply (auto intro: perm_supp_eq simp add: fresh_star_def)
        done            
      thus "\<pi> \<bullet> ESem_sumC (Terms.Let as body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
             ESem_sumC (Terms.Let (\<pi> \<bullet> as) (\<pi> \<bullet> body), heapExtend \<rho> (asToHeap (\<pi> \<bullet> as)) (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
         apply  (simp add: eqvt[unfolded eqvt_at_def, simplified, rule_format]   asToHeap.eqvt)
         apply (subst heapExtend_eqvt)
         defer
         unfolding permute_fun_def
         apply  (simp add: eqvt[unfolded eqvt_at_def, simplified, rule_format]   asToHeap.eqvt)
         (* Goal:  \<And>e. \<pi> \<bullet> \<rho> = \<rho> \<Longrightarrow> cont (\<lambda>x1. ESem_sumC (e, x1)) *)
         done
    qed
  thus "ESem_sumC (Terms.Let as body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
      ESem_sumC (Terms.Let as' body', heapExtend \<rho>' (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))" using `\<rho>' = \<rho>`  by simp
qed auto


termination (eqvt) proof

find_theorems ESem

end
