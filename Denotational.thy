theory Denotational
  imports "Denotational-Common"
begin

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>heapExtend \<rho> (asToHeap as) ESem\<^esub>"
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
    and eqvt2:"eqvt_at ESem_sumC (body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
    and eqvt3:"\<And>e x. e \<in> snd ` set (asToHeap as') \<Longrightarrow> eqvt_at ESem_sumC (e, x)"
    and eqvt4:"eqvt_at ESem_sumC (body', heapExtend \<rho>' (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"

  assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
  assume "(Terms.Let as body, \<rho>) =  (Terms.Let as' body', \<rho>')"
  hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

  have "ESem_sumC (body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
        ESem_sumC (body', heapExtend \<rho> (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
    apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem_sumC (body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))))" , OF tmp, simplified])
    apply (rule pure_fresh)+
    apply (erule conjE)
    using fresh2[unfolded rho]
    proof-
      fix \<pi>
      assume body: "\<pi> \<bullet> body = body'"
      assume as: "\<pi> \<bullet> as = as'"
      assume "set (bn as') \<sharp>* \<rho>" with fresh1
      have "(set (bn as) \<union> set (bn as')) \<sharp>* \<rho>" by (metis fresh_star_Un)
      moreover
      assume "supp \<pi> \<subseteq> set (bn as) \<union> set (bn as')"
      ultimately
      have "\<pi> \<bullet> \<rho> = \<rho>"
        using as
        apply -
        apply (rule perm_supp_eq)
        apply (auto intro: perm_supp_eq simp add: fresh_star_def)
        done            
      thus "\<pi> \<bullet> ESem_sumC (body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
             ESem_sumC (body', heapExtend \<rho> (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))"
         using as body
         apply (simp add: eqvt2[unfolded eqvt_at_def, simplified, rule_format]   asToHeap.eqvt heapExtend_eqvt)
         apply (subst heapExtend_cong)
         prefer 4
         apply (rule refl)+
         apply (simp add: permute_fun_def)
         apply rule
         apply (subst eqvt1[unfolded eqvt_at_def, simplified, rule_format])
         defer
         apply simp
         apply (subst mem_permute_iff[symmetric, of _ _ "\<pi>"])
         apply (simp add: image_eqvt)
         apply perm_simp
         using as
         apply simp
         done
    qed
  thus "ESem_sumC (body, heapExtend \<rho> (asToHeap as) (\<lambda>x0 x1. ESem_sumC (x0, x1))) =
      ESem_sumC (body', heapExtend \<rho>' (asToHeap as') (\<lambda>x0 x1. ESem_sumC (x0, x1)))" using `\<rho>' = \<rho>`  by simp
qed auto

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by(induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order


lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and True
proof(nominal_induct e and avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (ESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    by (intro cont2cont cont_compose[OF `cont (ESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (ESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ Var.prems(2)])    
next
case (Let as e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)
  show ?case
    by (simp, intro contE[OF _ Let.prems(2)] cont2cont cont_compose[OF `cont (ESem e)`])
qed simp

lemma ESem_cont: "cont (ESem e)"  using ESem_cont'[OF refl] by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]


definition HSem ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> = heapExtend \<rho> \<Gamma> ESem"

lemma Esem_simps4[simp]: "set (bn as) \<sharp>* \<rho> \<Longrightarrow> \<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as \<rbrace>\<rho>\<^esub>"
  by (simp add: HSem_def)

lemma HSem_def': "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_update \<rho> (fix1 (fmap_bottom (fst ` set \<Gamma>)) (\<Lambda> \<rho>'. heapToEnv \<Gamma> (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>fmap_update \<rho> \<rho>'\<^esub>))) "
  unfolding HSem_def heapExtend_def by simp

declare ESem.simps(4)[simp del]

end
