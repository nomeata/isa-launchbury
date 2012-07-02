theory "Denotational-Mutual"
  imports "Denotational-Common"
begin


nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
and
  HSem :: "heap => Env => Env" ("\<lbrace> _ \<rbrace>_"  [60,60] 60) 
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk> Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> body\<rbrakk>\<^bsub>\<lbrace> asToHeap as \<rbrace>\<rho>\<^esub>"
| "\<lbrace> h \<rbrace>\<rho> = heapExtend \<rho> h ESem"
proof-
have eqvt_at_ESem: "\<And> a b . eqvt_at ESem_HSem_sumC (Inl (a, b)) \<Longrightarrow> eqvt_at (\<lambda>(a, b). ESem a b) (a, b)" sorry
have eqvt_at_HSem: "\<And> a b . eqvt_at ESem_HSem_sumC (Inr (a, b)) \<Longrightarrow> eqvt_at (\<lambda>(a, b). HSem a b) (a, b)" sorry
{

case goal1 thus ?case
  unfolding eqvt_def ESem_HSem_graph_def
  apply rule
  apply perm_simp
  sorry (* :-( *)

(* Exhaustiveness *)
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Inl a)
    show ?thesis
    proof(cases a)
    case (Pair e \<rho>)
      show ?thesis 
        using Pair Inl goal3
        apply (rule_tac y=e in exp_assn.exhaust(1))
        apply auto[1]
        apply blast
        prefer 2
        apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
        apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
        done
    qed
  next
  case (Inr a) thus ?thesis using goal3
    apply(case_tac a)
    apply metis
    done
  qed
next
case (goal4 x \<rho> e x' \<rho>' e')
  have eqvt1: "(\<And>xa. eqvt_at (\<lambda>(a, b). ESem a b) (e, \<rho>(x f\<mapsto> xa)))" using goal4 by -(rule eqvt_at_ESem)
  have eqvt2: "(\<And>xa. eqvt_at (\<lambda>(a, b). ESem a b) (e', \<rho>'(x' f\<mapsto> xa)))"  using goal4 by -(rule eqvt_at_ESem)

  have tmp2: "[[atom x]]lst. e = [[atom x']]lst. e'" and rho_eq:"\<rho> = \<rho>'"  using goal4(7) by auto  

  have all_fresh: "(atom x' \<rightleftharpoons> atom x) \<bullet> \<rho>' = \<rho>'" 
    using goal4 `\<rho> = \<rho>'`
    by (auto simp add: swap_fresh_fresh)

  have tmp: "\<And> xa. ESem e (\<rho>(x f\<mapsto> xa)) = ESem e' (\<rho>'(x' f\<mapsto> xa))"
    using eqvt1 eqvt2 tmp2 rho_eq goal4(5) goal4(6)
    apply (simp add: Abs1_eq_iff')
    apply auto

    apply (erule_tac x = xa in meta_allE)
    apply (erule_tac x = xa in meta_allE)
    apply (simp only: eqvt_at_def)
    apply auto

    apply (erule_tac x = "(atom x' \<rightleftharpoons> atom x)" in allE)
    apply (auto simp add: fmap_upd_eqvt permute_Value_def all_fresh)
    done

   show ?case
    apply (simp only: meta_eq_to_obj_eq[OF ESem_def, symmetric, unfolded fun_eq_iff]
      meta_eq_to_obj_eq[OF HSem_def, symmetric, unfolded fun_eq_iff])
    (* No _sum any more at this point! *)
    by (subst tmp, rule)
next
case (goal16 as \<rho> body as' \<rho>' body')
  thus ?case
    apply -
    apply (drule eqvt_at_ESem)
    apply (drule eqvt_at_ESem)
    apply (drule eqvt_at_HSem)
    apply (drule eqvt_at_HSem)
    apply (simp only: meta_eq_to_obj_eq[OF ESem_def, symmetric, unfolded fun_eq_iff]
      meta_eq_to_obj_eq[OF HSem_def, symmetric, unfolded fun_eq_iff])
    (* No _sum any more at this point! *)
    proof- 
      assume eqvt1: "eqvt_at (\<lambda>(a, b). ESem a b) (body, HSem (asToHeap as) \<rho>)"
      assume eqvt2: "eqvt_at (\<lambda>(a, b). ESem a b) ( body', HSem (asToHeap as') \<rho>')"
      assume eqvt3: "eqvt_at (\<lambda>(a, b). HSem a b) (asToHeap as, \<rho>)"
      assume eqvt4: "eqvt_at (\<lambda>(a, b). HSem a b) (asToHeap as', \<rho>')"
      assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
      assume "Inl (Terms.Let as body, \<rho>) = Inl (Terms.Let as' body', \<rho>')"
      hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

      thm Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem body (HSem (asToHeap as) \<rho>))" , OF tmp, simplified]
      thm Abs_lst_fcb2[of "(bn as)" _ "(bn as')"]
      have "ESem body (HSem (asToHeap as) \<rho>) = ESem body' (HSem (asToHeap as') \<rho>)"
        apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem body (HSem (asToHeap as) \<rho>))" , OF tmp, simplified])
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
          thus "\<pi> \<bullet> ESem body (HSem (asToHeap as) \<rho>) = ESem (\<pi> \<bullet> body) (HSem (asToHeap (\<pi> \<bullet> as)) \<rho>)"
             by (simp only: eqvt1[unfolded eqvt_at_def, simplified, rule_format]
                            eqvt3[unfolded eqvt_at_def, simplified, rule_format]
                            asToHeap.eqvt)
        qed
        thus "Inl (ESem body (HSem (asToHeap as) \<rho>)) =
              Inl (ESem body' (HSem (asToHeap as') \<rho>'))" using `\<rho>' = \<rho>`
        by simp
    qed
}
qed auto

lemma [simp]:"set (bn as) \<sharp>* \<rho> \<Longrightarrow> list_size (\<lambda>p. size (snd p)) (asToHeap as) < Suc (size as + size body)"
  by(induct as rule:exp_assn.inducts(2), auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order

lemma sharp_Env: "atom (x::var) \<sharp> (\<rho> :: Env) \<longleftrightarrow> x \<notin> fdom \<rho>"
  apply (subst fresh_def)
  apply (simp  add: supp_fmap)
  apply (subst (1 2) fresh_def[symmetric])
  apply (simp add: fresh_finite_set_at_base[OF finite_fdom] pure_fresh)
  done

lemma sharp_star_Env: "set (bn as) \<sharp>* (\<rho> :: Env) \<longleftrightarrow> (\<forall> x \<in> fst`set (asToHeap as) . x \<notin> fdom \<rho>)"
  by(induct rule:asToHeap.induct, auto simp add: fresh_star_def exp_assn.bn_defs sharp_Env)

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


end
