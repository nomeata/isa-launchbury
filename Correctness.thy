theory Correctness
  imports "Denotational-Props" Launchbury
begin

lemma preserve_meaning:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and "x \<in> set L"
  and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  shows "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
proof(cases "x \<in> heapVars \<Gamma>")
case True
  thus ?thesis
  using fmap_less_eqD[OF `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`, of x] 
  by (auto simp add: heapVars_def)
next
case False with reds_avoids_live[OF assms(1,2)]
  have "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)" and "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)"
    by (auto intro:  the_lookup_HSem_other simp add: heapVars_def)
  thus ?thesis by simp
qed

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  using assms
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
print_cases
case Lambda
  print_cases
  case 1 show ?case by simp
  case 2 show ?case by simp
next

case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' \<rho>)

  case 1
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (subst preserve_meaning[OF `\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. e'` _ `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`], auto) also
  have "... = (\<Lambda> v. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> v)\<^esub>)\<cdot>(\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` by simp also
  have "... = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> (\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))\<^esub>"
    by simp also
  have "... = \<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` and `atom y \<sharp> x`
    by-(rule ESem_subst, simp_all add:fresh_at_base) also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>_\<^esub> = _` by simp
  finally
  show ?case .
  case 2 show ?case using `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> _` `\<lbrace>\<Delta>\<rbrace>\<rho> \<le> _`  by simp
next

case (Variable x e \<Gamma> L \<Delta> z \<rho>)
  have xnot1: "x \<notin> fst ` set (removeAll (x, e) \<Gamma>)" sorry
  have xnot2: "x \<notin> fst ` set \<Delta>" sorry

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e) # removeAll (x,e) \<Gamma>\<rbrace>\<rho>" sorry also (* Distinctness and reordering lemma needed *)
  have "... = fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>)))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set (removeAll (x, e) \<Gamma>)) (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'a\<^esub>)))"                           
    by (rule iterative_HSem[OF _ xnot1]) also (* Alternative definition needs to be proven *)
  have "... = fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>)))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set (removeAll (x, e) \<Gamma>)) (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>'a\<^esub>)))"
    sorry also (* Unfolding a bit under the fixed point, as in 5.2.1 *)
  have "... = fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>)))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set (removeAll (x, e) \<Gamma>)) (\<lbrace>removeAll (x, e) \<Gamma>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'a\<^esub>)))"
    by (subst  Variable.hyps(3), rule refl) also
  have "... \<le> fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, e) # removeAll (x, e) \<Gamma>)))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set (removeAll (x, e) \<Gamma>)) (\<lbrace>\<Delta>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'a\<^esub>)))"
    using Variable.hyps(4)
    (* \<le> and fix1 *)
    sorry also
  have "... \<le> fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>) ))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set \<Delta>) (\<lbrace>\<Delta>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'a\<^esub>)))"
    (* Extending the domain *)
    sorry also
  have "... \<le> fix1 (fmap_bottom (fdom \<rho> \<union> fst ` set ((x, z) # \<Delta>) ))
                   (\<Lambda> \<rho>'a. fmap_update \<rho>
                            (fmap_restr (fst ` set \<Delta>) (\<lbrace>\<Delta>\<rbrace>\<rho>'a)(x f\<mapsto> \<lbrakk> z \<rbrakk>\<^bsub>\<rho>'a\<^esub>)))"
    (* Again 5.2.1 *)
    sorry also
  have  "... = \<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>"
    by (rule iterative_HSem[OF xnot2,symmetric])
  finally show part2: ?case.

  case 1
  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup (\<lbrace>\<Gamma>\<rbrace>\<rho>) x)" by simp also
  have "... = the (lookup (\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>) x)"
    using part2 (* Definition of \<le> and existence of x in \<Gamma> *)
    sorry also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (subst HSem_unroll, auto)
  finally show ?case.
next

case (Let as \<Gamma> L body \<Delta> z \<rho>)
  have "set (bn as) \<sharp>* \<rho>" sorry (* Problem: How to achieve this? *)
  with `set (bn as) \<sharp>* \<Gamma>`
  have "set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)" sorry  

  case 1
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule Esem_simps4[OF `set (bn as) \<sharp>* (\<lbrace>\<Gamma>\<rbrace>\<rho>)`]) also
  have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>\<^esub>" sorry also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" by fact
  finally show ?case .

  case 2
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<rho>" sorry also
  have "... \<le> \<lbrace>\<Delta>\<rbrace>\<rho>" by fact
  finally show ?case .

qed

end


