theory Correctness
  imports "CorrectnessStacked" "Launchbury-Unstack"
begin

text {* Fresh bindings can be added to the heap *}

lemma ESem_add_fresh:
  assumes fresh: "atom x \<sharp> (\<Gamma>, e)"
  and "x \<notin> fdom \<rho>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
proof(rule ESem_ignores_fresh[symmetric])
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) "
    apply (rule HSem_add_fresh[OF _ `x \<notin> fdom \<rho>`, symmetric])
    using fresh by (simp add: fresh_Pair)
  thus "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (auto simp add: fmap_less_restrict)

  have "(insert x (fdom \<rho> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Gamma>)) = {x}"
    using fresh `x \<notin> fdom \<rho>` by (auto simp add: fresh_Pair  heapVars_not_fresh)
  thus "atom ` (fdom (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) - fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>)) \<sharp>* e"
    using fresh
    by (simp add: fresh_star_def fresh_Pair)
qed

text {*
As a corollary of the correctness of the stacked semantics and its equivalence to the original
semantics we obtaim Theorem 2 from \cite{launchbury}.
*}

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and [simp]:"distinctVars \<Gamma>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>\<rbrace>"
proof-
  obtain x :: var where fresh: "atom x \<sharp> (\<Gamma>,e,\<Delta>,z)"
    by (rule obtain_fresh)

  have "\<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z"
    by (rule reds_add_var_L[OF assms(1) fresh], simp)
  hence "\<Gamma> : [(x, e)] \<Down> \<Delta> : [(x, z)]"
    by (rule add_stack, simp_all add: supp_Nil)
  moreover
  from fresh
  have "x \<notin> heapVars \<Gamma>"
    by (metis heapVars_not_fresh fresh_Pair)
  hence "distinctVars ([(x, e)] @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  ultimately
  have le: "\<lbrace>[(x, e)] @ \<Gamma>\<rbrace> \<le> \<lbrace>[(x, z)] @ \<Delta>\<rbrace>"
    by (rule CorrectnessStacked.correctness)

  have "\<lbrace>\<Gamma>\<rbrace> = fmap_restr (heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>)"
    apply (rule HSem_add_fresh[where \<rho> = "f\<emptyset>", simplified, symmetric])
    using fresh apply (simp add: fresh_Pair)
    done
  also have "... \<le> fmap_restr (heapVars \<Delta>) (\<lbrace>(x, z) # \<Delta>\<rbrace>)"
    by (rule fmap_restr_le[OF le Launchbury.reds_doesnt_forget[OF assms(1)], simplified])
  also have "... = \<lbrace>\<Delta>\<rbrace>"
    apply (rule HSem_add_fresh[where \<rho> = "f\<emptyset>", simplified])
    using fresh by (simp add: fresh_Pair)
  finally show "\<lbrace>\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>\<rbrace>".

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e) # \<Gamma>\<rbrace>\<^esub>"
    apply (rule ESem_add_fresh[where \<rho> = "f\<emptyset>", symmetric, simplified])
    using fresh by (simp add: fresh_Pair)
  also have "... = \<lbrace>(x, e) # \<Gamma>\<rbrace> f! x"
    by (simp add: the_lookup_HSem_heap)
  also have "... = \<lbrace>(x, z) # \<Delta>\<rbrace> f! x" by (simp add: fmap_less_eqD[OF le, simplified])
  also have "... = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<^esub>" by (simp add: the_lookup_HSem_heap)
  also have "... =  \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>"
    apply (rule ESem_add_fresh[where \<rho> = "f\<emptyset>", simplified])
    using fresh by (simp add: fresh_Pair)
  finally show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>".
qed
end
