theory ResourcedDenotational
imports "Denotational-Common" CValue "HSem"
begin


type_synonym CEnv = "var f\<rightharpoonup> CValue"

nominal_primrec
  CESem :: "exp \<Rightarrow> CEnv \<Rightarrow> CValue" ("\<N>\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
 "atom x \<sharp> \<rho> \<Longrightarrow>
  \<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v r. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>) \<cdot> r))"
| "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    = (\<Lambda> (C \<cdot> r).  ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) \<cdot> r \<down>CFn \<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>) \<cdot> r)"
| "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      = (\<Lambda> (C \<cdot> r). (\<rho> f!\<^sub>\<bottom> x) \<cdot> r)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>
  \<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem CESem (asToHeap as) \<rho>\<^esub>) \<cdot> r)"
sorry

lemma  True and [simp]:"(a, b) \<in> set (asToHeap as) \<Longrightarrow> size b < Suc (size as + size body)"
  by(induct and as rule:exp_assn.inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)

termination (eqvt) by lexicographic_order

interpretation has_ESem CESem.

subsubsection {* Equivariance of the semantics *}

lemma permute_ESem: "\<pi> \<bullet> CESem = CESem"
  by (perm_simp, rule)

lemmas HSem_eqvt' = HSem_eqvt[of _ CESem, unfolded permute_ESem]

lemmas HSem_fresh[simp] = eqvt_fresh_cong2[of HSem, OF HSem_eqvt']
 and   HSem_fresh_star[simp] = eqvt_fresh_star_cong2[of HSem, OF HSem_eqvt']
 and   asToHeap_fresh[simp] = eqvt_fresh_cong1[of asToHeap, OF asToHeap.eqvt]
 and   fresh_fmap_upd[simp] = eqvt_fresh_cong3[of fmap_upd, OF fmap_upd_eqvt]

(* Re-Do the abbreviation from inside the the locale, as abbreviations are not exported *)
abbreviation CHSem_cond''
  where "CHSem_cond'' h \<rho> \<equiv>
      fix_join_cond (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) 
                        (\<lambda> \<rho>' . heapToEnv h (\<lambda>e. CESem e \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"



end

