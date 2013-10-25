theory ResourcedDenotational
imports CValue "Abstract-Denotational-Props"
begin

type_synonym CEnv = "var f\<rightharpoonup> CValue"

interpretation cont_semantic_domain
  "\<lambda> f . \<Lambda> r. CFn\<cdot>(\<Lambda> v. C_restr \<cdot> r \<cdot> (f\<cdot> (C_restr \<cdot> r \<cdot> v)))"
  "\<lambda>x y. (\<Lambda> r. (x\<cdot>r \<down>CFn C_restr\<cdot>r\<cdot>y)\<cdot>r)"
  "\<lambda> x. C_case \<cdot> x"
  by unfold_locales simp_all

abbreviation CESem ("\<N>\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> AESem e \<rho>"

(* The same, but with some beta_cfun's and eta_cfuns resolved.*)
lemma CESem_simps:
  "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). (CFn\<cdot>(\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(x f\<mapsto> C_restr\<cdot>r\<cdot>v)\<^esub>))))"
  "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    =  (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn C_restr\<cdot>r\<cdot>(\<rho> f!\<^sub>\<bottom> x))\<cdot>r)"
  "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      = (\<Lambda> (C \<cdot> r). (\<rho> f!\<^sub>\<bottom> x) \<cdot> r)"
  "set (bn as) \<sharp>* \<rho> \<Longrightarrow>
  \<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem CESem (asToHeap as) \<rho>\<^esub>) \<cdot> r)"
  by (simp_all add: eta_cfun)


(* Re-Do the abbreviation from inside the the locale, as abbreviations are not exported *)
abbreviation CHSem_cond''
  where "CHSem_cond'' h \<rho> \<equiv>
      fix_join_cond (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) 
                        (\<lambda> \<rho>' . heapToEnv h (\<lambda>e. CESem e \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"

abbreviation CHSem_syn ("\<N>\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"
abbreviation CHSem_fempty  ("\<N>\<lbrace>_\<rbrace>"  [60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace> \<equiv> \<N>\<lbrace>\<Gamma>\<rbrace>fempty"


lemma CESem_bot[simp]:"(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>\<bottom> = \<bottom>"
  by (nominal_induct e avoiding: \<sigma> rule: exp_assn.strong_induct(1)) auto

lemma CHSem_bot[simp]:"(\<N>\<lbrace> \<Gamma> \<rbrace> f!\<^sub>\<bottom> x)\<cdot> \<bottom> = \<bottom>"
  by (cases "x \<in> heapVars \<Gamma>") auto

end

