theory ResourcedDenotational
imports CValue "Abstract-Denotational-Props"
begin

type_synonym CEnv = "var f\<rightharpoonup> CValue"

interpretation semantic_domain
  "\<Lambda> f . \<Lambda> r. CFn\<cdot>(\<Lambda> v. C_restr \<cdot> r \<cdot> (f\<cdot> (C_restr \<cdot> r \<cdot> v)))"
  "\<Lambda> x y. (\<Lambda> r. (x\<cdot>r \<down>CFn C_restr\<cdot>r\<cdot>y)\<cdot>r)"
  "\<Lambda> x. (\<Lambda> (C\<cdot>r). x \<cdot> r)".

abbreviation ESem_syn'' ("\<N>\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation HSem_syn' ("\<N>\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation HSem_fempty  ("\<N>\<lbrace>_\<rbrace>"  [60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace> \<equiv> \<N>\<lbrace>\<Gamma>\<rbrace>\<bottom>"

(* The same, but with some beta_cfun's and eta_cfuns resolved.*)
lemma CESem_simps:
  "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). (CFn\<cdot>(\<Lambda> v. C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(x := C_restr\<cdot>r\<cdot>v)\<^esub>))))"
  "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn C_restr\<cdot>r\<cdot>(\<rho> x))\<cdot>r)"
  "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      = (\<Lambda> (C\<cdot>r). (\<rho>  x) \<cdot> r)"
  "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>) \<cdot> r)"
  by simp_all

lemma CESem_bot[simp]:"(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>\<bottom> = \<bottom>"
  by (nominal_induct e arbitrary: \<sigma> rule: exp_assn.strong_induct(1)) auto

lemma CHSem_bot[simp]:"((\<N>\<lbrace> \<Gamma> \<rbrace>) x)\<cdot>\<bottom> = \<bottom>"
  by (cases "x \<in> heapVars \<Gamma>") (auto simp add: lookup_HSem_heap lookup_HSem_other)

end

