theory ResourcedDenotational
imports "Denotational-Common" "Value-Meet" "HSem"
begin

domain C = C (lazy "C")

instantiation C :: pure_cpo
begin
  definition "p \<bullet> (c::C) = c"
instance
  apply default
  apply (auto simp add: permute_C_def)
  done
end

instance C :: Finite_Meet_cpo sorry
instance C :: Finite_Meet_bifinite_cpo by default


domain CValue' = CFn (lazy "(C \<rightarrow> CValue') \<rightarrow> (C \<rightarrow> CValue')")
type_synonym CValue = "C \<rightarrow> CValue'"

fixrec CFn_project :: "CValue' \<rightarrow> CValue \<rightarrow> CValue"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

instantiation CValue' :: pure_cpo
begin
  definition "p \<bullet> (v::CValue') = v"
instance
  apply default
  apply (auto simp add: permute_CValue'_def)
  done
end

instance cfun :: (Finite_Meet_cpo,Finite_Meet_cpo)Nonempty_Meet_cpo
sorry
instance cfun :: (Finite_Meet_bifinite_cpo,Finite_Meet_bifinite_cpo)Finite_Meet_bifinite_cpo sorry

instance CValue' :: Finite_Meet_cpo sorry
instance CValue' :: Finite_Meet_bifinite_cpo by default



type_synonym CEnv = "var f\<rightharpoonup> CValue"

nominal_primrec
  CESem :: "exp \<Rightarrow> CEnv \<Rightarrow> CValue" ("\<N>\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
where
 "atom x \<sharp> \<rho> \<Longrightarrow>
  \<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v r. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>) \<cdot> r))"
| "\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>    = (\<Lambda> (C \<cdot> r).  ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) \<cdot> r \<down>CFn \<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>) \<cdot> r)"
| "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>      = (\<Lambda> (C \<cdot> r). (\<rho> f! x) \<cdot> r)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>
  \<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem CESem (asToHeap as) \<rho>\<^esub>) \<cdot> r)"

oops


end

