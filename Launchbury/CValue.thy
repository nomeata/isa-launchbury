theory CValue
imports "Denotational-Common" C
begin

domain CValue' = CFn (lazy "(C \<rightarrow> CValue') \<rightarrow> (C \<rightarrow> CValue')")
type_synonym CValue = "C \<rightarrow> CValue'"

fixrec CFn_project :: "CValue' \<rightarrow> CValue \<rightarrow> CValue"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

lemma CFn_project_strict[simp]:
  "\<bottom> \<down>CFn v = \<bottom>"
  by (fixrec_simp) 

instantiation CValue' :: pure_cpo
begin
  definition "p \<bullet> (v::CValue') = v"
instance
  apply default
  apply (auto simp add: permute_CValue'_def)
  done
end

instance CValue' :: pcpo_pt by default


instantiation cfun :: (cpo,"{bifinite,cont_binary_meet}") Finite_Meet_cpo begin
  fixrec cfun_meet :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
    where "cfun_meet\<cdot>f\<cdot>g\<cdot>x = (f\<cdot>x) \<sqinter> (g\<cdot>x)"
  
  lemma[simp]: "cfun_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "cfun_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp)+

  instance
  apply default
  proof(intro exI conjI strip)
    fix x y
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> x" by (auto simp add: cfun_below_iff)
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> y" by (auto simp add: cfun_below_iff)
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> cfun_meet\<cdot>x\<cdot>y" by (auto simp add: cfun_below_iff meet_above_iff)
  qed
end

instance cfun :: (profinite,"{Finite_Meet_bifinite_cpo,cont_binary_meet}") Finite_Meet_bifinite_cpo by default

fixrec CValue'_meet :: "CValue' \<rightarrow> CValue' \<rightarrow> CValue'"
  where "CValue'_meet\<cdot>(CFn\<cdot>f)\<cdot>(CFn\<cdot>g) = CFn \<cdot>(\<Lambda> x r. CValue'_meet \<cdot> (f\<cdot>x\<cdot>r) \<cdot> (g\<cdot>x\<cdot>r))"
  
lemma[simp]: "CValue'_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "CValue'_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)  

lemma CValue'_meet_is_meet: "(z \<sqsubseteq> CValue'_meet\<cdot>x\<cdot>y) = (z \<sqsubseteq> x \<and> z \<sqsubseteq> y)"
proof (induct z rule:CValue'.take_induct)
  fix n
  show "(CValue'_take n\<cdot>z \<sqsubseteq> CValue'_meet\<cdot>x\<cdot>y) = (CValue'_take n\<cdot>z \<sqsubseteq> x \<and> CValue'_take n\<cdot>z \<sqsubseteq> y)"
  proof (induct n arbitrary: z x y rule:nat_induct)
    case 0 thus ?case by auto
    next
    case (Suc n z x y) thus ?case
      apply -
      apply (cases z, simp)
      apply (cases x, simp)
      apply (cases y, simp)
      apply (fastforce simp add: cfun_below_iff)
      done
  qed
qed auto

instance CValue' :: Finite_Meet_cpo
  apply default
  using CValue'_meet_is_meet
  apply blast
  done

instance CValue' :: cont_binary_meet
proof
  have [simp]:"\<And> x y. x \<sqinter> y = CValue'_meet\<cdot>x\<cdot>y"
    using CValue'_meet_is_meet
    by (blast intro: is_meetI)
  case goal1 thus ?case
    by (simp add: ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun)
qed

instance CValue' :: Finite_Meet_bifinite_cpo by default

end
