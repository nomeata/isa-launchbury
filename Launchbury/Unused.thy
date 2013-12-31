theory Unused 
imports CValue  "HOLCF-Meet-Classes" "AList-Utils" Terms
begin

nominal_primrec isLam :: "exp \<Rightarrow> bool" where
  "isLam (Var x) = False" |
  "isLam (Lam [x]. e) = True" |
  "isLam (App e x) = False" |
  "isLam (Let as e) = False"
  unfolding isLam_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_assn.exhaust(1))
  apply auto
  done
termination (eqvt) by lexicographic_order


lemma change_Lam_Variable:
  assumes "atom y' \<sharp> e'" and "atom y' \<sharp> y"
  shows   "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')"
proof-
  from assms
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y]. e'"
    by -(rule flip_fresh_fresh, (simp add: fresh_Pair)+)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')"
    by simp
  ultimately
  show "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')" by (simp add: fresh_Pair)
qed

lemma isLam_subst[simp]: "isLam e[x::=y] = isLam e"
  by (nominal_induct e avoiding: x y rule:exp_assn.strong_induct(1))
     (auto simp add: fresh_star_Pair)


lemma the_map_of_snd:
  "x\<in> domA \<Gamma> \<Longrightarrow> the (map_of \<Gamma> x) \<in> snd ` set \<Gamma>"
  by (induct \<Gamma>, auto)

lemma delete_no_there:
  "x \<notin> domA \<Gamma> \<Longrightarrow> delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>, auto)


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


end
