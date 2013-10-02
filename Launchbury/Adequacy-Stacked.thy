theory "Adequacy-Stacked"
imports "Resourced-Denotational-Props" "LaunchburyCombinedTaggedMap"
begin

lemma fdom_fmap_of[simp]: "fdom (fmap_of m) = heapVars m"
  by (transfer, metis dom_map_of_conv_heapVars)

lemma heapVars_list_of[simp]:
  "heapVars (list_of m) = fdom m"
  unfolding list_of_def
  by (rule someI2_ex[OF list_of_exists]) auto

theorem adequacy:
  assumes "(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "\<exists> \<Delta>. fmap_of \<Gamma> \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x#S\<^esub> \<Delta>"
using assms
proof(induction n arbitrary: \<Gamma> x S)
  case 0
  hence False by auto
  thus ?case..
next
  case (Suc n)
  def \<Gamma>' \<equiv> "fmap_delete x (fmap_of \<Gamma>)"
  have "x \<notin> fdom \<Gamma>'" unfolding \<Gamma>'_def by simp

  from Suc.prems
  have "x \<in> heapVars \<Gamma>" by (auto intro: ccontr)
  then obtain e where e: "map_of \<Gamma> x = Some e" by (metis domD dom_map_of_conv_heapVars)
  hence \<Gamma>': "fmap_of \<Gamma> = \<Gamma>'(x f\<mapsto> e)" (is "?\<Gamma>' = _")
    apply (subst \<Gamma>'_def)
    apply (subst fmap_delete_fmap_upd2)
    apply (subst fmap_upd_noop)
    apply (auto simp add: `x \<in> heapVars \<Gamma>`)
    done

  from e have "\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x = \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>" using `x \<in> heapVars \<Gamma>` by auto
  with Suc.prems
  have prem: "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>" by simp

  show ?case
  proof(cases e rule:exp_assn.strong_exhaust(1)[where c = "(\<Gamma>,x,S)", case_names Var App Let Lam])
  case (Lam v e')
    have "fmap_of \<Gamma> \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x#S\<^esub> fmap_of \<Gamma>" 
      using e Lam `x \<in> heapVars \<Gamma>` by (auto intro: reds_LambdaI)
    thus ?thesis..
  next
  case (Var v)
    with prem
    have "(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> v)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by simp
    from Suc.IH[OF this]
    obtain \<Delta> where "fmap_of \<Gamma> \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>v # x # S\<^esub> \<Delta>"..
    hence "fmap_of \<Gamma> \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S\<^esub> fmap_copy \<Delta> v x" using `x \<notin> fdom \<Gamma>'` 
      by (auto intro:VariableNoBH simp add: \<Gamma>' Var)
    thus ?thesis..
  next
  case (App e' y)
    obtain n' :: var where "atom n' \<sharp> (\<Gamma>', x, e', y, S)" by (rule obtain_fresh)

    from App prem
    have not_bot1: "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
      by (simp add: Rep_cfun_inverse)

    have eq1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>(n', e') # \<Gamma>\<rbrace>\<^esub>"
      (* n' is fresh, hence irrelevant here *)
      sorry
    
    with not_bot1
    have not_bot2: "(\<N>\<lbrace>(n', e')#\<Gamma> \<rbrace> f!\<^sub>\<bottom> n')\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    from Suc.IH[OF this]
    obtain \<Delta>' where lhs': "(fmap_of \<Gamma>)(n' f\<mapsto> e') \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>n' # x # S\<^esub> \<Delta>'"
      by (auto)
    obtain \<Delta> where lhs: "\<Gamma>'(x f\<mapsto> App (Var n') y)(n' f\<mapsto> e') \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>n' # x # S\<^esub> \<Delta>"
      (* Changing the value of something on the stack, should be irrelvant, but may change \<Delta>. *)
      sorry

    obtain z e'' where n': "lookup \<Delta> n' = Some (Lam [z]. e'')" and "atom z \<sharp> (\<Gamma>', x, e', y, S, \<Delta>)" 
      by (rule result_evaluated_fresh[OF lhs])
    hence [simp]: "z \<notin> fdom \<Delta>" by (simp add: fresh_Pair sharp_Env)

    have added: "\<And> v. \<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> v \<sqsubseteq> \<N>\<lbrace>(n', e')#\<Gamma>\<rbrace> f!\<^sub>\<bottom> v " sorry

    from lhs'
    have correct: "\<And> v. \<N>\<lbrace>(n', e')#\<Gamma>\<rbrace> f!\<^sub>\<bottom> v \<sqsubseteq> \<N>\<lbrace>list_of \<Delta>\<rbrace>  f!\<^sub>\<bottom> v" sorry


    have "(\<N>\<lbrace>(n', e') # \<Gamma>\<rbrace> f!\<^sub>\<bottom> n')\<cdot>C\<^bsup>n\<^esup> \<sqsubseteq> (\<N>\<lbrace>list_of \<Delta>\<rbrace> f!\<^sub>\<bottom> n')\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_fun monofun_cfun correct)
    hence not_bot3: "(\<N>\<lbrakk>Lam [z]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>list_of \<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" using n' not_bot2 by auto

    have "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y))\<cdot>C\<^bsup>n\<^esup> 
        = ((\<N>\<lbrace>(n', e')#\<Gamma> \<rbrace> f!\<^sub>\<bottom> n')\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y))\<cdot>C\<^bsup>n\<^esup>"
      using eq1 by simp
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrace>list_of \<Delta>\<rbrace> f!\<^sub>\<bottom> n')\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct)
    also have "\<dots> = ((\<N>\<lbrakk>Lam [z]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>list_of \<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y))\<cdot>C\<^bsup>n\<^esup>" using n' by simp
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>list_of \<Delta>\<rbrace>)(z f\<mapsto> (C_case\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> y)))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using not_bot3 by (simp add: sharp_Env del: CESem.simps)
    also have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>list_of \<Delta>\<rbrace>)(z f\<mapsto> (C_case\<cdot>(\<N>\<lbrace>list_of \<Delta>\<rbrace> f!\<^sub>\<bottom> y)))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_fun monofun_cfun cont2monofunE[OF ESem_cont] fmap_upd_mono below_refl below_trans[OF added correct])
    also have "\<dots> = (\<N>\<lbrakk>e''[z::=y]\<rbrakk>\<^bsub>(\<N>\<lbrace>(x, e''[z::=y])#(list_of \<Delta>)\<rbrace>)\<^esub>)\<cdot>C\<^bsup>n\<^esup>" sorry
    also have "\<dots> = (\<N>\<lbrace>(x, e''[z::=y])#(list_of \<Delta>)\<rbrace> f!\<^sub>\<bottom> x)\<cdot>C\<^bsup>n\<^esup>" by auto
    finally
    have "\<dots> \<noteq> \<bottom>" using not_bot1 by auto
    from Suc.IH[OF this]
    obtain \<Theta> where "fmap_of ((x, e''[z::=y]) # list_of \<Delta>) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S\<^esub> \<Theta>"..
    hence rhs: "\<Delta>(x f\<mapsto> e''[z::=y]) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S\<^esub> \<Theta>" by simp

    from reds_ApplicationI[OF `atom n' \<sharp> _` `atom z \<sharp> _`  `x \<notin> fdom \<Gamma>'` n' lhs rhs, folded App, folded \<Gamma>']
    show ?thesis..
  next
  case (Let as e')
    from Let(1) have "set (bn as) \<sharp>* (\<Gamma>', x, S)" sorry

    have "distinctVars (asToHeap as)" sorry

    from Let prem
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (simp add: Rep_cfun_inverse fresh_star_Pair)
    also have "\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>" sorry
    also have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> = (\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
    sorry

    have "(\<N>\<lbrace>asToHeap as @ (x, e') # delete x \<Gamma>\<rbrace> f!\<^sub>\<bottom> x)\<cdot>C\<^bsup>n\<^esup>  \<noteq> \<bottom>" sorry
    from Suc.IH[OF this]
    obtain \<Delta> where "\<Gamma>'(x f\<mapsto> e') f++ fmap_of (asToHeap as) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S\<^esub> \<Delta>" using \<Gamma>'_def by auto
    from reds.Let[OF `set (bn as) \<sharp>* (\<Gamma>', x, S)` `distinctVars (asToHeap as)` `x \<notin> fdom \<Gamma>'` this, folded Let(2), folded \<Gamma>']
    show ?thesis..
  qed
qed

end
