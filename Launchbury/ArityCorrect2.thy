theory ArityCorrect2
imports ArityCorrect LaunchburyAddLog
begin

context CorrectArityAnalysis
begin


fun Alog :: "CallLog \<Rightarrow> AEnv"
 where "Alog [] = \<bottom>"
    |  "Alog ((x,n)#c) = (AE_singleton x \<cdot> (up \<cdot> n) \<squnion> Alog c)"

lemma Alog_append[simp]: "Alog (c\<^sub>1 @ c\<^sub>2) = Alog c\<^sub>1 \<squnion> Alog c\<^sub>2"
  by (induct c\<^sub>1 rule: Alog.induct) auto

lemma 
assumes "\<Gamma> : e \<Down>\<^bsub>n,L\<^esub> \<Delta> : v c"
shows "Alog c \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp e \<cdot> n)"
using assms
proof(induction rule: LaunchburyLog.reds.induct)
case (Lambda \<Gamma> x e n L)
  show ?case
    by (metis Alog.simps(1) minimal)
next
  case (Application y \<Gamma> e x L \<Delta> \<Theta> z c\<^sub>1 c\<^sub>2 n e')
  
  {
    note Application.IH(1)
    also have "Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n)) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)"
      unfolding Aexp_App by (intro monofun_cfun_arg join_above1)
    finally
    have "Alog c\<^sub>1 \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)" by this simp_all
  }
  moreover
  {
    note Application.IH(2)
    also have "Afix \<Delta>\<cdot>(Aexp (e'[y::=x])\<cdot>n) \<sqsubseteq> Afix \<Delta> \<cdot> (Aexp (App (Lam [y]. e') x)\<cdot>n)"
      by (intro monofun_cfun Aexp_subst_App_Lam below_refl)
    also have "\<dots> = Afix \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0))"
      unfolding Aexp_App..
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0))"
      by (rule reds_improves_arity''[OF remove_log[OF Application(2)]]) auto
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)"
      unfolding Aexp_App by (intro monofun_cfun below_refl)
    finally
    have "Alog c\<^sub>2 \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)" by this simp_all
  }
  ultimately
  show ?case by (simp del: fun_meet_simp)
next
case (Variable \<Gamma> x e n L \<Delta> z c)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])

  {
    have "AE_singleton x\<cdot>(up\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n)"
      unfolding Aexp_Var by (rule Afix_above_arg)
  }
  moreover
  {
    have "Alog c \<sqsubseteq> Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n)" using Variable.IH.
    also have "\<dots> \<sqsubseteq> Afix ((x,e)#delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>(up\<cdot>n))" using Afix_e_to_heap'.
    also have "\<dots> \<sqsubseteq> Afix ((x,e)#delete x \<Gamma>)\<cdot>(Aexp (Var x)\<cdot>n)" unfolding Aexp_Var..
    also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n)" unfolding Afix_reorder[OF reorder]..
    finally
    have "Alog c \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n)" by this simp_all
  }
  ultimately
  show ?case by (simp del: fun_meet_simp)
next
case (Let as \<Gamma> L body n \<Delta> z c)
  hence *: "atom ` domA as \<sharp>* \<Gamma>" by (metis fresh_star_Pair) 

  have "Alog c \<sqsubseteq> Afix (as @ \<Gamma>)\<cdot>(Aexp body\<cdot>n)" using Let.IH.
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp body\<cdot>n))" unfolding Afix_append_fresh[OF *]..
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Terms.Let as body)\<cdot>n)" by (intro monofun_cfun below_refl Aexp_Let)
  finally show ?case by this simp_all
qed

end
end
