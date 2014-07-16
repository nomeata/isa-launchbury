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
shows "Alog c  f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp e \<cdot> n)  f|` (- (domA \<Delta> - domA \<Gamma>))"
using assms
proof(induction rule: LaunchburyLog.reds.induct)
case (Lambda \<Gamma> x e n L)
  show ?case
    by (metis Alog.simps(1) minimal env_restr_mono)
next
  case (Application y \<Gamma> e x L \<Delta> \<Theta> z c\<^sub>1 c\<^sub>2 n e')


  have subset1: " (- (domA \<Theta> - domA \<Gamma>)) \<subseteq> (- (domA \<Theta> - domA \<Delta>))"
  and subset2: "(- (domA \<Theta> - domA \<Gamma>)) \<subseteq> (- (domA \<Delta> - domA \<Gamma>))"
  using reds_doesnt_forget[OF  Application(2)]  reds_doesnt_forget[OF Application(3)] by auto
  let "?S" = " (- (domA \<Theta> - domA \<Gamma>))"

  
  {
    note env_restr_below_subset[OF subset2 Application.IH(1)]
    also have "Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n))  \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)"
      unfolding Aexp_App by (intro monofun_cfun_arg join_above1)
    finally
    have "Alog c\<^sub>1 f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n) f|` ?S" by this simp_all
  }
  moreover
  {
    note env_restr_below_subset[OF subset1 Application.IH(2)]
    also have "Afix \<Delta>\<cdot>(Aexp (e'[y::=x])\<cdot>n)  f|` ?S \<sqsubseteq> Afix \<Delta> \<cdot> (Aexp (App (Lam [y]. e') x)\<cdot>n)  f|` ?S"
      by (intro monofun_cfun Aexp_subst_App_Lam below_refl env_restr_mono)
    also have "\<dots> = Afix \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0))  f|` ?S"
      unfolding Aexp_App..
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0))  f|` ?S"
      by (rule env_restr_below_subset[OF subset2  reds_improves_arity''[OF remove_log[OF Application(2)]]]) auto
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n) f|` ?S"
      unfolding Aexp_App by (intro monofun_cfun below_refl)
    finally
    have "Alog c\<^sub>2 f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n)  f|` ?S" by this simp_all
  }
  ultimately
  show ?case by (simp del: fun_meet_simp add: env_restr_join)
next
case (Variable \<Gamma> x e n L \<Delta> z c)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])


  let "?S" = "(- (domA ((x, z) # \<Delta>) - domA \<Gamma>))"

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF remove_log[OF Variable(2)], where x = x]) simp_all
  hence subset: "?S \<subseteq>  (- (domA \<Delta> - domA (delete x \<Gamma>))) " by auto

  {
    have "AE_singleton x\<cdot>(up\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n)"
      by (rule below_trans[OF Aexp_Var_singleton Afix_above_arg])
    hence "AE_singleton x\<cdot>(up\<cdot>n) f|` ?S  \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n) f|` ?S " by (rule env_restr_mono)
  }
  moreover
  {
    note env_restr_below_subset[OF subset Variable.IH]
    also have "Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix ((x,e)#delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>(up\<cdot>n))" using Afix_e_to_heap'.
    also have "\<dots> \<sqsubseteq> Afix ((x,e)#delete x \<Gamma>)\<cdot>(Aexp (Var x)\<cdot>n)" by (intro monofun_cfun_arg Aexp_Var_singleton)
    also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n)" unfolding Afix_reorder[OF reorder]..
    finally
    have "Alog c f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>n) f|` ?S" by this simp_all
  }
  ultimately
  show ?case by (simp del: fun_meet_simp add: env_restr_join env_restr_mono)
 
next
case (Let as \<Gamma> L body n \<Delta> z c)
  hence *: "atom ` domA as \<sharp>* \<Gamma>" by (simp add: fresh_star_Pair) 

  let ?S = "(- (domA \<Delta> - domA \<Gamma>))"
  have subset: "?S \<subseteq>  (- (domA \<Delta> - domA (as @ \<Gamma>)))" by auto

  from `atom \` domA as \<sharp>* \<Gamma>` have "domA as \<inter> domA \<Gamma> = {}" by (metis fresh_distinct)
  moreover from reds_doesnt_forget[OF Let(2)] have "domA as \<subseteq> domA \<Delta>" by auto
  ultimately have ***: "((- domA \<Delta> \<union> domA \<Gamma>) \<inter> - domA as) = (- domA \<Delta> \<union> domA \<Gamma>)" by auto

  have "Alog c f|` ?S \<sqsubseteq> Afix (as @ \<Gamma>)\<cdot>(Aexp body\<cdot>n) f|` ?S " using env_restr_below_subset[OF subset Let.IH].
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp body\<cdot>n))  f|` ?S" by (rule arg_cong[OF Afix_append_fresh[OF *]])
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp body\<cdot>n)) f|` (- (domA as)) f|` ?S" by (simp add: ***)
  also have "\<dots> = Afix \<Gamma>\<cdot>((Afix as\<cdot>(Aexp body\<cdot>n)) f|` (- (domA as))) f|` (- (domA as)) f|` ?S" by (rule arg_cong[OF Afix_restr_fresh[OF *]])
  also have "\<dots> = Afix \<Gamma>\<cdot>((Afix as\<cdot>(Aexp body\<cdot>n)) f|` (- (domA as))) f|` ?S" by (simp add: ***)
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (Terms.Let as body)\<cdot>n) f|` ?S" by (intro monofun_cfun_arg join_mono env_restr_mono below_refl Aexp_Let)
  finally show ?case by this simp_all
qed

end
end
