theory ArityAnalysisFixProps
imports ArityAnalysisFix ArityAnalysisSpec
begin

context EdomArityAnalysis
begin

lemma Afix_edom: "edom (Afix \<Gamma> \<cdot> ae) \<subseteq> fv \<Gamma> \<union> edom ae"
  unfolding Afix_eq
  by (rule fix_ind[where P = "\<lambda> ae' . edom ae' \<subseteq> fv \<Gamma> \<union> edom ae"] )
     (auto dest: set_mp[OF edom_AnalBinds])

lemma ABinds_lookup_fresh:
  "atom v \<sharp> \<Gamma> \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae) v = \<bottom>"
by (induct \<Gamma> rule: ABinds.induct) (auto simp add: fresh_Cons fresh_Pair fup_Aexp_lookup_fresh fresh_delete)

lemma Afix_lookup_fresh:
  assumes "atom v \<sharp> \<Gamma>"
  shows "(Afix \<Gamma>\<cdot>ae) v = ae v"
  apply (rule below_antisym)
  apply (subst Afix_eq)
  apply (rule fix_ind[where  P = "\<lambda> ae'. ae' v \<sqsubseteq> ae v"])
  apply (auto simp add: ABinds_lookup_fresh[OF assms] fun_belowD[OF Afix_above_arg])
  done

lemma Afix_comp2join_fresh:
  "atom ` (domA \<Delta>) \<sharp>* \<Gamma> \<Longrightarrow> ABinds \<Delta>\<cdot>(Afix \<Gamma>\<cdot>ae) = ABinds \<Delta>\<cdot>ae"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 show ?case by (simp add: Afix_above_arg del: fun_meet_simp)
next
  case (2 v e \<Delta>)
  from 2(2)
  have "atom v \<sharp> \<Gamma>" and  "atom ` domA (delete v \<Delta>) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from 2(1)[OF this(2)]
  show ?case by (simp del: fun_meet_simp add: Afix_lookup_fresh[OF `atom v \<sharp> \<Gamma>`])
qed

lemma Afix_append_fresh:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  shows "Afix (\<Delta> @ \<Gamma>)\<cdot>ae = Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
proof (rule below_antisym)
  show *: "Afix (\<Delta> @ \<Gamma>)\<cdot>ae \<sqsubseteq> Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
  apply (rule Afix_least_below)
  apply (simp add: Abinds_append_disjoint[OF fresh_distinct[OF assms]] Afix_comp2join_fresh[OF assms])
  apply (rule below_trans[OF join_mono[OF Abinds_Afix_below Abinds_Afix_below]])
  apply (simp_all add: Afix_above_arg  below_trans[OF Afix_above_arg Afix_above_arg])
  done
next
  show "Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
  proof (rule Afix_least_below)
    show "ABinds \<Gamma>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule below_trans[OF _ Abinds_Afix_below])
      apply (subst Abinds_append_disjoint[OF fresh_distinct[OF assms]])
      apply simp
      done
    have "ABinds \<Delta>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule below_trans[OF _ Abinds_Afix_below])
      apply (subst Abinds_append_disjoint[OF fresh_distinct[OF assms]])
      apply simp
      done
    thus "Afix \<Delta>\<cdot>ae \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule Afix_least_below)
      apply (rule Afix_above_arg)
      done
  qed
qed


lemma Afix_e_to_heap:
   "Afix (delete x \<Gamma>)\<cdot>(fup\<cdot>(Aexp e)\<cdot>n \<squnion> ae) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(esing x\<cdot>n \<squnion> ae)"
    apply (simp add: Afix_eq)
    apply (rule fix_least_below, simp)
    apply (intro join_below)
    apply (subst fix_eq, simp)
    apply (subst fix_eq, simp)

    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule monofun_cfun_arg)
    apply (subst fix_eq, simp)
      
    apply (subst fix_eq, simp) back apply (simp add: below_trans[OF _ join_above2])
    done

lemma Afix_e_to_heap':
   "Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(esing x\<cdot>(up\<cdot>n))"
using Afix_e_to_heap[where ae = \<bottom> and n = "up\<cdot>n"] by simp

end

context SubstArityAnalysis
begin

lemma Afix_restr_subst:
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>[x::h=y]\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae f|` S) f|` S"
  by (rule Afix_restr_subst'[OF Aexp_subst_restr[OF assms(1,2)] assms])
end


end
