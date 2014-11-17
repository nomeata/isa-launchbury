theory FTreeCardinality
imports CardinalityAnalysis "FTree-HOLCF" CallFutureCardinality
begin

locale FutureAnalysis =
 fixes Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
begin

fun FBinds :: "heap \<Rightarrow> AEnv \<rightarrow> (var \<Rightarrow> var ftree)"
  where "FBinds [] = (\<Lambda> ae. \<bottom>)"
      | "FBinds ((x,e)#\<Gamma>) = (\<Lambda> ae. (FBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(Fexp e)\<cdot>(ae x)))"

lemma FBinds_Nil_simp[simp]: "FBinds []\<cdot>ae = \<bottom>" by simp

lemma FBinds_Cons[simp]:
  "FBinds ((x,e)#\<Gamma>)\<cdot>ae = (FBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(Fexp e)\<cdot>(ae x))" by simp

lemmas FBinds.simps[simp del]

lemma FBinds_not_there: "x \<notin> domA \<Gamma> \<Longrightarrow> (FBinds \<Gamma>\<cdot>ae) x = \<bottom>"
  by (induction \<Gamma> rule: FBinds.induct) auto
  
lemma FBinds_cong:
  assumes "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
  shows "FBinds \<Gamma>\<cdot>ae = FBinds \<Gamma>\<cdot>ae'"
using env_restr_eqD[OF assms]
by (induction \<Gamma> rule: FBinds.induct) (auto split: if_splits)

lemma FBinds_lookup: "(FBinds \<Gamma>\<cdot>ae) x = (case map_of \<Gamma> x of Some e \<Rightarrow> fup\<cdot>(Fexp e)\<cdot>(ae x) | None \<Rightarrow> \<bottom>)"
  by (induction \<Gamma> rule: FBinds.induct) auto

lemma FBinds_delete_below: "FBinds (delete x \<Gamma>)\<cdot>ae \<sqsubseteq> FBinds \<Gamma>\<cdot>ae"
  by (auto intro: fun_belowI simp add: FBinds_lookup split:option.split)

fun unstack :: "stack \<Rightarrow> exp \<Rightarrow> exp" where
  "unstack [] e = e"
| "unstack (Upd x # S) e = unstack S e"
| "unstack (Arg x # S) e = unstack S (App e x)"
| "unstack (Dummy x # S) e = unstack S e"

fun Fstack :: "stack \<Rightarrow> var ftree"
  where "Fstack [] = \<bottom>"
  | "Fstack (Upd x # S) = Fstack S"
  | "Fstack (Arg x # S) = both (many_calls x) (Fstack S)"
  | "Fstack (Dummy x # S) = Fstack S"

fun prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> var \<Rightarrow> two"
   where "prognosis ae a (\<Gamma>, e, S) = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S))))"
end

lemma pathsCard_paths_nxt:  "pathsCard (paths (nxt f x)) \<sqsubseteq> record_call x\<cdot>(pathsCard (paths f))"
  apply transfer
  apply (rule pathsCard_below)
  apply auto
  apply (erule below_trans[OF _ monofun_cfun_arg[OF paths_Card_above], rotated]) back
  apply (auto intro: fun_belowI simp add: record_call_simp two_pred_two_add_once)
  done

lemma pathsCards_none: "pathsCard (paths t) x = none \<Longrightarrow> x \<notin> carrier t"
  by transfer (auto dest: pathCards_noneD)

locale FutureAnalysisCorrect = FutureAnalysis +
  assumes Fexp_App: "both (many_calls x) ((Fexp e)\<cdot>(inc\<cdot>a)) \<sqsubseteq> Fexp (App e x)\<cdot>a"
  assumes Fexp_Lam: "without y (Fexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Fexp (Lam [y]. e) \<cdot> n"
  assumes Fexp_subst: "Fexp (e[y::=x])\<cdot>a \<sqsubseteq> both (many_calls x) (without y ((Fexp e)\<cdot>a))"
  assumes Fexp_Var: "single v \<sqsubseteq> Fexp (Var v)\<cdot>a"
  assumes Fun_repeatable: "isLam e \<Longrightarrow> repeatable (Fexp e\<cdot>0)"
begin

  sublocale CardinalityPrognosisCorrect prognosis
  proof
    fix \<Gamma> :: heap and ae ae' :: AEnv and u e S
    assume "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
    from FBinds_cong[OF this]
    show "prognosis ae u (\<Gamma>, e, S) = prognosis ae' u (\<Gamma>, e, S)" by simp
  next
    fix ae a \<Gamma> e S
    show "const_on (prognosis ae a (\<Gamma>, e, S)) (ap S) many"
    proof
      fix x
      assume "x \<in> ap S"
      hence "[x,x] \<in> paths (Fstack S)"
        by (induction S rule: Fstack.induct)
           (auto 4 4 intro: set_mp[OF both_contains_arg1] set_mp[OF both_contains_arg2] paths_Cons_nxt)
      hence "[x,x] \<in> paths (both (Fexp e\<cdot>a) (Fstack S))"
        by (rule set_mp[OF both_contains_arg2])
      hence "[x,x] \<in> paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S)))" 
        by (rule set_mp[OF substitute_contains_arg])
      hence "pathCard [x,x] x \<sqsubseteq> pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S)))) x"
        by (metis fun_belowD paths_Card_above)
      also have "pathCard [x,x] x = many"  by (auto simp add: pathCard_def)
      finally
      show "prognosis ae a (\<Gamma>, e, S) x = many"
        by (auto intro: below_antisym)
    qed
  next
    fix ae a \<Gamma> e x S
    have "both (Fexp e\<cdot>(inc\<cdot>a)) (both (many_calls x) (Fstack S)) = both (both (many_calls x) ((Fexp e)\<cdot>(inc\<cdot>a))) (Fstack S)"
      by (metis both_assoc both_comm)
    thus "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1' Fexp_App)
  next
    fix ae a \<Gamma> e y x S
    have "Fexp e[y::=x]\<cdot>(pred\<cdot>a) \<sqsubseteq> both (many_calls x) (Fexp (Lam [y]. e)\<cdot>a)" 
      by (rule below_trans[OF Fexp_subst both_mono2'[OF Fexp_Lam]])
    moreover have "both (Fexp (Lam [y]. e)\<cdot>a) (both (many_calls x) (Fstack S)) = both (both (many_calls x) (Fexp (Lam [y]. e)\<cdot>a)) (Fstack S)"
      by (metis both_assoc both_comm)
    ultimately  
    show "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, Lam [y]. e, Arg x # S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1')
  next
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"

    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>u) (Fstack S)))) = pathsCard (paths (nxt (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>u) (Fstack S)))) x))"
      by simp
      also
    have "\<dots> \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>u) (Fstack S))))))"
      by (rule pathsCard_paths_nxt)
      also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fstack S) (Fexp e\<cdot>u))))))"
      by (metis both_comm)
      also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fstack S) ((FBinds \<Gamma>\<cdot>ae) x))))))"
      using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` by (simp add: FBinds_lookup)
      also
    have "and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fstack S) ((FBinds \<Gamma>\<cdot>ae) x))) = substitute (FBinds \<Gamma>\<cdot>ae) (and_then x (Fstack S))"
      by (rule substitute_and_then[symmetric])
      also
    have "and_then x (Fstack S) \<sqsubseteq> both (FTree.single x) (Fstack S)" by (rule and_then_both_single')
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF this]]]
      also
    have "FTree.single x \<sqsubseteq> Fexp (Var x)\<cdot>a" by (rule Fexp_Var)
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF both_mono1'[OF this]]]]
    finally
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>u) (Fstack S)))) \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp (Var x)\<cdot>a) (Fstack S)))))" 
      by this simp_all
    thus "prognosis ae u ( \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x\<cdot>(prognosis ae a (\<Gamma>, Var x, S))" by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and  x :: var and  S
    assume "isLam e"
    hence "repeatable (Fexp e\<cdot>0)" by (rule Fun_repeatable)

    assume [simp]: "x \<notin> domA \<Gamma>"

    have "fup\<cdot>(Fexp e)\<cdot>(ae x) \<sqsubseteq> Fexp e\<cdot>0" by (metis fup2 monofun_cfun_arg up_zero_top)
    hence "substitute ((FBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(Fexp e)\<cdot>(ae x))) (both (Fexp e\<cdot>0) (Fstack S)) \<sqsubseteq> substitute ((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0)) (both (Fexp e\<cdot>0) (Fstack S))"
      by (intro substitute_mono1' fun_upd_mono below_refl)
    also have "\<dots> = substitute (((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0))(x := empty)) (both (Fexp e\<cdot>0) (Fstack S))"
      using `repeatable (Fexp e\<cdot>0)` by (rule substitute_remove_anyways, simp)
    also have "((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0))(x := empty) = FBinds \<Gamma>\<cdot>ae"
      by (simp add: fun_upd_idem FBinds_not_there empty_is_bottom)
    finally
    show "prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)"
      by (simp, intro pathsCard_mono' paths_mono)
  next
    fix \<Gamma> \<Delta> :: heap and e :: exp and ae :: AEnv and u S
    assume "map_of \<Gamma> = map_of \<Delta>"
    hence "FBinds \<Gamma> = FBinds \<Delta>" by (auto intro!: cfun_eqI  simp add: FBinds_lookup)
    thus "prognosis ae u (\<Gamma>, e, S) = prognosis ae u (\<Delta>, e, S)"  by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and u S x
    show "prognosis ae u (delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono1' FBinds_delete_below)
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and u S x
    show "prognosis ae u (\<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)" by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and a S x
    assume "prognosis ae a (delete x \<Gamma>, e, S) x = none"
    hence "x \<notin> carrier (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S)))" 
      by (simp add: pathsCards_none)
    hence "substitute (FBinds \<Gamma>\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S)) = substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (both (Fexp e\<cdot>a) (Fstack S))"
      by (auto intro: substitute_cong[symmetric] simp add: FBinds_lookup delete_conv')
    thus "prognosis ae a (\<Gamma>, e, S) \<sqsubseteq> prognosis ae a (delete x \<Gamma>, e, S)"
      by simp
  qed
end



end
  
