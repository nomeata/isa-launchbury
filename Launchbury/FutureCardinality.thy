theory FutureCardinality
imports CallFutures CardinalityAnalysis CallFutureCardinality
begin

locale FutureAnalysis =
 fixes Fexp :: "exp \<Rightarrow> Arity \<rightarrow> future set"
begin

fun FBinds :: "heap \<Rightarrow> AEnv \<rightarrow> (var \<Rightarrow> future set)"
  where "FBinds [] = (\<Lambda> ae. \<bottom>)"
      | "FBinds ((x,e)#\<Gamma>) = (\<Lambda> ae. (\<lambda> x'. (if x' = x then fup\<cdot>(Fexp e)\<cdot>(ae x) else (FBinds \<Gamma>\<cdot>ae) x)))"

lemma FBinds_Nil_simp[simp]: "FBinds []\<cdot>ae = \<bottom>" by simp

lemma FBinds_Cons[simp]:
  "FBinds ((x,e)#\<Gamma>)\<cdot>ae = (\<lambda> x'. (if x' = x then fup\<cdot>(Fexp e)\<cdot>(ae x) else (FBinds \<Gamma>\<cdot>ae) x))" by simp

lemmas FBinds.simps[simp del]

lemma FBinds_cong:
  assumes "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
  shows "FBinds \<Gamma>\<cdot>ae = FBinds \<Gamma>\<cdot>ae'"
using env_restr_eqD[OF assms]
by (induction \<Gamma> rule: FBinds.induct) (auto split: if_splits)

fun unstack :: "stack \<Rightarrow> exp \<Rightarrow> exp" where
  "unstack [] e = e"
| "unstack (Upd x # S) e = unstack S e"
| "unstack (Arg x # S) e = unstack S (App e x)"
| "unstack (Dummy x # S) e = unstack S e"

fun Fstack :: "stack \<Rightarrow> future set"
  where "Fstack [] = \<bottom>"
  | "Fstack (Upd x # S) = Fstack S"
  | "Fstack (Arg x # S) = may_call x (Fstack S)"
  | "Fstack (Dummy x # S) = Fstack S"

fun prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> var \<Rightarrow> two"
   where "prognosis ae a (\<Gamma>, e, S) = pathsCard (paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp e\<cdot>a) (Fstack S)))"
end

locale FutureAnalysisCorrect = FutureAnalysis +
  assumes Fexp_App: "Fexp (App e x)\<cdot>a = may_call x ((Fexp e)\<cdot>(inc\<cdot>a))"
  assumes Fexp_Lam: "without y ` (Fexp e \<cdot>(pred\<cdot>n)) = Fexp (Lam [y]. e) \<cdot> n"
  assumes Fexp_subst: "Fexp (e[y::=x])\<cdot>a = may_call x (without y ` ((Fexp e)\<cdot>a))"
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
      hence "\<exists> f \<in> Fstack S. f x > 1"
        by(induction S rule: Fstack.induct)(auto simp add: may_call_multiple_calls)
      hence "\<exists> f \<in> future_add (Fexp e\<cdot>a) (Fstack S). f x > 1"
        using future_add_subset2 by auto
      hence "[x,x] \<in> paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp e\<cdot>a) (Fstack S))" 
        apply -
        apply (erule bexE)
        apply (rule paths_intros)
        apply assumption
        apply (simp add: possible_def)
        apply (rule paths_intros)
        apply (rule set_mp[OF future_add_subset1])
        apply simp
        apply (simp add: possible_def after_def)
        apply rule
        done
      hence "pathCard [x,x] x \<sqsubseteq> pathsCard (paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp e\<cdot>a) (Fstack S))) x"
        by (metis fun_belowD paths_Card_above)
      also have "pathCard [x,x] x = many" by (auto simp add: pathCard_def)
      finally
      show "prognosis ae a (\<Gamma>, e, S) x = many"
        by (auto intro: below_antisym)
    qed
  next
    fix ae a \<Gamma> e x S
    have "future_add (Fexp e\<cdot>(inc\<cdot>a)) (may_call x (Fstack S)) = future_add (may_call x (Fexp e\<cdot>(inc\<cdot>a))) (Fstack S)"
      by (rule future_add_may_call_twist)
    hence "(future_add (Fexp e\<cdot>(inc\<cdot>a)) (may_call x (Fstack S))) = future_add (Fexp (App e x)\<cdot>a) (Fstack S)"
      by (simp add: Fexp_App)
    thus "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)"
      by simp
  next
    fix ae a \<Gamma> e y x S
    have "Fexp e[y::=x]\<cdot>(pred\<cdot>a) = may_call x (Fexp (Lam [y]. e)\<cdot>a)" 
      by (simp add: Fexp_Lam Fexp_subst)
    hence "future_add (Fexp e[y::=x]\<cdot>(pred\<cdot>a)) (Fstack S) = future_add (Fexp (Lam [y]. e)\<cdot>a) (may_call x (Fstack S))"
      by (metis future_add_may_call_twist)
    thus "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, Lam [y]. e, Arg x # S)"
      by simp
  next
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"
    assume "a \<sqsubseteq> u"

    have "paths (FBinds (delete x \<Gamma>)\<cdot>ae) (future_add (Fexp e\<cdot>u) (Fstack S)) \<subseteq> {tl p |p. p \<in> paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp (Var x)\<cdot>a) (Fstack S)) \<and> hd p = x}"
    proof
      fix p 
      assume "p \<in> paths (FBinds (delete x \<Gamma>)\<cdot>ae) (future_add (Fexp e\<cdot>u) (Fstack S))"

      have "x# p \<in>paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp (Var x)\<cdot>a) (Fstack S))"
      proof
        
      qed
      thus "p \<in> {tl p |p. p \<in> paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp (Var x)\<cdot>a) (Fstack S)) \<and> hd p = x}" by force
    qed
    hence "pathsCard (paths (FBinds (delete x \<Gamma>)\<cdot>ae) (future_add (Fexp e\<cdot>u) (Fstack S))) \<sqsubseteq> pathsCard {tl p |p. p \<in> paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp (Var x)\<cdot>a) (Fstack S)) \<and> hd p = x}"
      by (rule pathsCard_mono)
    hence "pathsCard (paths (FBinds (delete x \<Gamma>)\<cdot>ae) (future_add (Fexp e\<cdot>u) (Fstack S))) \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (FBinds \<Gamma>\<cdot>ae) (future_add (Fexp (Var x)\<cdot>a) (Fstack S))))"
      by (rule below_trans[OF _ record_call_pathsCard])
    thus "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x\<cdot>(prognosis ae a (\<Gamma>, Var x, S))" by simp
  oops

end



end
  
