theory FTreeCardinality
imports FTreeAnalysis CardinalityAnalysis CallFutureCardinality
begin

context FutureAnalysis
begin

fun unstack :: "stack \<Rightarrow> exp \<Rightarrow> exp" where
  "unstack [] e = e"
| "unstack (Upd x # S) e = unstack S e"
| "unstack (Arg x # S) e = unstack S (App e x)"
| "unstack (Dummy x # S) e = unstack S e"

fun Fstack :: "stack \<Rightarrow> var ftree"
  where "Fstack [] = \<bottom>"
  | "Fstack (Upd x # S) = Fstack S"
  | "Fstack (Arg x # S) = many_calls x \<otimes>\<otimes> Fstack S"
  | "Fstack (Dummy x # S) = Fstack S"

lemma carrier_Fstack[simp]: "carrier (Fstack S) = ap S"
  by (induction S rule: Fstack.induct) (auto simp add: empty_is_bottom[symmetric])

fun prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> var \<Rightarrow> two"
   where "prognosis ae a (\<Gamma>, e, S) = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)))"
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

lemma const_on_edom_disj: "const_on f S empty \<longleftrightarrow> edom f \<inter> S = {}"
  by (auto simp add: empty_is_bottom edom_def)

context FutureAnalysisCarrier
begin
  lemma carrier_FBinds: "carrier ((FBinds \<Gamma>\<cdot>ae) x) \<subseteq> fv \<Gamma>"
  apply (simp add: Fexp.AnalBinds_lookup)
  apply (auto split: option.split simp add: empty_is_bottom[symmetric] )
  apply (case_tac "ae x")
  apply (auto simp add: empty_is_bottom[symmetric] carrier_Fexp dest!: set_mp[OF Aexp_edom])
  by (metis (poly_guards_query) contra_subsetD domA_from_set map_of_fv_subset map_of_is_SomeD option.sel)
end




context FutureAnalysisCorrect
begin

  sublocale CardinalityPrognosisCorrect prognosis
  proof
    fix \<Gamma> :: heap and ae ae' :: AEnv and u e S
    assume "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
    from Fexp.AnalBinds_cong[OF this]
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
      hence "[x,x] \<in> paths (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)"
        by (rule set_mp[OF both_contains_arg2])
      hence "[x,x] \<in> paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S))" 
        by (rule set_mp[OF substitute_contains_arg])
      hence "pathCard [x,x] x \<sqsubseteq> pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S))) x"
        by (metis fun_belowD paths_Card_above)
      also have "pathCard [x,x] x = many"  by (auto simp add: pathCard_def)
      finally
      show "prognosis ae a (\<Gamma>, e, S) x = many"
        by (auto intro: below_antisym)
    qed
  next
    fix ae a \<Gamma> e x S
    have "Fexp e\<cdot>(inc\<cdot>a)  \<otimes>\<otimes> many_calls x \<otimes>\<otimes> Fstack S = many_calls x  \<otimes>\<otimes> (Fexp e)\<cdot>(inc\<cdot>a) \<otimes>\<otimes> Fstack S"
      by (metis both_assoc both_comm)
    thus "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1' Fexp_App)
  next
    fix ae a \<Gamma> e y x S
    have "Fexp e[y::=x]\<cdot>(pred\<cdot>a) \<sqsubseteq> many_calls x  \<otimes>\<otimes> Fexp (Lam [y]. e)\<cdot>a"
      by (rule below_trans[OF Fexp_subst both_mono2'[OF Fexp_Lam]])
    moreover have "Fexp (Lam [y]. e)\<cdot>a \<otimes>\<otimes> many_calls x \<otimes>\<otimes> Fstack S = many_calls x  \<otimes>\<otimes> Fexp (Lam [y]. e)\<cdot>a \<otimes>\<otimes> Fstack S"
      by (metis both_assoc both_comm)
    ultimately  
    show "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, Lam [y]. e, Arg x # S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1')
  next
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"

    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u \<otimes>\<otimes> Fstack S))) = pathsCard (paths (nxt (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S))) x))"
      by simp
    also
    have "\<dots> \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S)))))"
      by (rule pathsCard_paths_nxt)
    also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fstack S  \<otimes>\<otimes> Fexp e\<cdot>u)))))"
      by (metis both_comm)
    also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fstack S  \<otimes>\<otimes> (FBinds \<Gamma>\<cdot>ae) x)))))"
      using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` by (simp add: Fexp.AnalBinds_lookup)
    also
    assume "isLam e"
    hence "x \<notin> thunks \<Gamma>" using `map_of \<Gamma> x = Some e` by (metis thunksE)
    hence "FBinds \<Gamma>\<cdot>ae = f_nxt (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) x" by (auto simp add: f_nxt_def)
    hence "and_then x (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fstack S  \<otimes>\<otimes> (FBinds \<Gamma>\<cdot>ae) x)) = substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (and_then x (Fstack S))"
      by (simp add: substitute_and_then)
    also
    have "and_then x (Fstack S) \<sqsubseteq> FTree.single x \<otimes>\<otimes> Fstack S" by (rule and_then_both_single')
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF this]]]
    also
    have "FTree.single x \<sqsubseteq> Fexp (Var x)\<cdot>a" by (rule Fexp_Var)
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF both_mono1'[OF this]]]]
    finally
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S))) \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp (Var x)\<cdot>a  \<otimes>\<otimes> Fstack S))))" 
      by this simp_all
    thus "prognosis ae u (\<Gamma>, e, S) \<sqsubseteq> record_call x\<cdot>(prognosis ae a (\<Gamma>, Var x, S))" by simp
  next
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"
    assume "\<not> isLam e"
    hence "x \<in> thunks \<Gamma>" using `map_of \<Gamma> x = Some e` by (metis thunksI)
    hence [simp]: "f_nxt (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) x = FBinds (delete x \<Gamma>)\<cdot>ae" 
      by (auto simp add: f_nxt_def Fexp.AnalBinds_delete_to_fun_upd empty_is_bottom)

    have "pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks (delete x \<Gamma>)) (Fexp e\<cdot>u \<otimes>\<otimes> Fstack S)))
       =  pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u \<otimes>\<otimes> Fstack S)))"
       by (rule arg_cong[OF substitute_cong_T]) (auto simp add: empty_is_bottom)
    also have "\<dots>  = pathsCard (paths (nxt (and_then x (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S))) x))"
      by simp
    also
    have "\<dots> \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S)))))"
      by (rule pathsCard_paths_nxt)
    also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fstack S  \<otimes>\<otimes> Fexp e\<cdot>u)))))"
      by (metis both_comm)
    also
    have "\<dots> = record_call x\<cdot>(pathsCard (paths (and_then x (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fstack S  \<otimes>\<otimes> (FBinds \<Gamma>\<cdot>ae) x)))))"
      using `map_of \<Gamma> x = Some e` `ae x = up\<cdot>u` by (simp add: Fexp.AnalBinds_lookup)
    also
    have "and_then x (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Fstack S \<otimes>\<otimes> (FBinds \<Gamma>\<cdot>ae) x)) = substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (and_then x (Fstack S))"
      by (simp add: substitute_and_then)
    also
    have "and_then x (Fstack S) \<sqsubseteq> FTree.single x \<otimes>\<otimes> Fstack S" by (rule and_then_both_single')
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF this]]]
    also
    have "FTree.single x \<sqsubseteq> Fexp (Var x)\<cdot>a" by (rule Fexp_Var)
    note pathsCard_mono'[OF paths_mono[OF substitute_mono2'[OF both_mono1'[OF this]]]]
    finally
    have "pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks (delete x \<Gamma>)) (Fexp e\<cdot>u  \<otimes>\<otimes> Fstack S)))
       \<sqsubseteq> record_call x\<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp (Var x)\<cdot>a  \<otimes>\<otimes> Fstack S))))" 
      by this simp_all
    thus "prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x\<cdot>(prognosis ae a (\<Gamma>, Var x, S))" by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and  x :: var and  S
    assume "isLam e"
    hence "repeatable (Fexp e\<cdot>0)" by (rule Fun_repeatable)

    assume [simp]: "x \<notin> domA \<Gamma>"

    have [simp]: "thunks ((x, e) # \<Gamma>) = thunks \<Gamma>" 
      using `isLam e`
      by (auto simp add: thunks_Cons dest: set_mp[OF thunks_domA])

    have "fup\<cdot>(Fexp e)\<cdot>(ae x) \<sqsubseteq> Fexp e\<cdot>0" by (metis fup2 monofun_cfun_arg up_zero_top)
    hence "substitute ((FBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(Fexp e)\<cdot>(ae x))) (thunks \<Gamma>) (Fexp e\<cdot>0 \<otimes>\<otimes> Fstack S) \<sqsubseteq> substitute ((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0)) (thunks \<Gamma>) (Fexp e\<cdot>0 \<otimes>\<otimes> Fstack S)"
      by (intro substitute_mono1' fun_upd_mono below_refl)
    also have "\<dots> = substitute (((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0))(x := empty)) (thunks \<Gamma>) (Fexp e\<cdot>0 \<otimes>\<otimes> Fstack S)"
      using `repeatable (Fexp e\<cdot>0)` by (rule substitute_remove_anyways, simp)
    also have "((FBinds \<Gamma>\<cdot>ae)(x := Fexp e\<cdot>0))(x := empty) = FBinds \<Gamma>\<cdot>ae"
      by (simp add: fun_upd_idem Fexp.AnalBinds_not_there empty_is_bottom)
    finally
    show "prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)"
      by (simp, intro pathsCard_mono' paths_mono)
  next
    fix \<Gamma> \<Delta> :: heap and e :: exp and ae :: AEnv and u S
    assume "map_of \<Gamma> = map_of \<Delta>"
    hence "FBinds \<Gamma> = FBinds \<Delta>" and "thunks \<Gamma> = thunks \<Delta>" by (auto intro!: cfun_eqI  thunks_cong simp add: Fexp.AnalBinds_lookup)
    thus "prognosis ae u (\<Gamma>, e, S) = prognosis ae u (\<Delta>, e, S)"  by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and u S x

    show "prognosis ae u (delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, S)"
      by (simp add: substitute_T_delete empty_is_bottom)
         (intro pathsCard_mono' paths_mono substitute_mono1' Fexp.AnalBinds_delete_below)
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and u S x
    show "prognosis ae u (\<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)" by simp
  next
    fix ae a \<Gamma> e S x e'
    assume "prognosis ae a (\<Gamma>, e, S) x = none"
    hence "x \<notin> carrier (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S))"
      by (simp add: pathsCards_none)

    assume "x \<notin> domA \<Gamma>"
    hence [simp]: "(FBinds \<Gamma>\<cdot>ae) x = empty" by (metis ExpAnalysis.AnalBinds_not_there empty_is_bottom)

    have *: "substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S) = substitute (FBinds \<Gamma>\<cdot>ae) (thunks ((x, e') # \<Gamma>)) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)"
      by (rule fun_cong[OF substitute_cong_T]) (auto simp add: thunks_Cons )
    also have "\<dots> = substitute (FBinds ((x, e') # \<Gamma>)\<cdot>ae) (thunks ((x, e') # \<Gamma>)) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)"
      using `x \<notin> carrier _`[unfolded *]
      by (auto intro: substitute_cong simp add: thunks_Cons)
    finally show "prognosis ae a ((x, e') # \<Gamma>, e, S) = prognosis ae a (\<Gamma>, e, S)" by simp
  next
    fix ae a \<Gamma> x S
    have "once \<sqsubseteq> (pathCard [x]) x" by (simp add: two_add_simp)
    also have "pathCard [x] \<sqsubseteq> pathsCard ({[],[x]})"
      by (rule paths_Card_above) simp
    also have "\<dots> = pathsCard (paths (single x))" by simp
    also have "single x \<sqsubseteq> (Fexp (Var x)\<cdot>a)" by (rule Fexp_Var)
    also have "\<dots> \<sqsubseteq> Fexp (Var x)\<cdot>a \<otimes>\<otimes> Fstack S" by (rule both_above_arg1)
    also have "\<dots> \<sqsubseteq> substitute  (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp (Var x)\<cdot>a \<otimes>\<otimes> Fstack S)" by (rule substitute_above_arg)
    also have "pathsCard (paths \<dots>) x =  prognosis ae a (\<Gamma>, Var x, S) x" by simp
    finally
    show "once \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S) x"
      by this (rule cont2cont_fun, intro cont2cont)+
  qed
end

context FutureAnalysisCardinalityHeap
begin

  definition cHeap where
    "cHeap \<Gamma> e = (\<Lambda> a. pathsCard (paths (Fheap \<Gamma> e\<cdot>a)))"

  lemma cHeap_simp: "(cHeap \<Gamma> e)\<cdot>a = pathsCard (paths (Fheap \<Gamma> e\<cdot>a))"
    unfolding cHeap_def  by (rule beta_cfun) (intro cont2cont)
  
  (*
  lemma cHeap_eqvt: "\<pi> \<bullet> (cHeap \<Gamma> e) = cHeap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
    unfolding cHeap_def
    apply perm_simp
    apply (simp add: Fheap_eqvt)
    apply (rule Abs_cfun_eqvt)
    apply (intro cont2cont)
    done
  *)

  sublocale CardinalityHeap Aexp Aheap cHeap
  proof
  (*
    note cHeap_eqvt[eqvt]
    fix \<pi> show "\<pi> \<bullet> cHeap = cHeap" by perm_simp rule
  next
  *)
    fix x \<Gamma> e a
    assume "x \<in> thunks \<Gamma>"
    moreover
    assume "many \<sqsubseteq> (cHeap \<Gamma> e\<cdot>a) x"
    hence "many \<sqsubseteq> pathsCard (paths (Fheap \<Gamma> e \<cdot>a)) x" unfolding cHeap_def by simp
    hence "\<exists>p\<in> (paths (Fheap \<Gamma> e\<cdot>a)). \<not> (one_call_in_path x p)" unfolding pathsCard_def
      by (auto split: if_splits)
    ultimately
    show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
      by (metis Fheap_thunk)
  next
    fix \<Gamma> e a
    show "edom (cHeap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    by (simp add: cHeap_def Union_paths_carrier carrier_Fheap)
  qed

  sublocale CardinalityPrognosisEdom prognosis Aexp Aheap
  proof
    fix ae a \<Gamma> e S
    show "edom (prognosis ae a (\<Gamma>, e, S)) \<subseteq> fv \<Gamma> \<union> fv e \<union> fv S"
      apply (simp add: Union_paths_carrier)
      apply (rule carrier_substitute_below)
      apply (auto simp add: carrier_Fexp dest: set_mp[OF Aexp_edom] set_mp[OF ap_fv_subset] set_mp[OF carrier_FBinds])
      done
  qed
  
  sublocale CardinalityPrognosisCorrectLet prognosis Aexp Aheap cHeap
  proof
    fix \<Delta> \<Gamma> :: heap and e :: exp and S :: stack and  ae :: AEnv and a :: Arity
    assume "atom ` domA \<Delta> \<sharp>* \<Gamma>"
    assume "atom ` domA \<Delta> \<sharp>* S"
    assume "edom ae \<subseteq> domA \<Gamma> \<union> upds S"

    have "domA \<Delta> \<inter> edom ae = {}"
      using fresh_distinct[OF `atom \` domA \<Delta> \<sharp>* \<Gamma>`] fresh_distinct_fv[OF `atom \` domA \<Delta> \<sharp>* S`] 
            `edom ae \<subseteq> domA \<Gamma> \<union> upds S` ups_fv_subset[of S]
      by auto

    have const_on1:  "\<And> x. const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (carrier ((FBinds \<Gamma>\<cdot>ae) x)) empty"
      unfolding const_on_edom_disj using fresh_distinct_fv[OF `atom \` domA \<Delta> \<sharp>* \<Gamma>`]
      by (auto dest!: set_mp[OF carrier_FBinds] set_mp[OF Fexp.edom_AnalBinds])
    have const_on2:  "const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (carrier (Fstack S)) empty"
      unfolding const_on_edom_disj using fresh_distinct_fv[OF `atom \` domA \<Delta> \<sharp>* S`]
      by (auto dest!: set_mp[OF carrier_FBinds] set_mp[OF Fexp.edom_AnalBinds] set_mp[OF ap_fv_subset ])
    have  const_on3: "const_on (FBinds \<Gamma>\<cdot>ae) (- (- domA \<Delta>)) FTree.empty"
      and const_on4: "const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (domA \<Gamma>) FTree.empty"
      unfolding const_on_edom_disj using fresh_distinct[OF `atom \` domA \<Delta> \<sharp>* \<Gamma>`]
      by (auto dest!:  set_mp[OF Fexp.edom_AnalBinds])

    have disj1: "\<And> x. carrier ((FBinds \<Gamma>\<cdot>ae) x) \<inter> domA \<Delta> = {}"
      using fresh_distinct_fv[OF `atom \` domA \<Delta> \<sharp>* \<Gamma>`]
      by (auto dest: set_mp[OF carrier_FBinds])
    hence disj1': "\<And> x. carrier ((FBinds \<Gamma>\<cdot>ae) x) \<subseteq> - domA \<Delta>" by auto
    have disj2: "\<And> x. carrier (Fstack S) \<inter> domA \<Delta> = {}"
      using fresh_distinct_fv[OF `atom \` domA \<Delta> \<sharp>* S`] ap_fv_subset[of S] by auto
    hence disj2': "carrier (Fstack S) \<subseteq> - domA \<Delta>" by auto
    

    {
    fix x
    have "(FBinds (\<Delta> @ \<Gamma>)\<cdot>(ae \<squnion> Aheap \<Delta> e\<cdot>a)) x = (FBinds \<Gamma>\<cdot>ae) x \<otimes>\<otimes> (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x"
    proof (cases "x \<in> domA \<Delta>")
      case True
      have "map_of \<Gamma> x = None" using True fresh_distinct[OF `atom \` domA \<Delta> \<sharp>* \<Gamma>`] by (metis disjoint_iff_not_equal domA_def map_of_eq_None_iff)
      moreover
      have "ae x = \<bottom>" using True `domA \<Delta> \<inter> edom ae = {}` by auto
      ultimately
      show ?thesis using True 
          by (auto simp add: Fexp.AnalBinds_lookup empty_is_bottom[symmetric] cong: option.case_cong)
    next
      case False
      have "map_of \<Delta> x = None" using False by (metis domA_def map_of_eq_None_iff)
      moreover
      have "(Aheap \<Delta> e\<cdot>a) x = \<bottom>" using False using edom_Aheap by (metis contra_subsetD edomIff)
      ultimately
      show ?thesis using False
         by (auto simp add: Fexp.AnalBinds_lookup empty_is_bottom[symmetric] cong: option.case_cong)
    qed
    }
    note FBinds = ext[OF this]

    {
    have "pathsCard (paths (substitute (FBinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) (thunks (\<Delta> @ \<Gamma>)) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)))
      = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks (\<Delta> @ \<Gamma>)) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks (\<Delta> @ \<Gamma>))  (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S))))"
       by (simp add: substitute_substitute[OF const_on1] FBinds)
    also have "substitute (FBinds \<Gamma>\<cdot>ae) (thunks (\<Delta> @ \<Gamma>)) = substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>)"
      apply (rule substitute_cong_T)
      using const_on3
      by (auto dest: set_mp[OF thunks_domA])
    also have "substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks (\<Delta> @ \<Gamma>)) = substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>)"
      apply (rule substitute_cong_T)
      using const_on4
      by (auto dest: set_mp[OF thunks_domA])
    also have "substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S) = substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a) \<otimes>\<otimes> Fstack S" 
      by (rule substitute_only_empty_both[OF const_on2])
    also note calculation
    }
    note eq_imp_below[OF this]
    also
    note env_restr_split[where S = "domA \<Delta>"]
    also
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a) \<otimes>\<otimes> Fstack S))) f|` domA \<Delta> 
        = pathsCard (paths (ftree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))))"
          by (simp add: filter_paths_conv_free_restr ftree_restr_both ftree_rest_substitute[OF disj1]  ftree_restr_is_empty[OF disj2])
    also
    have "ftree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<sqsubseteq> Fheap \<Delta> e\<cdot>a"  by (rule Fheap_substitute)
    also
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a) \<otimes>\<otimes> Fstack S))) f|` (- domA \<Delta>) =
          pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (ftree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<otimes>\<otimes> Fstack S)))"
          by (simp add: filter_paths_conv_free_restr2 ftree_rest_substitute2[OF disj1' const_on3] ftree_restr_both  ftree_restr_noop[OF disj2'])
    also have "ftree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks \<Delta>)  (Fexp e\<cdot>a)) \<sqsubseteq> Fexp (Terms.Let \<Delta> e)\<cdot>a" by (rule Fexp_Let)
    finally
    show "prognosis (Aheap \<Delta> e\<cdot>a \<squnion> ae) a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> cHeap \<Delta> e\<cdot>a \<squnion> prognosis ae a (\<Gamma>, Terms.Let \<Delta> e, S)"
      by (simp add: cHeap_def del: fun_meet_simp) 
  qed
end

end
