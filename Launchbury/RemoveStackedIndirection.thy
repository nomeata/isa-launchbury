theory RemoveStackedIndirection
imports LaunchburyCombinedStacked Indirections "Nominal-Utils"  "~~/src/HOL/Library/Permutation"
begin

definition ind_for :: "indirections \<Rightarrow> heap \<Rightarrow> bool" where
  "ind_for is \<Gamma> = (\<forall> (x,y) \<in> set is. (x, Var y) \<in> set \<Gamma>)"

lemma ind_for_heapVars_subset:
  "ind_for is \<Gamma> \<Longrightarrow> heapVars is \<subseteq> heapVars \<Gamma>"
  unfolding ind_for_def
  apply (auto simp add: heapVars_def)
  by (metis (lifting) fst_conv imageI splitD)

nominal_primrec isVar :: "exp \<Rightarrow> bool" where
  "isVar (Var x) = True" |
  "isVar (Lam [x]. e) = False" |
  "isVar (App e x) = False" |
  "isVar (Let as e) = False"
  unfolding isVar_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_assn.exhaust(1))
  apply auto
  done
termination (eqvt) by lexicographic_order

lemma non_var_not_ind:
  "distinctVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> (x,e) \<in> set \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isVar e"
  unfolding heapVars_def ind_for_def
  by (auto dest: distinctVarsE)

lemma ind_for_Cons[simp]: "\<not> isVar e \<Longrightarrow> ind_for is ((x,e)#\<Gamma>) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def by auto

lemma ind_for_Cons_notHeapVar[simp]: "x \<notin> heapVars is \<Longrightarrow> ind_for is ((x,e)#\<Gamma>) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def heapVars_def by fastforce

lemma ind_for_larger_set: "ind_for is \<Gamma> \<Longrightarrow> set \<Gamma>  \<subseteq> set \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  unfolding ind_for_def by auto

lemma ind_for_larger[simp]: "ind_for is \<Gamma> \<Longrightarrow> ind_for is (x#\<Gamma>)"
  by (auto elim: ind_for_larger_set)
  
lemma ind_for_permutation: "ind_for is \<Gamma> \<Longrightarrow> \<Gamma> <~~> \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  by (auto elim: ind_for_larger_set simp add: perm_set_eq)

lemma ind_for_ConsCons[simp]: "ind_for is (\<Gamma>) \<Longrightarrow> ind_for ((x,y)#is) ((x,Var y)#\<Gamma>)"
  unfolding ind_for_def by auto

lemma ind_for_subset:  "ind_for is \<Gamma> \<Longrightarrow> heapVars is \<subseteq> heapVars \<Gamma>"
  unfolding ind_for_def heapVars_def 
  apply (auto dest: imageE dest!: bspec)
  by (metis heapVars_def heapVars_from_set)

lemma ind_for_supp_subset:
  assumes "ind_for is \<Gamma>"
  shows "supp is \<subseteq> supp \<Gamma>"
proof
  fix x 
  assume "x \<in> supp is"
  hence "x \<in> (\<Union>i \<in> set is . supp i)" by (metis supp_set supp_of_finite_sets finite_set)
  then obtain a b  where "(a,b) \<in> set is" and "x \<in> supp (a,b)" by (metis PairE UN_E)
  with assms[unfolded ind_for_def]
  have "(a,Var b) \<in> set \<Gamma>" and "x \<in> supp (a, Var b)"
    by (auto simp add: supp_Pair exp_assn.supp)
  thus "x \<in> supp \<Gamma>" by (metis (full_types) set_mp supp_set_mem)
qed

lemma ind_for_fresh: "ind_for is \<Gamma> \<Longrightarrow> a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> is"
  by (auto dest: ind_for_supp_subset simp add: fresh_def)

lemma delete_Cons_permutation: "distinctVars \<Gamma> \<Longrightarrow> (y, e) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> <~~> (y, e) # delete y \<Gamma>"
  by (induction \<Gamma> rule:distinctVars.induct) (auto simp add: delete_no_there heapVars_from_set)

theorem
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> ind_for is (\<Gamma>'@\<Gamma>) \<Longrightarrow> valid_ind is \<Longrightarrow> fst (hd \<Gamma>') \<notin> heapVars is \<Longrightarrow>
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : \<Delta>' \<ominus>\<^sub>h is')
       \<and> ind_for is' (\<Delta>'@\<Delta>)
       \<and> heapVars is \<subseteq> heapVars is'
       \<and> (heapVars is' \<inter> heapVars (\<Gamma>'@\<Gamma>)) \<subseteq> heapVars is
       \<and> valid_ind is'"
proof (nominal_induct \<Gamma> \<Gamma>' "\<surd>" u \<Delta> \<Delta>' avoiding: "is" rule:distinct_reds.strong_induct )
case (DLambda x y e \<Gamma>' \<Gamma> u "is")
  from DLambda have "x \<notin> heapVars is"
    by (auto simp add: distinctVars_Cons dest: set_mp[OF ind_for_subset])
  moreover
  (* We need to rename y to avoid is *)
  obtain y' :: var where "atom y' \<sharp> (y, e, is)" by (rule obtain_fresh)
  {
    hence "atom y' \<sharp> e" and "atom y' \<sharp> y" and "atom y' \<sharp> is" by (simp_all add: fresh_Pair)
    from this(1,2)
    have "Lam [y]. e = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)"
      by (rule change_Lam_Variable)
    also
    from `atom y' \<sharp> is`
    have "(Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)) \<ominus> is = Lam [y']. (((y \<leftrightarrow> y') \<bullet> e) \<ominus> is)"
    by (rule resolveExp_Lam)
    finally
    have "(Lam [y]. e) \<ominus> is = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e \<ominus> is)".
  }
  ultimately
  show ?case using DLambda
    by -(rule exI[where x = "is"], auto intro: reds.Lambda)
next
case (DApplicationInd n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e' u "is")
  hence "x \<notin> heapVars is" by simp

  from `ind_for is (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "ind_for is (\<Gamma>'@\<Gamma>)" by simp

  from `ind_for is (\<Gamma>'@ \<Gamma>)` `atom n \<sharp> \<Gamma>` `atom n \<sharp> \<Gamma>'`  `atom z \<sharp> \<Gamma>` `atom z \<sharp> \<Gamma>'`
  have "atom n \<sharp> is" and "atom z \<sharp> is" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is" and "z \<notin> heapVars is" by (metis heapVars_not_fresh)+
 
  from `ind_for is (\<Gamma>'@\<Gamma>)`
  have "ind_for is (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)" by simp
  moreover
  note `valid_ind is`
  moreover
  from `n \<notin> heapVars is`
  have "fst (hd ((n, e) # (x, App (Var n) y) # \<Gamma>')) \<notin> heapVars is" by (simp)
  moreover
  note DApplicationInd(24)[OF calculation]
  ultimately
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : ((n, e) # (x, App (Var n) y) # \<Gamma>') \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' \<ominus>\<^sub>h is'"
      and "ind_for is' (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>)"
      and hV: "heapVars is' \<inter> heapVars (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>) \<subseteq> heapVars is"
      and "valid_ind is'"
      and "heapVars is \<subseteq> heapVars is'"
      by blast

  from `ind_for is' _`
  have "ind_for is' (\<Delta>'@\<Delta>)" by simp
  hence "ind_for ((z,y)#is') ((z, Var y) # (x, e') # \<Delta>' @ \<Delta>)" by simp
  hence "ind_for ((z,y)#is') (((x, e') # \<Delta>') @ (z, Var y) # \<Delta>)"
    apply (rule ind_for_permutation)
    by (metis append_Cons perm_append_Cons)
  moreover

  from `ind_for is' (\<Delta>' @ \<Delta>)` `atom n \<sharp> \<Delta>` `atom n \<sharp> \<Delta>'` `atom z \<sharp> \<Delta>` `atom z \<sharp> \<Delta>'`
  have "atom n \<sharp> is'" and "atom z \<sharp> is'" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is'" by (metis heapVars_not_fresh)

  from `valid_ind is'` `atom z \<sharp> is'` `atom z \<sharp> y`
  have "valid_ind ((z, y) # is')"
    by (auto intro!: ValidIndCons simp add: fresh_Pair)
  moreover
  from `x \<notin> heapVars is` hV
  have "x \<notin> heapVars is'" by auto
  with  `atom z \<sharp> x`
  have "fst (hd ((x, e') # \<Delta>')) \<notin> heapVars ((z, y) # is')"
    by simp
  moreover
  note DApplicationInd(26)[OF calculation]
  ultimately
  obtain "is''"
  where is'':"(z, Var y) # \<Delta> \<ominus>\<^sub>h (z,y) # is' : (x, e') # \<Delta>' \<ominus>\<^sub>h (z,y)# is' \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
          and "ind_for is'' (\<Theta>' @ \<Theta>)"
          and "valid_ind is''"
          and "heapVars ((z, y) # is') \<subseteq> heapVars is''"
          and hV': "heapVars is'' \<inter> heapVars (((x, e') # \<Delta>') @ (z, Var y) # \<Delta>) \<subseteq> heapVars ((z, y) # is')"
          by blast

  have "x \<notin> heapVars is" by (metis (full_types) DApplicationInd.hyps(18) DApplicationInd.prems(1) append_Cons distinctVars_ConsD(1) ind_for_Cons ind_for_heapVars_subset isVar.simps(3) set_mp)
  have "x \<notin> heapVars is'" by (metis (full_types) DApplicationInd.hyps(20) `ind_for is' (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>)` append_Cons distinctVars_ConsD(1) distinctVars_ConsD(2) ind_for_Cons ind_for_heapVars_subset isVar.simps(2) isVar.simps(3) set_mp)

  from `ind_for is'' (\<Theta>' @ \<Theta>)` `atom n \<sharp> \<Theta>` `atom n \<sharp> \<Theta>'`
  have "atom n \<sharp> is''" by (auto intro: ind_for_fresh simp add: fresh_append)

  from is'  `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'`
  have [simp]:"y \<ominus> is' = y \<ominus> is"
    by (auto simp add: resolveExp_App dest: stack_unchanged)

  from `heapVars ((z, y) # is') \<subseteq> heapVars is''` 
  have "z \<in> heapVars is''" by auto
  with `valid_ind is''`
  have "atom z \<sharp> \<Theta> \<ominus>\<^sub>h is''" and "atom z \<sharp> \<Theta>' \<ominus>\<^sub>h is''"
    by (auto intro!: resolveHeap_fresh)
 
  {
    from is' `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'` `atom z \<sharp> is` `atom z \<sharp> is'`
    have "\<Gamma> \<ominus>\<^sub>h is : (n, e \<ominus> is) # (x, App (Var n) (y \<ominus> is)) # (\<Gamma>' \<ominus>\<^sub>h is)
      \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : (n, Lam [z]. (e' \<ominus> is')) # (x, App (Var n) (y \<ominus> is)) # (\<Delta>' \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_App resolveExp_Var resolveExp_Lam)
  } moreover {
    from is'' `atom z \<sharp> \<Delta>` `atom z \<sharp> \<Delta>'` `atom z \<sharp> x`  `atom z \<sharp> is'` `x \<notin> heapVars is'`
    have "\<Delta> \<ominus>\<^sub>h is' : (x, (e' \<ominus> is')[z::=(y \<ominus> is)]) # (\<Delta>' \<ominus>\<^sub>h is') \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
      by (simp add: resolve_subst)
  }
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : (x, App (e \<ominus> is) (y \<ominus> is)) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
    apply(rule Application[rotated 2])
    using  `atom n \<sharp> x`  `atom n \<sharp> z`  `atom n \<sharp> is`  `atom n \<sharp> is'`  `atom n \<sharp> is''` `atom n \<sharp> \<Gamma>`  `atom n \<sharp> \<Gamma>'`
          `atom n \<sharp> \<Delta>` `atom n \<sharp> \<Delta>'` `atom n \<sharp> e` `atom n \<sharp> y`  `atom n \<sharp> \<Theta>`  `atom n \<sharp> \<Theta>'`
    using  `atom z \<sharp> x` `atom z \<sharp> is`  `atom z \<sharp> is'`  `atom z \<sharp> \<Gamma>`  `atom z \<sharp> \<Gamma>'`
          `atom z \<sharp> \<Delta>` `atom z \<sharp> \<Delta>'` `atom z \<sharp> e` `atom z \<sharp> y`
    using `atom z \<sharp> \<Theta> \<ominus>\<^sub>h is''` `atom z \<sharp> \<Theta>' \<ominus>\<^sub>h is''`
      apply (auto simp add: fresh_Pair fresh_append 
        intro: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
         eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
        eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt]
        resolveHeapOneFresh subst_is_fresh(1))
      done

  with `x \<notin> heapVars is`
  have "\<Gamma> \<ominus>\<^sub>h is : (x, App e y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
    by (simp add: resolveExp_App)
  moreover
  note `ind_for is'' _`
  moreover
  note `valid_ind is''`
  moreover
  from `heapVars is \<subseteq> heapVars is'` and `_ \<subseteq> heapVars is''`
  have "heapVars is \<subseteq> heapVars is''" by auto
  moreover

  { from `x \<notin> heapVars is` hV hV' `atom z \<sharp> x`
    have "x \<notin> heapVars is''" by (auto simp add: fresh_at_base)
    moreover
    { fix x'
      assume "x' \<in> heapVars is''"
      hence "x' \<noteq> x" and "x' \<noteq> n" 
        using `x \<notin> heapVars is''` `atom n \<sharp> is''` by (auto dest: heapVars_not_fresh)

      assume "x' \<in> heapVars (\<Gamma>'@\<Gamma>)"
      with reds_doesnt_forget'[OF DApplicationInd.hyps(23), simplified] `x' \<noteq> x` `x' \<noteq> n`
      have "x' \<in> heapVars (\<Delta>'@\<Delta>)" by auto
      moreover
      have "x' \<noteq> z" by (metis DApplicationInd.hyps(11) DApplicationInd.hyps(12) `x' \<in> heapVars (\<Gamma>' @ \<Gamma>)` fresh_append heapVars_not_fresh)
      moreover
      note `x' \<in> heapVars is''` hV'
      ultimately
      have "x' \<in> heapVars is'" by auto
      with hV `x' \<in> heapVars (\<Gamma>'@\<Gamma>)`
      have "x' \<in> heapVars is" by auto
    }
    ultimately
    have "heapVars is'' \<inter> heapVars (((x, App e y) # \<Gamma>') @ \<Gamma>) \<subseteq> heapVars is"
      by auto
  }
  ultimately 
  show ?case by auto
next
case (DVariable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> "is")
  hence "x \<notin> heapVars is" by simp

  from `distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>)`
  have "distinctVars \<Gamma>" by (simp add: distinctVars_Cons distinctVars_append)
  from delete_Cons_permutation[OF this `(y,e) \<in> set \<Gamma>`]
  have "\<Gamma> <~~> (y,e) # (delete y \<Gamma>)".
  hence "\<Gamma>' @ \<Gamma> <~~> \<Gamma>' @ (y,e) # (delete y \<Gamma>)" by (metis perm_append1_eq)
  hence "((x, Var y) # \<Gamma>') @ \<Gamma> <~~> (x, Var y) # (\<Gamma>' @ (y,e) # (delete y \<Gamma>))"
    by (metis append_Cons cons_perm_eq)
  hence perm: "((x, Var y) # \<Gamma>') @ \<Gamma> <~~> ((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>"
    by (metis (hide_lams, no_types) append_Cons perm.trans perm_append_Cons perm_append_swap)

  show ?case
  proof(cases "y \<in> heapVars is")
  case True
    show ?thesis sorry
  next
  case False
    from `ind_for is _` perm
    have "ind_for is (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)"
      by (rule ind_for_permutation)
    moreover
    note `valid_ind is`
    moreover
    have "fst (hd ((y, e) # (x, Var y) # \<Gamma>')) \<notin> heapVars is" using False by simp
    moreover
    note DVariable(7)[OF calculation]
    ultimately
    obtain is' where is': "delete y \<Gamma> \<ominus>\<^sub>h is : (y, e) # (x, Var y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<surd> \<Delta> \<ominus>\<^sub>h is' : (y, z) # (x, Var y) # \<Delta>' \<ominus>\<^sub>h is'"
      and "ind_for is' (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>)"
      and "heapVars is \<subseteq> heapVars is'"
      and "valid_ind is'"
      and hV: "heapVars is' \<inter> heapVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>) \<subseteq> heapVars is"
      by blast

    from `y \<notin> heapVars is` `x \<notin> heapVars is` hV
    have "y \<notin> heapVars is'" "x \<notin> heapVars is'" by auto
    
    from `(y, e) \<in> set \<Gamma>` `y \<notin> heapVars is`
    have "(y, e \<ominus> is) \<in> set (\<Gamma> \<ominus>\<^sub>h is)" by (rule resolveHeap_set)
    moreover
    from is' `y \<notin> heapVars is` `x \<notin> heapVars is` `y \<notin> heapVars is'` `x \<notin> heapVars is'`
    have "delete y (\<Gamma> \<ominus>\<^sub>h is) : (y, e \<ominus> is) # (x, Var y) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<surd> \<Delta> \<ominus>\<^sub>h is' : (y, z \<ominus> is') # (x, Var y) # (\<Delta>' \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_Var)
    ultimately
    have "\<Gamma> \<ominus>\<^sub>h is : (x, Var y) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<surd> (y, z \<ominus> is') # (\<Delta> \<ominus>\<^sub>h is') : (x, z \<ominus> is') # (\<Delta>' \<ominus>\<^sub>h is')"
      by (rule Variable)
    hence "\<Gamma> \<ominus>\<^sub>h is : (x, Var y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<surd> (y, z) # \<Delta> \<ominus>\<^sub>h is' : (x, z) # \<Delta>' \<ominus>\<^sub>h is'"
      using  `y \<notin> heapVars is` `x \<notin> heapVars is` `y \<notin> heapVars is'` `x \<notin> heapVars is'`
      by (simp add: resolveExp_Var)
    moreover
    from `ind_for is' _`  `y \<notin> heapVars is'` `x \<notin> heapVars is'`
    have "ind_for is' (((x, z) # \<Delta>') @ (y, z) # \<Delta>)"
      by (auto elim: ind_for_larger_set)
    moreover
    note `heapVars is \<subseteq> heapVars is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> heapVars (((x, Var y) # \<Gamma>') @ \<Gamma>) \<subseteq> heapVars is" by auto
    moreover
    from `x \<notin> heapVars is'`
    have "fst (hd ((x, z) # \<Delta>')) \<notin> heapVars is'" by simp
    ultimately
    show ?thesis by blast
  qed
next
case (DVariableNoUpd y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> "is")
  show ?case sorry
next
case (DLet as \<Gamma> x \<Gamma>' body \<Delta>' \<Delta> u "is")
  show ?case sorry
qed

end
