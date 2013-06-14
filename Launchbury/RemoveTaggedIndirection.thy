theory RemoveTaggedIndirection
imports LaunchburyCombinedTagged Indirections "Nominal-Utils"
begin

consts resolveStack :: "var list \<Rightarrow> indirections \<Rightarrow> var list"(infixl "\<ominus>\<^sub>S" 60)

lemma resolveStack_Cons_not[simp]: "x \<notin> heapVars is \<Longrightarrow> (x # S) \<ominus>\<^sub>S is = x # (S \<ominus>\<^sub>S is)"
  sorry

lemma resolveStack_eqvt[eqvt]: "\<pi> \<bullet> (S \<ominus>\<^sub>S is) = (\<pi> \<bullet> S) \<ominus>\<^sub>S (\<pi> \<bullet> is)"
  sorry

lemma resolveStack_set[simp]: "x \<notin> heapVars is \<Longrightarrow> x \<in> set (S \<ominus>\<^sub>S is) \<longleftrightarrow> x \<in> set S"
  sorry

lemma resolveStack_fresh_noop[simp]: "atom z \<sharp> S \<Longrightarrow> (S \<ominus>\<^sub>S (z, y) # is) = (S \<ominus>\<^sub>S is)"
  sorry

lemma resolveStack_ConsCons[simp]:
  "(x, y) \<in> set is \<Longrightarrow> y # x # S \<ominus>\<^sub>S is = x # S \<ominus>\<^sub>S is" sorry

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

lemma ind_for_smaller_index:
  assumes "valid_ind is"
  assumes "i < length is"
  assumes "j < length is"
  assumes "is ! i = (x,y)"
  assumes "is ! j = (y,y')"
  shows "j > i"
using assms
proof (induct arbitrary: i j rule:valid_ind.induct)
case ValidIndNil thus ?case by simp
next
case (ValidIndCons "is" a b i j)
  show ?case
  proof(cases i)
    case 0
    with ValidIndCons
    show ?thesis
      by (cases j) (auto simp add: fresh_Pair fresh_at_base)
  next
    case (Suc i')
    with ValidIndCons have "i' < length is" by auto

    show ?thesis
    proof (cases j)
    case 0
      with ValidIndCons  `i = Suc i'`
      have "atom y \<sharp> is" and "is ! i' = (x, y)" by (simp_all add: fresh_Pair)
      hence "(x,y) \<in> set is" using `i' < length is`
      by (metis nth_mem)
      with `atom y \<sharp> is` have "atom y \<sharp> (x,y)" by (metis fresh_list_elem)
      hence False by (simp add: fresh_Pair fresh_at_base)
      thus ?thesis by simp
    next
    case Suc with `i = Suc i'` ValidIndCons
      show ?thesis by (auto simp add: fresh_Pair fresh_at_base)
    qed
  qed
qed

lemma ind_for_induct[consumes 1, case_names NoInd Ind]:
  assumes "valid_ind is"
  assumes NoInd: "\<And> x. x \<notin> heapVars is \<Longrightarrow> P x"
  assumes Ind: "\<And> x y. P y \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> P x"
  shows "P x"
proof(cases "x \<in> heapVars is")
case True
  then obtain y i where "i < length is" and "is ! i = (x,y)" unfolding heapVars_def 
    by (auto simp add: in_set_conv_nth)
  thus ?thesis
  proof (induction i arbitrary: x y rule:measure_induct_rule[where f = "\<lambda>x . length is - x"])
  case (less i x y)
    have "P y"
    proof(cases "y \<in> heapVars is")
    case True
      then obtain y' j where "j < length is" and "is ! j = (y,y')" unfolding heapVars_def 
        by (auto simp add: in_set_conv_nth)
      from `valid_ind is` `i < length is` `j < length is` `is ! i = _` `is ! j = _`
      have "i < j" by (rule ind_for_smaller_index)
      hence "length is - j < length is - i" by (metis diff_less_mono2 less.prems(1))
      from less.IH[OF this `j < length is` `is ! j = (y,y')`]
      show ?thesis.
    next
    case False
      thus ?thesis by (rule NoInd)
    qed
    moreover
    from less have "(x,y) \<in> set is" by (metis nth_mem)
    ultimately
    show ?case by (rule Ind)
  qed
next
case False
  thus ?thesis by (rule NoInd)
qed

lemma value_not_var:
  "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>x#S\<^esub> \<Delta> \<Longrightarrow> (x,e) \<in> set \<Delta> \<Longrightarrow> \<not>isVar e"
by (induct \<Gamma> i u "x#S" \<Delta> arbitrary: x S  rule:distinct_reds.induct)
   (auto simp add: distinctVars_Cons heapVars_from_set perm_set_eq)

theorem
  "\<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d\<^bsub>S\<^esub> \<Delta> \<Longrightarrow>
    ind_for is \<Gamma> \<Longrightarrow>
    valid_ind is \<Longrightarrow>
    (*  fst (hd \<Gamma>') \<notin> heapVars is \<Longrightarrow> *)
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>S \<ominus>\<^sub>S is\<^esub> \<Delta> \<ominus>\<^sub>h is')
       \<and> ind_for is' \<Delta>
       \<and> heapVars is \<subseteq> heapVars is'
       \<and> (heapVars is' \<inter> heapVars \<Gamma>) \<subseteq> heapVars is
       \<and> valid_ind is'
       \<and> S \<ominus>\<^sub>S is' = S \<ominus>\<^sub>S is"
proof (nominal_induct \<Gamma> "\<surd>" u S \<Delta> avoiding: "is" rule:distinct_reds.strong_induct )
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
case (DApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z e' u "is")

  from `ind_for is ((x, App e y) # \<Gamma>)`
  have "ind_for is \<Gamma>" by simp

  from ind_for_subset[OF this] `distinctVars ((x, App e y) # \<Gamma>)`
  have "x \<notin> heapVars is"
    by (auto simp add: distinctVars_append distinctVars_Cons)

  from `ind_for is \<Gamma>` `atom n \<sharp> \<Gamma>`  `atom z \<sharp> \<Gamma>`
  have "atom n \<sharp> is" and "atom z \<sharp> is" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is" and "z \<notin> heapVars is" by (metis heapVars_not_fresh)+
 
  from `ind_for is \<Gamma>`
  have "ind_for is ((n, e) # (x, App (Var n) y) # \<Gamma>)" by simp
  moreover
  note `valid_ind is`
  moreover
  (*
  from `n \<notin> heapVars is`
  have "fst (hd ((n, e) # (x, App (Var n) y) # \<Gamma>')) \<notin> heapVars is" by (simp)
  moreover
  *)
  note DApplicationInd(26)[OF calculation]
  ultimately
  obtain "is'"
  where is': "(n, e) # (x, App (Var n) y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>n # x # S \<ominus>\<^sub>S is\<^esub>
        (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta> \<ominus>\<^sub>h is'"
      and "ind_for is' ((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>)"
      and hV: "heapVars is' \<inter> heapVars ((n, e) # (x, App (Var n) y) # \<Gamma>)  \<subseteq> heapVars is"
      and "valid_ind is'"
      and "heapVars is \<subseteq> heapVars is'"
      and "n # x # S \<ominus>\<^sub>S is' = n # x # S \<ominus>\<^sub>S is"
      by blast

  from `ind_for is' _`
  have "ind_for is' \<Delta>" by simp
  hence "ind_for ((z,y)#is') ((z, Var y) # (x, e') # \<Delta>)" by simp
  moreover

  from `ind_for is' \<Delta>` `atom n \<sharp> \<Delta>` `atom z \<sharp> \<Delta>`
  have "atom n \<sharp> is'" and "atom z \<sharp> is'" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is'" by (metis heapVars_not_fresh)

  from `valid_ind is'` `atom z \<sharp> is'` `atom z \<sharp> y`
  have "valid_ind ((z, y) # is')"
    by (auto intro!: ValidIndCons simp add: fresh_Pair)
  moreover
  (*
  from `x \<notin> heapVars is` hV
  have "x \<notin> heapVars is'" by auto
  with  `atom z \<sharp> x`
  have "fst (hd ((x, e') # \<Delta>')) \<notin> heapVars ((z, y) # is')"
    by simp
  moreover
  *)
  note DApplicationInd(28)[OF calculation]
  ultimately
  obtain "is''"
  where is'':"(z, Var y) # (x, e') # \<Delta> \<ominus>\<^sub>h (z, y) # is' \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x # S \<ominus>\<^sub>S (z, y) # is'\<^esub> \<Theta> \<ominus>\<^sub>h is''"
          and "ind_for is'' \<Theta>"
          and "valid_ind is''"
          and "heapVars ((z, y) # is') \<subseteq> heapVars is''"
          and hV': "heapVars is'' \<inter> heapVars ((z, Var y) # (x, e') # \<Delta>) \<subseteq> heapVars ((z, y) # is')"
          and "x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S (z, y) # is'"
          by blast

  from `x \<notin> heapVars is` hV
  have "x \<notin> heapVars is'" by auto
  with hV' `atom z \<sharp> x`
  have "x \<notin> heapVars is''" by (auto simp add: fresh_at_base)

  from `ind_for is'' \<Theta>` `atom n \<sharp> \<Theta>`
  have "atom n \<sharp> is''" by (auto intro: ind_for_fresh simp add: fresh_append)

  from is'  `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'`
    `distinctVars ((n, e) # (x, App (Var n) y) # \<Gamma>)` `distinct (n # x # S)`
  have [simp]:"y \<ominus> is' = y \<ominus> is" sorry
  (*
    apply (simp add: resolveExp_App)
    apply (drule distinct_redsI)
    apply (auto simp add: distinctVars_Cons)[1]
    apply auto[1]
    prefer 5
    apply (drule stack_unchanged[where x= x])
    apply auto[1]
    apply auto[1]
    sorry
  *)
  from  `n # x # S \<ominus>\<^sub>S is' = n # x # S \<ominus>\<^sub>S is`
        `n \<notin> heapVars is'` `n \<notin> heapVars is` `x \<notin> heapVars is'` `x \<notin> heapVars is`
  have [simp]: "S \<ominus>\<^sub>S is' = S \<ominus>\<^sub>S is" by simp

  from `heapVars ((z, y) # is') \<subseteq> heapVars is''` 
  have "z \<in> heapVars is''" by auto
  with `valid_ind is''`
  have "atom z \<sharp> \<Theta> \<ominus>\<^sub>h is''"
    by (auto intro!: resolveHeap_fresh)
 
  {
    from is' `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'` `atom z \<sharp> is` `atom z \<sharp> is'`
    have "(n, e \<ominus> is) # (x, App (Var n) (y \<ominus> is)) # (\<Gamma> \<ominus>\<^sub>h is)
      \<Down>\<^sup>\<times>\<^sup>u\<^bsub>n # x # (S \<ominus>\<^sub>S is)\<^esub> (n, Lam [z]. (e' \<ominus> is')) # (x, App (Var n) (y \<ominus> is)) # (\<Delta> \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_App resolveExp_Var resolveExp_Lam)
  } moreover {
    from is'' `atom z \<sharp> \<Delta>` `atom z \<sharp> x`  `atom z \<sharp> is'` `x \<notin> heapVars is'` `atom z \<sharp> S`
    have "(x, (e' \<ominus> is')[z::=(y \<ominus> is)]) # (\<Delta> \<ominus>\<^sub>h is') \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x # (S \<ominus>\<^sub>S is)\<^esub> \<Theta> \<ominus>\<^sub>h is''"
      by (simp add: resolve_subst)
  }
  ultimately
  have "(x, App (e \<ominus> is) (y \<ominus> is)) # (\<Gamma> \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x # (S \<ominus>\<^sub>S is)\<^esub> \<Theta> \<ominus>\<^sub>h is''"
    apply(rule Application[rotated 2])
    using  `atom n \<sharp> x`  `atom n \<sharp> z`  `atom n \<sharp> is`  `atom n \<sharp> is'`  `atom n \<sharp> is''` `atom n \<sharp> \<Gamma>` 
          `atom n \<sharp> \<Delta>`  `atom n \<sharp> e` `atom n \<sharp> y`  `atom n \<sharp> \<Theta>`  `atom n \<sharp> S`
    using  `atom z \<sharp> x` `atom z \<sharp> is`  `atom z \<sharp> is'`  `atom z \<sharp> \<Gamma>` 
          `atom z \<sharp> \<Delta>` `atom z \<sharp> e` `atom z \<sharp> y` `atom z \<sharp> S`
    using `atom z \<sharp> \<Theta> \<ominus>\<^sub>h is''`
      apply (auto simp add: fresh_Pair fresh_append 
        intro: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
         eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
        eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt]
        eqvt_fresh_cong2[where f = resolveStack, OF resolveStack_eqvt]
        resolveHeapOneFresh subst_is_fresh(1))
      done

  with `x \<notin> heapVars is`
  have "(x, App e y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u\<^bsub> x # S \<ominus>\<^sub>S is\<^esub> \<Theta> \<ominus>\<^sub>h is''"
    by (simp add: resolveExp_App)
  moreover
  note `ind_for is'' _`
  moreover
  note `valid_ind is''`
  moreover
  from `heapVars is \<subseteq> heapVars is'` and `_ \<subseteq> heapVars is''`
  have "heapVars is \<subseteq> heapVars is''" by auto
  moreover

  { fix x'
    assume "x' \<in> heapVars is''"
    hence "x' \<noteq> x" and "x' \<noteq> n" 
      using `x \<notin> heapVars is''` `atom n \<sharp> is''` by (auto dest: heapVars_not_fresh)

    assume "x' \<in> heapVars \<Gamma>"
    with reds_doesnt_forget'[OF DApplicationInd.hyps(25), simplified] `x' \<noteq> x` `x' \<noteq> n`
    have "x' \<in> heapVars \<Delta>" by auto
    moreover
    have "x' \<noteq> z" by (metis DApplicationInd.hyps(15) calculation heapVars_not_fresh)
    moreover
    note `x' \<in> heapVars is''` hV'
    ultimately
    have "x' \<in> heapVars is'" by auto
    with hV `x' \<in> heapVars \<Gamma>`
    have "x' \<in> heapVars is" by auto
  }
  with `x \<notin> heapVars is''`
  have "heapVars is'' \<inter> heapVars ((x, App e y) # \<Gamma>) \<subseteq> heapVars is"
    by auto
  moreover
  from `x \<notin> heapVars is''`  `x \<notin> heapVars is`  `x \<notin> heapVars is'` `x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S (z, y) # is'`
        `atom z \<sharp> S` `atom z \<sharp> x`
  have "x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S is"
    by simp
  ultimately 
  show ?case by auto
next
case (DVariable y x S \<Gamma> z \<Delta> "is")
  from `distinctVars ((y, z) # (x, Var y) # \<Delta>)`
  have "x \<noteq> y" by (auto simp add: distinctVars_Cons distinctVars_append)

  from DVariable(10)[OF  `ind_for is _` `valid_ind is`]
  obtain is' where is': "(x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>y # x # S \<ominus>\<^sub>S is\<^esub> (y, z) # (x, Var y) # \<Delta> \<ominus>\<^sub>h is'"
    and "ind_for is' ((y, z) # (x, Var y) # \<Delta>)"
    and "heapVars is \<subseteq> heapVars is'"
    and "valid_ind is'"
    and hV: "heapVars is' \<inter> heapVars ((x, Var y) # \<Gamma>) \<subseteq> heapVars is"
    and "y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is"
    by blast

  show ?case
  proof(cases "x \<in> heapVars is")
  case True
    have "(x,y) \<in> set is"
    proof-
      from True obtain y' where "(x,y') \<in> set is" by (auto simp add: heapVars_def)
      hence "(x, Var y') \<in> set ((x, Var y) # \<Gamma>)"
      using `ind_for is _`  by (auto simp add: ind_for_def dest: bspec)
      with `distinctVars ((x, Var y) # \<Gamma>)`
      have "y' = y" by (metis Pair_inject distinctVars_ConsD(1) exp_assn.eq_iff(1) heapVars_from_set set_ConsD)
      with `_ \<in> set is` show ?thesis by simp
    qed

    have [simp]: "x \<ominus> is = y \<ominus> is" sorry

    from `(x,y) \<in> set is`
    have [simp]: "y # x # S \<ominus>\<^sub>S is = x # S \<ominus>\<^sub>S is" by simp

    from `x \<in> heapVars is` `heapVars is \<subseteq> heapVars is'`
    have "x \<in> heapVars is'" by auto

    from is' `x \<in> heapVars is` `x \<in> heapVars is'`
    have "(x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> (y, z) # (x, z) # \<Delta> \<ominus>\<^sub>h is'" by simp
    moreover
  
    from `ind_for is' _`
    have "ind_for is' ((y, z) # (x, z) # \<Delta>)"
      sorry
    moreover
    note `heapVars is \<subseteq> heapVars is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> heapVars ((x, Var y) # \<Gamma>) \<subseteq> heapVars is" by auto
    moreover
    from `y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is`
    have "x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is"
      sorry
    (*
    moreover
    from `x \<notin> heapVars is'`
    have "fst (hd ((x, z) # \<Delta>')) \<notin> heapVars is'" by simp
    *)
    ultimately
    show ?thesis by blast
  next
  case False
    from `x \<notin> heapVars is` hV
    have "x \<notin> heapVars is'" by auto

    from value_not_var[OF DVariable(9), simplified] `ind_for is' _` `valid_ind is'`
    have "y \<notin> heapVars is'"
      by (metis DVariable.hyps(3) distinctVars_ConsD(1) ind_for_Cons ind_for_heapVars_subset set_mp)
    with `heapVars is \<subseteq> heapVars is'`
    have "y \<notin> heapVars is" by auto

    from `x \<notin> heapVars is` hV
    have "x \<notin> heapVars is'" by auto

    from `y \<notin> set (x # S)` `x \<noteq> y` `y \<notin> heapVars is`
    have "y \<notin> set (x # (S \<ominus>\<^sub>S is))" by simp
    moreover
    from is' `y \<notin> heapVars is` `x \<notin> heapVars is` `y \<notin> heapVars is'` `x \<notin> heapVars is'`
    have "(x, Var y) # (\<Gamma> \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>y # x # (S \<ominus>\<^sub>S is)\<^esub> (y, z \<ominus> is') # (x, Var y) # (\<Delta> \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_Var)
    ultimately
    have "(x, Var y) # (\<Gamma> \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>x # (S \<ominus>\<^sub>S is)\<^esub> (y, z \<ominus> is') # (x, z \<ominus> is') # (\<Delta> \<ominus>\<^sub>h is')"
      by (rule Variable)
    hence "(x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> (y, z) # (x, z) # \<Delta> \<ominus>\<^sub>h is'"
      using  `y \<notin> heapVars is` `x \<notin> heapVars is` `y \<notin> heapVars is'` `x \<notin> heapVars is'`
      by (simp add: resolveExp_Var)
    moreover
  
    from `ind_for is' _` (* `y \<notin> heapVars is'` `x \<notin> heapVars is'` *)
    have "ind_for is' ((x, Var y) # (y, z) # \<Delta>)"
      apply (rule ind_for_permutation)
      by (metis perm.swap)
    with `x \<notin> heapVars is'`
    have "ind_for is' ((x, z) # (y, z) # \<Delta>)"
      by auto
    hence "ind_for is' ((y, z) # (x, z) # \<Delta>)"
      apply (rule ind_for_permutation)
      by (metis perm.swap)
    moreover
    note `heapVars is \<subseteq> heapVars is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> heapVars ((x, Var y) # \<Gamma>) \<subseteq> heapVars is" by auto
    moreover
    from `y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is`
    have "x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is"
      sorry
    (*
    moreover
    from `x \<notin> heapVars is'`
    have "fst (hd ((x, z) # \<Delta>')) \<notin> heapVars is'" by simp
    *)
    ultimately
    show ?thesis by blast
  qed
next
(*
case (DVariableNoUpd y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> "is")
  from `distinctVars (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>)`
  have "x \<noteq> y" by (auto simp add: distinctVars_Cons distinctVars_append)

  from `distinctVars (((x, Var y) # \<Gamma>') @ \<Gamma>)`
  have "distinctVars \<Gamma>" by (simp add: distinctVars_Cons distinctVars_append)
  from delete_Cons_permutation[OF this `(y,e) \<in> set \<Gamma>`]
  have "\<Gamma> <~~> (y,e) # (delete y \<Gamma>)".
  hence "\<Gamma>' @ \<Gamma> <~~> \<Gamma>' @ (y,e) # (delete y \<Gamma>)" by (metis perm_append1_eq)
  hence "((x, Var y) # \<Gamma>') @ \<Gamma> <~~> (x, Var y) # (\<Gamma>' @ (y,e) # (delete y \<Gamma>))"
    by (metis append_Cons cons_perm_eq)
  hence perm: "((x, Var y) # \<Gamma>') @ \<Gamma> <~~> ((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>"
    by (metis (hide_lams, no_types) append_Cons perm.trans perm_append_Cons perm_append_swap)

  from `ind_for is _` perm
  have "ind_for is (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)"
    by (rule ind_for_permutation)

  note `ind_for is (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)`
  moreover
  note `valid_ind is`
  moreover
  have "y \<notin> heapVars is" sorry (* Needed? *)
  hence "fst (hd ((y, e) # (x, Var y) # \<Gamma>')) \<notin> heapVars is"  by simp
  moreover
  note DVariableNoUpd(7)[OF calculation]
  ultimately
  obtain is' where is': "delete y \<Gamma> \<ominus>\<^sub>h is : (y, e) # (x, Var y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times> \<Delta> \<ominus>\<^sub>h is' : (y, z) # (x, Var y) # \<Delta>' \<ominus>\<^sub>h is'"
    and "ind_for is' (((y, z) # (x, Var y) # \<Delta>') @ \<Delta>)"
    and "heapVars is \<subseteq> heapVars is'"
    and "valid_ind is'"
    and hV: "heapVars is' \<inter> heapVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>) \<subseteq> heapVars is"
    by blast
    
  have "\<Gamma> \<ominus>\<^sub>h is : (x, Var y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times> (y, e) # \<Delta> \<ominus>\<^sub>h is' : (x, z) # \<Delta>' \<ominus>\<^sub>h is'"
  proof(cases "x \<in> heapVars is")
  case True
    then obtain y' where "(x,y') \<in> set is" by (auto simp add: heapVars_def)
    hence "(x, Var y') \<in> set ((((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>))"
    using `ind_for is (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)`
      by (auto simp add: ind_for_def dest: bspec)
    with `distinctVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)`
    have "y' = y" sorry
    have [simp]: "x \<ominus> is = y \<ominus> is" sorry

    show ?thesis
    proof (cases "y \<in> heapVars is")
    case True
      have "x \<in> heapVars is'" and "y \<in> heapVars is'" sorry
      from is' `x \<in> heapVars is` `y \<in> heapVars is` `x \<in> heapVars is'` `y \<in> heapVars is'`
      show ?thesis by simp
    next
    case False
      have "x \<in> heapVars is'" and "y \<notin> heapVars is'" sorry
      from is' `x \<in> heapVars is`  `y \<notin> heapVars is`  `x \<in> heapVars is'` `y \<notin> heapVars is'`
      show ?thesis
        apply simp
        sorry
    qed
  next
  case False
    show ?thesis
    proof(cases "y \<in> heapVars is")
    case True
      then obtain x' where "(y,x') \<in> set is" by (auto simp add: heapVars_def)
      hence "(y, Var x') \<in> set ((((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>))"
      using `ind_for is (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)`
        by (auto simp add: ind_for_def dest: bspec)
      with `distinctVars (((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>)`
      have "e = Var x'" by (metis Cons_eq_appendI append_Nil distinctVarsE in_set_conv_decomp)
  
      have "x \<notin> heapVars is'" and "y \<in> heapVars is'" sorry
      from is' `x \<notin> heapVars is`  `y \<in> heapVars is`  `x \<notin> heapVars is'` `y \<in> heapVars is'`
      show ?thesis
        apply simp
        sorry
    next
    case False
      from `y \<notin> heapVars is` `x \<notin> heapVars is` hV
      have "y \<notin> heapVars is'" "x \<notin> heapVars is'" by auto

      have [simp]: "e \<ominus> is' = e \<ominus> is" sorry
      
      from `(y, e) \<in> set \<Gamma>` `y \<notin> heapVars is`
      have "(y, e \<ominus> is) \<in> set (\<Gamma> \<ominus>\<^sub>h is)" by (rule resolveHeap_set)
      moreover
      from is' `y \<notin> heapVars is` `x \<notin> heapVars is` `y \<notin> heapVars is'` `x \<notin> heapVars is'`
      have "delete y (\<Gamma> \<ominus>\<^sub>h is) : (y, e \<ominus> is) # (x, Var y) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<times> \<Delta> \<ominus>\<^sub>h is' : (y, z \<ominus> is') # (x, Var y) # (\<Delta>' \<ominus>\<^sub>h is')"
        by (simp add: resolveExp_Var)
      ultimately
      have "\<Gamma> \<ominus>\<^sub>h is : (x, Var y) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<times> (y, e \<ominus> is) # (\<Delta> \<ominus>\<^sub>h is') : (x, z \<ominus> is') # (\<Delta>' \<ominus>\<^sub>h is')"
        by (rule VariableNoUpd)
      hence "\<Gamma> \<ominus>\<^sub>h is : (x, Var y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times> (y, e) # \<Delta> \<ominus>\<^sub>h is' : (x, z) # \<Delta>' \<ominus>\<^sub>h is'"
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
  qed
next
*)
next
case (DVariableNoUpd y x S e \<Gamma> \<Delta> "is")
  show ?case sorry
next
case (DLet as \<Gamma> x body \<Delta> S u "is")
  show ?case sorry
next
case (DPermute \<Gamma> \<Gamma>' \<Delta> \<Delta>' S u "is")
  show ?case sorry
qed

end
