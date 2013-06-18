theory RemoveTaggedIndirection
imports LaunchburyCombinedTagged Indirections "Nominal-Utils"
begin

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


fun remdups' :: "'a list \<Rightarrow> 'a list" where
  "remdups' [] = []" |
  "remdups' (x#xs) = x # removeAll x (remdups' xs)"

definition resolveStack :: "var list \<Rightarrow> indirections \<Rightarrow> var list"(infixl "\<ominus>\<^sub>S" 60)
  where "resolveStack xs is = remdups' (xs \<ominus> is)"

lemma resolveStack_Cons[simp]: "(x # S) \<ominus>\<^sub>S is = (x \<ominus> is) # (removeAll (x \<ominus> is) (S \<ominus>\<^sub>S is))"
  unfolding resolveStack_def by simp

lemma resolveStack_eqvt[eqvt]: "\<pi> \<bullet> (S \<ominus>\<^sub>S is) = (\<pi> \<bullet> S) \<ominus>\<^sub>S (\<pi> \<bullet> is)"
  sorry

(*
lemma resolveStack_set[simp]: "x \<notin> heapVars is \<Longrightarrow> x \<in> set (S \<ominus>\<^sub>S is) \<longleftrightarrow> x \<in> set S"
  sorry
*)

lemma resolveStack_fresh_noop[simp]: "atom z \<sharp> S \<Longrightarrow> (S \<ominus>\<^sub>S (z, y) # is) = (S \<ominus>\<^sub>S is)"
  unfolding resolveStack_def by (induction "is" arbitrary: S) auto

lemma valid_ind_different: "valid_ind is \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> x \<noteq> y"
  by (induct  "is" rule: valid_ind.induct) (auto simp add: fresh_Pair)

lemma resolve_var_modifies: "valid_ind is \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> x \<noteq> x \<ominus> is" 
  sorry

lemma resolve_var_same_image[dest]: "valid_ind is \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> x \<ominus> is = y \<ominus> is"
  apply (induct  "is" rule: valid_ind.induct)
  apply (auto simp add: fresh_Pair)
  apply (metis heapVars_from_set heapVars_not_fresh)
  apply (metis fresh_heap_expr not_self_fresh)
  done

lemma resolveStack_ConsCons[simp]:
  "valid_ind is \<Longrightarrow> (x, y) \<in> set is \<Longrightarrow> y # x # S \<ominus>\<^sub>S is = (y \<ominus> is) # (removeAll (y \<ominus> is) (S \<ominus>\<^sub>S is))"
  unfolding resolveStack_def by auto

definition ind_for :: "indirections \<Rightarrow> heap \<Rightarrow> bool" where
  "ind_for is \<Gamma> = (\<forall> (x,y) \<in> set is. (x \<in> heapVars \<Gamma> \<and> ((map_of \<Gamma> x) = Some (Var y) \<or> (isLam (the (map_of \<Gamma> x)) \<and> map_of \<Gamma> x = map_of \<Gamma> y))))"

lemma ind_for_heapVars_subset:
  "ind_for is \<Gamma> \<Longrightarrow> heapVars is \<subseteq> heapVars \<Gamma>"
  unfolding ind_for_def heapVars_def by auto

lemma ind_var_or_lambda:
  "ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isVar (the (map_of \<Gamma> x)) \<or> isLam ( the (map_of \<Gamma> x))"
  unfolding heapVars_def ind_for_def by auto



lemma map_of_from_set[simp]: "distinctVars \<Gamma> \<Longrightarrow> (x, e) \<in> set \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some e" sorry
lemma map_of_from_set_iff[simp]: "distinctVars \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some e \<longleftrightarrow> (x, e) \<in> set \<Gamma>" sorry

lemma map_of_not_from_set[simp]: "x \<notin> heapVars \<Gamma> \<Longrightarrow> map_of \<Gamma> x = None" by (metis domIff dom_map_of_conv_heapVars)

lemma map_of_not_from_set_iff[simp]: "map_of \<Gamma> x = None \<longleftrightarrow> x \<notin> heapVars \<Gamma>" by (metis domIff dom_map_of_conv_heapVars)


lemma ind_var_or_lambda2:
  "distinctVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> (x,e) \<in> set \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isVar e \<or> isLam e"
  by (auto dest: ind_var_or_lambda)

lemma ind_for_Cons[simp]: "distinctVars ((x,e)#\<Gamma>) \<Longrightarrow> \<not> isVar e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ind_for is ((x,e)#\<Gamma>) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def
  by (auto simp add: distinctVars_Cons)

(*
lemma ind_for_Cons_notHeapVar[simp]: "x \<notin> heapVars is \<Longrightarrow> ind_for is ((x,e)#\<Gamma>) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def heapVars_def by fastforce
*)

lemma ind_for_larger_set: "distinctVars \<Gamma>' \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> set \<Gamma>  \<subseteq> set \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  unfolding ind_for_def
  apply (auto dest!: bspec)
  apply (auto simp add: heapVars_def)[3]
  apply (subgoal_tac "y \<in> heapVars \<Gamma>")
  sorry
  
lemma ind_for_larger[simp]: "distinctVars \<Gamma> \<Longrightarrow> x \<notin> heapVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> ind_for is ((x,y)#\<Gamma>)"
  by (auto intro: ind_for_larger_set simp add: distinctVars_Cons)
  
lemma ind_for_permutation: "distinctVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> \<Gamma> <~~> \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  by (auto intro: ind_for_larger_set[where \<Gamma> = \<Gamma>] simp add: perm_set_eq perm_distinctVars)

lemma ind_for_ConsCons[simp]: "x \<notin> heapVars \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> ind_for ((x,y)#is) ((x,Var y)#\<Gamma>)"
  unfolding ind_for_def by auto

lemma ind_for_supp_subset:
  assumes "ind_for is \<Gamma>"
  shows "supp is \<subseteq> supp \<Gamma>"
sorry
(*
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
*)

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
  assumes NoInd: "\<And> x. valid_ind is \<Longrightarrow> x \<notin> heapVars is \<Longrightarrow> P x"
  assumes Ind: "\<And> x y.  valid_ind is \<Longrightarrow> P y \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> P x"
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
      thus ?thesis by (rule NoInd[OF assms(1)])
    qed
    moreover
    from less have "(x,y) \<in> set is" by (metis nth_mem)
    ultimately
    show ?case by (rule Ind[OF assms(1)])
  qed
next
case False
  thus ?thesis by (rule NoInd[OF assms(1)])
qed

thm ind_for_induct

lemma ind_for_isLam: "ind_for is \<Gamma> \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> isLam (the (map_of \<Gamma> x)) \<Longrightarrow> isLam (the (map_of \<Gamma> y))"
  unfolding ind_for_def by auto

lemma resolve_isLam_there: "valid_ind is \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> (x \<ominus> is) \<in> heapVars \<Gamma>" 
  apply (induct x rule:ind_for_induct)
  apply simp
  apply auto
  apply (simp add: resolve_var_same_image)
  apply (case_tac "y \<in> heapVars is")
  apply auto
  sorry

lemma resolve_isLam_isLam: "valid_ind is \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isLam (the (map_of \<Gamma> x)) \<Longrightarrow> isLam (the (map_of \<Gamma> (x \<ominus> is)))"
  apply (induct x rule:ind_for_induct)
  apply simp
  apply auto
  apply (drule (2) ind_for_isLam)
  apply (simp add: resolve_var_same_image)
  apply (case_tac "y \<in> heapVars is")
  apply auto
  done

lemma Lambda_AnywhereI:
  assumes "x \<in> heapVars \<Gamma>"
  assumes "isLam (the (map_of \<Gamma> x))"
  shows "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^bsub>x#S\<^esub> \<Gamma>"
proof-
  from `x \<in> heapVars \<Gamma>` `isLam (the (map_of \<Gamma> x))`
  obtain e where "(x,e) \<in> set \<Gamma>" and "isLam e"
    apply (auto simp add: heapVars_def)
    by (metis map_of_is_SomeD the.simps weak_map_of_SomeI)
  obtain z e' where "e = Lam [z]. e'" by (metis `isLam e` isLam.simps(1) isLam.simps(3) isLam.simps(4) isVar.cases)
  obtain \<Gamma>' where perm: "(x,Lam [z]. e') # \<Gamma>' <~~> \<Gamma>"
    by (metis `(x, e) \<in> set \<Gamma>` `e = Lam [z]. e'` perm_remove perm_sym)

  have "(x,Lam [z]. e') # \<Gamma>' \<Down>\<^sup>i\<^sup>u\<^bsub>x#S\<^esub> (x,Lam [z]. e') # \<Gamma>'" by (rule Lambda)
  thus ?thesis
    by (rule Permute[OF perm perm])
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
case (DLambda x y e \<Gamma> S u "is")
  show ?case
  proof(cases "x \<in> heapVars is")
  case True
    hence [simp]: "x \<ominus> is \<noteq> x" by (rule resolve_var_modifies[OF `valid_ind _`, symmetric])

    have "x \<ominus> is \<in> heapVars (\<Gamma> \<ominus>\<^sub>h is)" sorry
    moreover
    from resolve_isLam_isLam[OF  `valid_ind is` `ind_for is _` True]
    have "isLam (the (map_of \<Gamma> (x \<ominus> is)))" by simp
    hence "isLam (the (map_of (\<Gamma> \<ominus>\<^sub>h is) (x \<ominus> is)))" sorry
    ultimately
    have "\<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is) # removeAll (x \<ominus> is) (S \<ominus>\<^sub>S is)\<^esub> \<Gamma> \<ominus>\<^sub>h is" by (rule Lambda_AnywhereI)
    with `x \<in> heapVars is`
    have "(x, Lam [y]. e) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> (x, Lam [y]. e) # \<Gamma> \<ominus>\<^sub>h is" by simp
    with  `ind_for is ((x, Lam [y]. e) # \<Gamma>)`   `valid_ind is`
    show ?thesis
      by -(rule exI[where x = "is"], auto intro: reds.Lambda)
  next
  case False
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
    show ?thesis using DLambda
      by -(rule exI[where x = "is"], auto intro: reds.Lambda)
  qed
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
case (DVariableNoUpd n \<Gamma> x y e S \<Delta> z "is")
  from `y \<notin> set (x # S)`
  have "x \<noteq> y" by auto

  from `ind_for is ((x, Var y) # \<Gamma>)`
  have "ind_for is ((n, e) # (x, Var y) # \<Gamma>)" by simp
  from DVariableNoUpd(20)[OF this `valid_ind is`]
  obtain is' where is': "(n, e) # (x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times>\<^bsub>n # y # x # S \<ominus>\<^sub>S is\<^esub> (n, z) # (x, Var y) # \<Delta> \<ominus>\<^sub>h is'"
    and "ind_for is' ((n, z) # (x, Var y) # \<Delta>)"
    and "heapVars is \<subseteq> heapVars is'"
    and "valid_ind is'"
    and hV: " heapVars is' \<inter> heapVars ((n, e) # (x, Var y) # \<Gamma>) \<subseteq> heapVars is"
    and "n # y # x # S \<ominus>\<^sub>S is' = n # y # x # S \<ominus>\<^sub>S is"
    by blast

  show ?case
  proof(cases "x \<in> heapVars is")
  case True
    have "(x,y) \<in> set is"
    proof-
      from True obtain y' where "(x,y') \<in> set is" by (auto simp add: heapVars_def)
      hence "(x, Var y') \<in> set  ((x, Var y) # \<Gamma>)"
        using `ind_for is ((x, Var y) # \<Gamma>)` by (auto simp add: ind_for_def dest:bspec)
      with `distinctVars ((x, Var y) # \<Gamma>)`
      have "y' = y" by (metis Pair_inject distinctVars_ConsD(1) exp_assn.eq_iff(1) heapVars_from_set set_ConsD)
      with `_ \<in> set is` show ?thesis by simp
    qed

    have [simp]: "x \<ominus> is = y \<ominus> is" sorry

    (*
    from `(x,y) \<in> set is`
    have [simp]: "y # x # S \<ominus>\<^sub>S is = x # S \<ominus>\<^sub>S is" by simp
    *)

    from `x \<in> heapVars is` `heapVars is \<subseteq> heapVars is'`
    have "x \<in> heapVars is'" by auto

    from `atom n \<sharp> is` have "n \<notin> heapVars is" by (metis heapVars_not_fresh)

    from is' `x \<in> heapVars is` `x \<in> heapVars is'` `n \<notin> heapVars is`
    have "(x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> (x, z) # \<Delta> \<ominus>\<^sub>h is'"
      apply simp
      sorry
    moreover
  
    from `ind_for is' _`
    have "ind_for is' ((y, e) # (x, z) # \<Delta>)"
      sorry
    moreover
    note `heapVars is \<subseteq> heapVars is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> heapVars ((x, Var y) # (y, e) # \<Gamma>) \<subseteq> heapVars is" by auto
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

    from value_not_var[OF DVariableNoUpd(19), simplified] `ind_for is' _` `valid_ind is'`
    have "n \<notin> heapVars is'"
      sorry
    with `heapVars is \<subseteq> heapVars is'`
    have "n \<notin> heapVars is" by auto

    from `x \<notin> heapVars is` hV
    have "x \<notin> heapVars is'" by auto

    have [simp]: "e \<ominus> is' = e \<ominus> is" sorry
    have [simp]: "y \<ominus> is' = y \<ominus> is" sorry

    have "atom n \<sharp> (\<Gamma> \<ominus>\<^sub>h is, x, y \<ominus> is, e \<ominus> is, S \<ominus>\<^sub>S is, \<Delta> \<ominus>\<^sub>h is', z \<ominus> is')" sorry
    moreover
    from `y \<notin> set (x # S)` `x \<noteq> y` `n \<notin> heapVars is`
    have "y \<ominus> is \<notin> set (x # (S \<ominus>\<^sub>S is))" sorry
    moreover
    have "(y \<ominus> is, e \<ominus> is) \<in> set (\<Gamma> \<ominus>\<^sub>h is)" sorry
    moreover
    from is' `n \<notin> heapVars is` `x \<notin> heapVars is` `n \<notin> heapVars is'` `x \<notin> heapVars is'`
    have "(n, e \<ominus> is) # (x, Var (y \<ominus> is)) # (\<Gamma> \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<times>\<^bsub>n # (y \<ominus> is) # x # (S \<ominus>\<^sub>S is)\<^esub> (n, z \<ominus> is') # (x, Var (y \<ominus> is)) # (\<Delta> \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_Var)
    ultimately
    have "(x, Var (y \<ominus> is)) # (\<Gamma> \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>\<times>\<^bsub>x # (S \<ominus>\<^sub>S is)\<^esub> (x, z \<ominus> is') # (\<Delta> \<ominus>\<^sub>h is')"
      by (rule VariableNoUpd)
    hence "(x, Var y) # \<Gamma> \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> (x, z) # \<Delta> \<ominus>\<^sub>h is'"
      using  `n \<notin> heapVars is` `x \<notin> heapVars is` `n \<notin> heapVars is'` `x \<notin> heapVars is'`
      by (simp add: resolveExp_Var)
    moreover
  
    from `ind_for is' _` (* `y \<notin> heapVars is'` `x \<notin> heapVars is'` *)
    have "ind_for is' ((x, z) # \<Delta>)"
      sorry
    moreover
    note `heapVars is \<subseteq> heapVars is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> heapVars ((x, Var y) # \<Gamma>) \<subseteq> heapVars is"
      sorry
    moreover
    from `n # y # x # S \<ominus>\<^sub>S is' = n # y # x # S \<ominus>\<^sub>S is`
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
case (DLet as \<Gamma> x body \<Delta> S u "is")
  show ?case sorry
next
case (DPermute \<Gamma> \<Gamma>' \<Delta> \<Delta>' S u "is")
  show ?case sorry
qed

end
