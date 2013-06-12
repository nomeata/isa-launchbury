theory RemoveStackedIndirection
imports LaunchburyCombinedStacked Indirections "Nominal-Utils"  "~~/src/HOL/Library/Permutation"
begin

(*
inductive ind_related :: "heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" ("_ : _ \<succeq> _ : _") where
  IndSym: "\<Gamma> : \<Gamma>' \<succeq> \<Gamma> : \<Gamma>'" |
  IndRemove: "(x, Var y) \<in> set (\<Gamma>@\<Gamma>') \<Longrightarrow> \<Gamma> : \<Gamma>' \<succeq> (resolveHeapOne \<Gamma> x y) : (resolveHeapOne \<Gamma>' x y)"
*)

(*
fun var_of :: "(heap \<times> heap) \<Rightarrow> var \<Rightarrow> var" where
  "var_of (\<Gamma>,\<Gamma>') x = (case map_of (\<Gamma>@\<Gamma>') x of Some (Var y) \<Rightarrow> y | None \<Rightarrow> x)"

fun resolveHeap' :: "(heap \<times> heap) \<Rightarrow> var list \<Rightarrow> (heap \<times> heap)" (infixl "\<ominus>\<^sub>H" 60) where
  "(\<Gamma>,\<Gamma>') \<ominus>\<^sub>H [] = (\<Gamma>,\<Gamma>')"
 | "(\<Gamma>,\<Gamma>') \<ominus>\<^sub>H (x#xs) = (resolveHeapOne \<Gamma> x (var_of (\<Gamma>,\<Gamma>') x),resolveHeapOne \<Gamma>' x (var_of (\<Gamma>,\<Gamma>') x)) \<ominus>\<^sub>H xs"

lemma resolveHeapNil[simp]: "([],[]) \<ominus>\<^sub>H is = ([],[])"
  by (induct "([],[])::(heap \<times> heap)" "is" rule:resolveHeap'.induct) simp_all

(*
lemma resolveHeapConsRemoved[simp]: "x \<in> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = \<Gamma> \<ominus>\<^sub>h is"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  apply (erule disjE)
  apply auto
  done
*)
(*
lemma resolveHeapCons[simp]: "x \<notin> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = (x, e \<ominus> is) # (\<Gamma> \<ominus>\<^sub>h is)"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  done
*)
lemma resolveHeap'_eqvt[eqvt]: "p \<bullet> resolveHeap' \<Gamma> is = resolveHeap' (p \<bullet> \<Gamma>) (p \<bullet> is)"
  by(induction \<Gamma> "is" rule:resolveHeap'.induct) simp_all

lemma resolveHeap_append[simp]: "\<Gamma> \<ominus>\<^sub>h (is'@is) = \<Gamma> \<ominus>\<^sub>h is' \<ominus>\<^sub>h is"
  apply (induct \<Gamma> "is'" rule:resolveHeap.induct)
  apply (auto)
  done
*)

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

lemma ind_for_larger[simp]: "ind_for is \<Gamma> \<Longrightarrow> ind_for is (x#\<Gamma>)"
  unfolding ind_for_def by auto

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

lemma ind_for_permutation: "ind_for is \<Gamma> \<Longrightarrow> \<Gamma> <~~> \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  unfolding ind_for_def by (auto dest!: perm_set_eq)

theorem
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> ind_for is (\<Gamma>'@\<Gamma>) \<Longrightarrow> valid_ind is \<Longrightarrow>
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : \<Delta>' \<ominus>\<^sub>h is')
       \<and> ind_for is' (\<Delta>'@\<Delta>)
       \<and> heapVars is \<subseteq> heapVars is'
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
  from `ind_for is (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "ind_for is (\<Gamma>'@\<Gamma>)" by simp
  hence "ind_for is (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)" by simp
  from DApplicationInd(24)[OF this `valid_ind is`]
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : ((n, e) # (x, App (Var n) y) # \<Gamma>') \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' \<ominus>\<^sub>h is'"
      and "ind_for is' (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>)"
      and "valid_ind is'"
      and "heapVars is \<subseteq> heapVars is'"
      by blast

  from `ind_for is (\<Gamma>'@ \<Gamma>)` `atom n \<sharp> \<Gamma>` `atom n \<sharp> \<Gamma>'`  `atom z \<sharp> \<Gamma>` `atom z \<sharp> \<Gamma>'`
  have "atom n \<sharp> is" and "atom z \<sharp> is" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is" by (metis heapVars_not_fresh)

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
  note DApplicationInd(26)
  ultimately
  obtain "is''"
  where is'':"(z, Var y) # \<Delta> \<ominus>\<^sub>h (z,y) # is' : (x, e') # \<Delta>' \<ominus>\<^sub>h (z,y)# is' \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
          and "ind_for is'' (\<Theta>' @ \<Theta>)"
          and "valid_ind is''"
          and "heapVars ((z, y) # is') \<subseteq> heapVars is''"
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
  ultimately 
  show ?case
    by -(rule exI, auto)
next
case (DVariable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> "is")
  show ?case sorry
next
case (DVariableNoUpd y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta> "is")
  show ?case sorry
next
case (DLet as \<Gamma> x \<Gamma>' body \<Delta>' \<Delta> u "is")
  show ?case sorry
qed

end
