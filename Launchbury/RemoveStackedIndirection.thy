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

lemma ind_for_permutation: "ind_for is \<Gamma> \<Longrightarrow> \<Gamma> <~~> \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  unfolding ind_for_def by (auto dest!: perm_set_eq)

theorem
  "\<Gamma> : \<Gamma>' \<Down>\<^sup>\<surd>\<^sup>u\<^sup>d \<Delta> : \<Delta>' \<Longrightarrow> ind_for is (\<Gamma>'@\<Gamma>) \<Longrightarrow>
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : \<Delta>' \<ominus>\<^sub>h is')
       \<and> ind_for is' (\<Delta>'@\<Delta>)"
proof (nominal_induct \<Gamma> \<Gamma>' "\<surd>" u \<Delta> \<Delta>' avoiding: "is" rule:distinct_reds.strong_induct )
case (DLambda x y e \<Gamma>' \<Gamma> u "is")
  from DLambda have "x \<notin> heapVars is"
    by (auto simp add: distinctVars_Cons dest: set_mp[OF ind_for_subset])
  moreover
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
(*
case (Application y \<Gamma> e x L \<Delta> \<Theta> z u e' "is" vars)
  from Application(11)
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x # L) \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : (Lam [y]. e') \<ominus> (is'@is)"
      and "atom ` fst ` set is' \<sharp>* (x # L)" and "set (atom y#vars) \<sharp>* is'" by blast

  from this(2)
  have "atom ` fst ` set is' \<sharp>* x" and "atom ` fst ` set is' \<sharp>*  L"
    by (simp_all add: fresh_star_Pair fresh_star_Cons)

  from `_ \<sharp>* is'`
  have "atom y \<sharp> is'" and  "set vars \<sharp>* is'"
    by (auto simp add: fresh_star_def)

  from Application(13)
  obtain "is''"
  where is'':"\<Delta> \<ominus>\<^sub>h is'@is : (e'[y::=x]) \<ominus> is'@is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is'@is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)"
          and "atom ` fst ` set is'' \<sharp>* L"  and "set (atom y#vars) \<sharp>* is''" by blast
  hence "atom y \<sharp> is''" and "set vars \<sharp>* is''" by (simp_all add: fresh_star_def)

  from `atom \` fst \` set is' \<sharp>* x`
  have [simp]: "x \<ominus> is' = x"
    by (rule resolve_var_fresh)
  from `atom \` fst \` set is' \<sharp>* L`
  have [simp]: "L \<ominus> is' = L"
    by (rule resolve_var_list_fresh)

  {
    note is'
    also
    from `atom y \<sharp> is` `atom y \<sharp> is'` 
    have "(Lam [y]. e' \<ominus> (is'@is)) =  Lam [y]. (e' \<ominus> (is'@is))"
      by (simp add: resolveExp_Lam)
    also
    have "x # L \<ominus> is = (x \<ominus> is) # (L \<ominus> is)" by simp
    finally
    have "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is) # (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h is' @ is : Lam [y]. (e' \<ominus> is' @ is)".
  }
  moreover
  { note is''
    also
    from `atom y \<sharp> is` `atom y \<sharp> is'`
    have "(e'[y ::= x]) \<ominus> (is'@is) = (e' \<ominus> (is'@is))[y ::= (x \<ominus> (is'@is))]" 
       by (simp add: resolve_subst)
    also
    have "L \<ominus> is' @ is = L \<ominus> is" by simp
    also
    have "x \<ominus> is' @ is = x \<ominus> is" by simp
    finally      
    have "\<Delta> \<ominus>\<^sub>h is'@is : (e' \<ominus> (is'@is))[y ::= (x \<ominus> is)] \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)".
  }
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : App (e \<ominus> is) (x \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ is' @ is : z \<ominus> is'' @ is' @ is"
    apply (rule reds.Application[rotated])
    using Application(1-9) `atom y \<sharp> is'`  `atom y \<sharp> is''`
    apply (auto simp add: fresh_Pair fresh_append
          intro!: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
           eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
          eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt])
    done
  moreover
  from `atom \` fst \` set is' \<sharp>* L` `atom \` fst \` set is'' \<sharp>* L`
  have "atom ` (fst ` (set (is'' @ is'))) \<sharp>* L"
    by (auto simp add: fresh_star_def)
  moreover
  from `set vars \<sharp>* is'` and  `set vars \<sharp>* is''`
  have "set vars \<sharp>* (is''@is')"
    by (simp add: fresh_star_append)
  ultimately
  show ?case
    by -(rule exI[where x = "is''@is'"], simp add: resolveExp_App resolve_var_append)
next
*)
case (DApplicationInd n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e' u "is")
  from `ind_for is (((x, App e y) # \<Gamma>') @ \<Gamma>)`
  have "ind_for is (((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>)" by simp
  from DApplicationInd(24)[OF this]
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : ((n, e) # (x, App (Var n) y) # \<Gamma>') \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' \<ominus>\<^sub>h is'"
      and "ind_for is' (((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>)"
      by blast

  from this(2)
  have "ind_for ((z,y)#is') ((z, Var y) # (x, e') # \<Delta>' @ \<Delta>)" by simp
  hence "ind_for ((z,y)#is') (((x, e') # \<Delta>') @ (z, Var y) # \<Delta>)"
    apply (rule ind_for_permutation)
    by (metis append_Cons perm_append_Cons)
  from DApplicationInd(26)[OF this]
  obtain "is''"
  where is'':"(z, Var y) # \<Delta> \<ominus>\<^sub>h (z,y) # is' : (x, e') # \<Delta>' \<ominus>\<^sub>h (z,y)# is' \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
          and "ind_for is'' (\<Theta>' @ \<Theta>)"
          by blast

  have [simp]:"e' \<ominus> is' = e' \<ominus> is" sorry
  have [simp]:"y \<ominus> is' = y \<ominus> is" sorry

  {
    have "x \<notin> heapVars is" and "n \<notin> heapVars is" and "atom z \<sharp> is"
    and  "x \<notin> heapVars is'" and "n \<notin> heapVars is'" and "atom z \<sharp> is'" sorry
    with is'
    have "\<Gamma> \<ominus>\<^sub>h is : (n, e \<ominus> is) # (x, App (Var n) (y \<ominus> is)) # (\<Gamma>' \<ominus>\<^sub>h is)
      \<Down>\<^sup>\<times>\<^sup>u \<Delta> \<ominus>\<^sub>h is' : (n, Lam [z]. (e' \<ominus> is)) # (x, App (Var n) (y \<ominus> is)) # (\<Delta>' \<ominus>\<^sub>h is')"
      by (simp add: resolveExp_App resolveExp_Var resolveExp_Lam)
  } moreover {
    from is''
    have "\<Delta> \<ominus>\<^sub>h is' : (x, (e' \<ominus> is)[z::=(y \<ominus> is)]) # (\<Delta>' \<ominus>\<^sub>h is') \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
      sorry
  }
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : (x, App (e \<ominus> is) (y \<ominus> is)) # (\<Gamma>' \<ominus>\<^sub>h is) \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''"
    apply(rule Application[rotated 2])
    sorry
  hence "\<Gamma> \<ominus>\<^sub>h is : (x, App e y) # \<Gamma>' \<ominus>\<^sub>h is \<Down>\<^sup>\<times>\<^sup>u \<Theta> \<ominus>\<^sub>h is'' : \<Theta>' \<ominus>\<^sub>h is''" sorry
  with `ind_for is'' _`
  show ?case
    by -(rule exI, auto)
next
case (Variable x e \<Gamma> i L \<Delta> z "is")
  show ?case sorry
next
case (VariableNoUpd x e \<Gamma> i L \<Delta> z "is")
  show ?case sorry
next
case (Let as \<Gamma> L body i u \<Delta> z "is")
  show ?case sorry
qed

end
