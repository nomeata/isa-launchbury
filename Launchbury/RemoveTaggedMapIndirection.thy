theory RemoveTaggedMapIndirection
imports LaunchburyCombinedTaggedMap Indirections "Nominal-Utils" LaunchburyAddBH
begin


fun remdups' :: "'a list \<Rightarrow> 'a list" where
  "remdups' [] = []" |
  "remdups' (x#xs) = x # removeAll x (remdups' xs)"

lemma remdups'_noop[simp]: "distinct S \<Longrightarrow> remdups' S = S"
  by (induction rule:remdups'.induct) simp_all

lemma remdumps'_distinct[simp]: "distinct (remdups' xs)"
  by (induction xs rule:remdups'.induct) (auto intro: distinct_removeAll)

(*
definition resolveStack :: "var list \<Rightarrow> indirections \<Rightarrow> var list"(infixl "\<ominus>\<^sub>S" 60)
  where "resolveStack xs is = remdups' (xs \<ominus> is)"
*)

function resolveStack :: "var list \<Rightarrow> indirections \<Rightarrow> var list" (infixl "\<ominus>\<^sub>S" 60)
  where "(x,y) \<in> set is \<Longrightarrow> (y#x#S) \<ominus>\<^sub>S is = (x#S) \<ominus>\<^sub>S is"
      | "(x,y) \<notin> set is \<Longrightarrow> (y#x#S) \<ominus>\<^sub>S is = (y \<ominus> is) # ((x#S) \<ominus>\<^sub>S is)"
      | "[x] \<ominus>\<^sub>S is = [x \<ominus> is]"
      | "[] \<ominus>\<^sub>S is = []"
by (metis list.exhaust prod.exhaust) auto
termination  by (relation "measure (\<lambda> (x,y). size x)") auto

lemma resolveStack_set: "valid_ind is \<Longrightarrow> set (S \<ominus>\<^sub>S is) = (\<lambda> x. x \<ominus> is) ` set S"
  by (induction rule:resolveStack.induct) auto

fun dropChain :: "indirections \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> var list"
where "dropChain is y (x#xs) = (if (x,y) \<in> set is then dropChain is x xs else (x#xs))"
    | "dropChain is y [] = []"

declare dropChain.simps(1)[simp del]

lemma dropChainCons_simps[simp]:
  "(x,y) \<in> set is \<Longrightarrow> dropChain is y (x#xs) = dropChain is x xs"
  "(x,y) \<notin> set is \<Longrightarrow> dropChain is y (x#xs) = x#xs"
  "x \<notin> heapVars is \<Longrightarrow> dropChain is y (x#xs) = x#xs"
unfolding dropChain.simps(1) by (auto simp add: heapVars_from_set )

lemma dropChainCons_fresh:
  "atom y \<sharp> is     \<Longrightarrow> dropChain is y (x#xs) = x#xs"
  unfolding dropChain.simps(1) by (metis fresh_heap_expr not_self_fresh)

lemma dropChain_fresh_var[simp]:
  "atom y \<sharp> is     \<Longrightarrow> dropChain is y xs = xs"
  by (cases xs)(simp_all add: dropChainCons_fresh)

lemma resolveStack_fresh[simp]:
  "atom x \<sharp> is \<Longrightarrow> (x#S) \<ominus>\<^sub>S is = (x \<ominus> is) # (S \<ominus>\<^sub>S is)"
  apply (induction "x#S" "is" arbitrary: x S rule: resolveStack.induct)
  apply auto
  by (metis fresh_heap_expr not_self_fresh)

lemma resolveStack_Cons[simp]:
  "valid_ind is \<Longrightarrow> (x#S) \<ominus>\<^sub>S is = (x \<ominus> is) # ((dropChain is x S) \<ominus>\<^sub>S is)"
  by (induction "x#S" "is" arbitrary: x S rule: resolveStack.induct) auto

lemma resolveStack_Nil[simp]: "S \<ominus>\<^sub>S [] = S"
  by (induction S "[]::indirections" rule: resolveStack.induct) auto

lemma dropChain_set: "set (dropChain is x S) \<subseteq> set S"
  by (induction rule:dropChain.induct) (auto simp add: dropChain.simps(1))

lemma dropChain_supp: "supp (dropChain is x S) \<subseteq> supp S"
  by (induction rule:dropChain.induct) (auto simp add: dropChain.simps(1) supp_Cons supp_at_base)

lemma dropChain_fresh: "atom x \<sharp> S \<Longrightarrow> atom x \<sharp> dropChain is y S"
  by (metis fresh_def dropChain_supp set_mp)

lemma dropChain_Cons_fresh[simp]: "atom z \<sharp> S \<Longrightarrow>dropChain ((z,y)#is) x S = dropChain is x S" 
  by (induction "(z,y)#is" x S rule:dropChain.induct) (auto simp add: dropChain.simps(1) fresh_Cons)


(*
lemma resolveStack_Cons[simp]: "(x # S) \<ominus>\<^sub>S is = (x \<ominus> is) # (removeAll (x \<ominus> is) (S \<ominus>\<^sub>S is))"
  unfolding resolveStack_def by simp
*)

lemma resolveStack_eqvt[eqvt]: "\<pi> \<bullet> (S \<ominus>\<^sub>S is) = (\<pi> \<bullet> S) \<ominus>\<^sub>S (\<pi> \<bullet> is)"
  sorry

lemma dropChain_eqvt[eqvt]: "\<pi> \<bullet> (dropChain is x S) = dropChain (\<pi> \<bullet> is) (\<pi> \<bullet> x) (\<pi> \<bullet> S)"
  sorry

lemma resolveStack_distinct_fresh:
  assumes "distinct (S \<ominus>\<^sub>S is)"
  assumes "valid_ind is" "atom n \<sharp> is" "atom n \<sharp> S"
  shows "distinct (n # S \<ominus>\<^sub>S is)" 
using assms
by (auto dest:  eqvt_fresh_cong2[where f = resolveStack, OF resolveStack_eqvt] simp add: set_not_fresh)

(*
lemma resolveStack_distinct[simp]: "distinct (S \<ominus>\<^sub>S is)"
  unfolding resolveStack_def by simp
*)

(*
lemma resolveStack_set[simp]: "x \<notin> heapVars is \<Longrightarrow> x \<in> set (S \<ominus>\<^sub>S is) \<longleftrightarrow> x \<in> set S"
  sorry
*)

lemma resolveStack_fresh_noop[simp]: "atom z \<sharp> S \<Longrightarrow> (S \<ominus>\<^sub>S (z, y) # is) = (S \<ominus>\<^sub>S is)"
  by (induction S "(z, y) # is" arbitrary: "is" rule: resolveStack.induct)
     (auto simp add: fresh_Cons fresh_Nil)


(*
lemma resolveStack_ConsCons[simp]:
  "valid_ind is \<Longrightarrow> (x, y) \<in> set is \<Longrightarrow> y # x # S \<ominus>\<^sub>S is = (y \<ominus> is) # (removeAll (y \<ominus> is) (S \<ominus>\<^sub>S is))"
  unfolding resolveStack_def by auto
*)

definition ind_for :: "indirections \<Rightarrow> Heap \<Rightarrow> bool" where
  "ind_for is \<Gamma> = (\<forall> (x,y) \<in> set is. (x \<in> fdom \<Gamma> \<and> (((lookup \<Gamma> x) = Some (Var y) \<or> (isLam (\<Gamma> f! x)) \<and> lookup \<Gamma> x = lookup \<Gamma> y))))"

lemma ind_for_heapVars_subset:
  "ind_for is \<Gamma> \<Longrightarrow> heapVars is \<subseteq> fdom \<Gamma>"
  unfolding ind_for_def heapVars_def by auto

lemma ind_var_or_lambda:
  "ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isVar (\<Gamma> f! x) \<or> isLam (\<Gamma> f! x)"
  unfolding heapVars_def ind_for_def by auto

lemma ind_var_or_lambda2:
  "ind_for is \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some e \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isVar e \<or> isLam e"
  by (auto dest: ind_var_or_lambda)

lemma ind_for_Cons[simp]: "x \<notin> fdom \<Gamma> \<Longrightarrow> \<not> isVar e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ind_for is (\<Gamma>(x f\<mapsto> e)) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def
  apply (rule ball_cong[OF refl])
  apply clarsimp
  apply (case_tac "a=x")
  apply auto[1]
  by (metis fdomIff lookup_fmap_upd lookup_fmap_upd_other the.simps)

lemma fresh_not_setE[dest]: "atom x \<sharp> is \<Longrightarrow> (x,a) \<in> set is \<Longrightarrow> False" by (metis heapVars_from_set heapVars_not_fresh)

lemma ind_for_Cons_fresh[simp]: "atom x \<sharp> is \<Longrightarrow> ind_for is (\<Gamma>(x f\<mapsto> e)) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def
  apply (rule ball_cong[OF refl])
  apply clarsimp
  apply (case_tac "a=x")
  apply auto[1]
  by (metis fresh_heap_expr lookup_fmap_upd_other not_self_fresh)

(*
lemma ind_for_Cons_notHeapVar[simp]: "x \<notin> heapVars is \<Longrightarrow> ind_for is ((x,e)#\<Gamma>) \<longleftrightarrow> ind_for is \<Gamma>"
  unfolding ind_for_def heapVars_def by fastforce
*)

lemma ind_for_larger_set: "ind_for is \<Gamma> \<Longrightarrow> \<Gamma> \<le> \<Gamma>' \<Longrightarrow> ind_for is \<Gamma>'"
  unfolding ind_for_def
  apply (auto dest!: bspec dest: fmap_less_eqD elim: set_mp[OF fmap_less_fdom])
  by (metis fdomIff fmap_less_eqD)

lemma ind_for_larger[simp]: "x \<notin> fdom \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> ind_for is (\<Gamma>(x f\<mapsto> e))"
  by (auto elim!: ind_for_larger_set simp add: lookup_fmap_upd_eq)
  
lemma ind_for_ConsCons[simp]: "x \<notin> fdom \<Gamma> \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> ind_for ((x,y)#is) (\<Gamma>(x f\<mapsto> Var y))"
  unfolding ind_for_def
  by (auto  simp add: lookup_fmap_upd_eq fdomIff)

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


lemma ind_for_agrees: "(x, y) \<in> set is \<Longrightarrow> ind_for is (\<Gamma>(x f\<mapsto> Var y')) \<Longrightarrow> y' = y"
  unfolding ind_for_def by auto

lemma ind_for_isLam: "ind_for is \<Gamma> \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> isLam (\<Gamma> f! x) \<Longrightarrow> isLam (\<Gamma> f! y)"
  unfolding ind_for_def by auto

lemma ind_for_update: "isLam e \<Longrightarrow> ind_for is (\<Gamma>(y f\<mapsto> Var x)(x f\<mapsto> e)) \<Longrightarrow> ind_for is (\<Gamma>(y f\<mapsto> e)(x f\<mapsto> e))"
  unfolding ind_for_def  by (fastforce simp add: lookup_fmap_upd_eq)

lemma ind_for_copy: "lookup \<Gamma> y = Some (Var x) \<Longrightarrow> x \<in> fdom \<Gamma> \<Longrightarrow> isLam (\<Gamma> f! x) \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> ind_for is (fmap_copy \<Gamma> x y)"
  unfolding ind_for_def
  by (auto simp add: lookup_fmap_copy_eq)

lemma resolveHeap_fmap_copy:
  assumes "valid_ind is" "isLam (\<Delta> f! y)" "ind_for is \<Delta>" "x \<notin> heapVars is"
  shows "fmap_copy \<Delta> y x \<ominus>\<^sub>H is = fmap_copy (\<Delta> \<ominus>\<^sub>H is) (y \<ominus> is) x"
using assms(1-3)
proof (induction y rule: valid_ind_induct)
  case NoInd thus ?case using `x \<notin> heapVars is` by simp
next
  case (Ind y y')
    from Ind.hyps(2) Ind.prems 
    have y': "lookup \<Delta> y = lookup \<Delta> y'" unfolding ind_for_def by auto
    hence "fmap_copy \<Delta> y x = fmap_copy \<Delta> y' x"  by (rule fmap_copy_cong)
    moreover
    have "y \<ominus> is = y' \<ominus> is" by (rule resolve_var_same_image[OF Ind(1-2)])
    ultimately
    show ?case using Ind.IH Ind.prems y' by simp
qed



lemma lookup_resolveHeap': "x \<notin> heapVars is \<Longrightarrow> lookup (\<Gamma> \<ominus>\<^sub>H is) x = Option.map (\<lambda> x. x \<ominus> is) (lookup \<Gamma> x)"
  unfolding resolveHeap'_def
  by (auto simp add: fdomIff)

lemma the_lookup_resolveHeap': "x \<notin> heapVars is \<Longrightarrow> x \<in> fdom \<Gamma> \<Longrightarrow> (\<Gamma> \<ominus>\<^sub>H is) f! x = (\<Gamma> f! x) \<ominus> is"
  unfolding resolveHeap'_def
  by (auto simp add: fdomIff)

lemma isLam_resolve_exp[simp]: "isLam (e \<ominus> is) \<longleftrightarrow> isLam e"
  by (nominal_induct e avoiding: "is" rule: exp_assn.strong_induct(1))
     (simp_all add: resolveExp_Var resolveExp_App resolveExp_Lam resolveExp_Let)

lemma isVar_resolve_exp[simp]: "isVar (e \<ominus> is) \<longleftrightarrow> isVar e"
  by (nominal_induct e avoiding: "is" rule: exp_assn.strong_induct(1))
     (simp_all add: resolveExp_Var resolveExp_App resolveExp_Lam resolveExp_Let)

lemma resolve_isLam_there: "valid_ind is \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> (x \<ominus> is) \<in> fdom \<Gamma>" 
  apply (induct x rule:valid_ind_induct)
  apply simp
  apply auto
  apply (simp add: resolve_var_same_image)
  apply (case_tac "y \<in> heapVars is")
  apply auto
  sorry

lemma resolve_isLam_isLam: "valid_ind is \<Longrightarrow> ind_for is \<Gamma> \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> isLam (\<Gamma> f! x) \<Longrightarrow> isLam (\<Gamma> f! (x \<ominus> is))"
  apply (induct x rule:valid_ind_induct)
  apply simp
  apply auto
  apply (drule (2) ind_for_isLam)
  apply (simp add: resolve_var_same_image)
  apply (case_tac "y \<in> heapVars is")
  apply auto
  done


fun heap_of :: "Heap \<Rightarrow> var list \<Rightarrow> atom set"
  where "heap_of \<Gamma> S = supp (\<Gamma> f|` (- set S)) \<union> supp (lookup \<Gamma> (hd S))"
declare heap_of.simps[simp del]



(* Verm. falsch: Auf dem Stack liegt unten beliebiger Müll! *)
lemma stack_not_used:
  assumes "valid_ind is"
  assumes "ind_for is \<Gamma>"
  assumes "\<Gamma> \<Down>\<^sup>i\<^sup>u\<^sup>d\<^bsub>x # S\<^esub> \<Delta>"
  shows "x \<ominus> is \<notin> set S"
oops

theorem
  "\<Gamma> \<Down>\<^sup>\<surd>\<^sup>u\<^sup>\<times>\<^bsub>S\<^esub> \<Delta> \<Longrightarrow>
    ind_for is \<Gamma> \<Longrightarrow>
    valid_ind is \<Longrightarrow>
    (* distinct (S \<ominus>\<^sub>S is) \<Longrightarrow> *)
    (*  fst (hd \<Gamma>') \<notin> heapVars is \<Longrightarrow> *)
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>S \<ominus>\<^sub>S is\<^esub> \<Delta> \<ominus>\<^sub>H is')
       \<and> ind_for is' \<Delta>
       \<and> set is \<subseteq> set is'
       \<and> (heapVars is' \<inter> fdom \<Gamma>) \<subseteq> heapVars is
       \<and> valid_ind is'
       \<and> S \<ominus>\<^sub>S is' = S \<ominus>\<^sub>S is"
proof (nominal_induct \<Gamma> "\<surd>" u "\<times>" S \<Delta> avoiding: "is" rule:reds.strong_induct )
case (Lambda x \<Gamma> y e u S "is")
  show ?case
  proof(cases "x \<in> heapVars is")
  case True
    hence [simp]: "x \<ominus> is \<noteq> x" by (rule resolve_var_modifies[OF `valid_ind _`, symmetric])

    from resolve_isLam_there[OF `valid_ind is` `ind_for _ _` `x \<in> heapVars is`]
    have "x \<ominus> is \<in> fdom \<Gamma>" by simp
    with resolve_resolved[OF `valid_ind is`]
    have "x \<ominus> is \<in> fdom (\<Gamma> \<ominus>\<^sub>H is)" by simp
    moreover
    from resolve_isLam_isLam[OF `valid_ind is` `ind_for is _` True]
    have "isLam (\<Gamma> f! (x \<ominus> is))" by simp
    hence "isLam ((\<Gamma> \<ominus>\<^sub>H is) f! (x \<ominus> is))"
      by (simp add: the_lookup_resolveHeap'[OF  resolve_resolved[OF `valid_ind is`] `x \<ominus> is \<in> fdom \<Gamma>`])
    ultimately
    have "\<Gamma> \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>(x \<ominus> is) # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Gamma> \<ominus>\<^sub>H is"
      by (rule reds_LambdaI)
    with `x \<in> heapVars is` `valid_ind is`
    have "\<Gamma> \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> \<Gamma> \<ominus>\<^sub>H is" by simp
    with `ind_for is (\<Gamma>(x f\<mapsto> Lam [y]. e))`  `valid_ind is` True `x \<notin> fdom \<Gamma>`
    show ?thesis
      by -(rule exI[where x = "is"], auto)
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
    show ?thesis using Lambda
      by -(rule exI[where x = "is"],auto intro: reds.Lambda)
  qed
next
case (ApplicationInd n \<Gamma> x e y S \<Delta> \<Theta> z u e' "is")

  from `x \<notin> fdom \<Gamma>` `ind_for is (\<Gamma>(x f\<mapsto> App e y))`
  have "ind_for is \<Gamma>" by (metis ind_for_Cons isLam.simps(3) isVar.simps(3))

  from ind_for_heapVars_subset[OF this] `x \<notin> fdom \<Gamma>`
  have "x \<notin> heapVars is" by (auto simp add: distinctVars_append distinctVars_Cons)

  from `ind_for is \<Gamma>` `atom n \<sharp> \<Gamma>`  `atom z \<sharp> \<Gamma>`
  have "atom n \<sharp> is" and "atom z \<sharp> is" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is" and "z \<notin> heapVars is" by (metis heapVars_not_fresh)+
 
  from `ind_for is \<Gamma>` `x \<notin> fdom \<Gamma>` `atom n \<sharp> is`
  have "ind_for is (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e))" by simp
  moreover
  note `valid_ind is`
  moreover
  (*
  from `atom n \<sharp> S``atom n \<sharp> x`
  have "atom n \<sharp> (x # S)" by (simp add: fresh_Cons)
  with `distinct (x # S \<ominus>\<^sub>S is)` `valid_ind is` `atom n \<sharp> is` 
  have "distinct (n # x # S \<ominus>\<^sub>S is)"  by (rule resolveStack_distinct_fresh)
  moreover
  *)
  (*
  from `n \<notin> heapVars is`
  have "fst (hd ((n, e) # (x, App (Var n) y) # \<Gamma>')) \<notin> heapVars is" by (simp)
  moreover
  *)
  note ApplicationInd(18)[OF calculation]
  ultimately
  obtain "is'"
  where is': "\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e) \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>n # x # S \<ominus>\<^sub>S is\<^esub> \<Delta>(n f\<mapsto> Lam [z]. e') \<ominus>\<^sub>H is'"
      and "ind_for is' (\<Delta>(n f\<mapsto> Lam [z]. e'))"
      and hV: "heapVars is' \<inter> fdom (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e)) \<subseteq> heapVars is"
      and "valid_ind is'"
      and "set is \<subseteq> set is'"
      and "n # x # S \<ominus>\<^sub>S is' = n # x # S \<ominus>\<^sub>S is"
      by blast

  (* New invariant? *)
  (* TODO: Migrate to fmap 
  have "(supp is' - supp is) \<inter> supp ((n, e) # (x, App (Var n) y) # \<Gamma>)  \<subseteq> heap_of ((n, e) # (x, App (Var n) y) # \<Gamma>) (n # x # S)"
    sorry
  moreover
  have "heap_of ((n, e) # (x, App (Var n) y) # \<Gamma>) (n # x # S) \<subseteq> supp e \<union> supp \<Gamma>"
    sorry
  ultimately 
  have "atom n \<sharp> is'"
    using `atom n \<sharp> is`  `atom n \<sharp> e`  `atom n \<sharp> \<Gamma>`
    by (auto simp add: fresh_def supp_Cons supp_Pair supp_at_base)
  *)
  have "atom n \<sharp> is'" sorry

  have "z \<notin> fdom \<Delta>"by (metis ApplicationInd.hyps(15) fresh_fdom)

  from second_stack_element_unchanged[OF ApplicationInd.hyps(17)]  `atom n \<sharp> x`
  have "lookup \<Delta> x = Some (App (Var n) y)" by simp
 
  from `ind_for is' _` `atom n \<sharp> is'` 
  have "ind_for is' \<Delta>" by simp
  with `z \<notin> fdom \<Delta>`
  have "ind_for ((z,y)#is') (\<Delta>(z f\<mapsto> Var y))" by (rule ind_for_ConsCons)
  with `lookup \<Delta> x = Some (App (Var n) y)` `atom z \<sharp> x`
  have "ind_for ((z,y)#is') (\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e'))"
    unfolding ind_for_def
    by (auto simp add: lookup_fmap_upd_eq)
  moreover

  from `ind_for is' \<Delta>` `atom n \<sharp> \<Delta>` `atom z \<sharp> \<Delta>`
  have "atom n \<sharp> is'" and "atom z \<sharp> is'" by (auto intro: ind_for_fresh simp add: fresh_append)
  hence "n \<notin> heapVars is'" by (metis heapVars_not_fresh)

  from `valid_ind is'` `atom z \<sharp> is'` `atom z \<sharp> y`
  have "valid_ind ((z, y) # is')"
    by (auto intro!: ValidIndCons simp add: fresh_Pair)
    
  from `n # x # S \<ominus>\<^sub>S is' = n # x # S \<ominus>\<^sub>S is` `atom n \<sharp> is'` `atom n \<sharp> is`
  have [simp]:"x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is" by simp

  from  `atom z \<sharp> S` `atom z \<sharp> x` 
  have [simp]:"x # S \<ominus>\<^sub>S (z,y) # is' = x # S \<ominus>\<^sub>S is'"
    by (auto intro: resolveStack_fresh_noop simp add: fresh_Cons)
  
  note `valid_ind ((z, y) # is')`
  moreover
  (*
  from `x \<notin> heapVars is` hV
  have "x \<notin> heapVars is'" by auto
  with  `atom z \<sharp> x`
  have "fst (hd ((x, e') # \<Delta>')) \<notin> heapVars ((z, y) # is')"
    by simp
  moreover
  *)
  note ApplicationInd(20)[OF calculation]
  (*
  moreover
  from `distinct (n # x # S \<ominus>\<^sub>S is)` `atom n \<sharp> is `
  have "distinct (x # S \<ominus>\<^sub>S (z,y) # is')" by simp
  ultimately
  *)
  then
  obtain "is''"
  where is'':"\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e') \<ominus>\<^sub>H (z, y) # is' \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S (z, y) # is'\<^esub> \<Theta> \<ominus>\<^sub>H is''"
          and "ind_for is'' \<Theta>"
          and "valid_ind is''"
          and "set ((z, y) # is') \<subseteq> set is''"
          and hV': " heapVars is'' \<inter> fdom (\<Delta>(z f\<mapsto> Var y)(x f\<mapsto> e')) \<subseteq> heapVars ((z, y) # is')"
          and "x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S (z, y) # is'"
          by blast
  ultimately have True by simp -- "clear calculation"

  from `x \<notin> heapVars is` hV
  have "x \<notin> heapVars is'" by auto
  with hV' `atom z \<sharp> x`
  have "x \<notin> heapVars is''" by (auto simp add: fresh_at_base)

  from `ind_for is'' \<Theta>` `atom n \<sharp> \<Theta>`
  have "atom n \<sharp> is''" by (auto intro: ind_for_fresh simp add: fresh_append)

 
 from is' `x \<notin> fdom \<Gamma>` `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'` `atom z \<sharp> is` `atom z \<sharp> is'`  `atom n \<sharp> x` `valid_ind is` `atom n \<sharp> \<Gamma>` `atom n \<sharp> \<Delta>`
  have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> App (Var n) (y \<ominus> is))(n f\<mapsto> e \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>n # x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub>  (\<Delta> \<ominus>\<^sub>H is')(n f\<mapsto>Lam [z]. (e' \<ominus> is'))"
    by (simp add: resolveExp_App resolveExp_Var resolveExp_Lam)
  from second_stack_element_unchanged[OF this] `atom n \<sharp> x` `x \<notin> heapVars is'`
  have "(\<Delta> f! x) \<ominus> is' = App (Var n) (y \<ominus> is)" by (auto simp add: lookup_resolveHeap')
  with `lookup \<Delta> x = Some (App (Var n) y)`
  have [simp]:"y \<ominus> is' = y \<ominus> is" by (simp add: resolveExp_App)

  (*
  from  `atom n \<sharp> x` `atom n \<sharp> S` `atom n \<sharp> is`  `atom n \<sharp> is'`
  have "atom n \<sharp> removeAll x (S \<ominus>\<^sub>S is)" "atom n \<sharp> removeAll x (S \<ominus>\<^sub>S is')"
   by (simp_all add:
        eqvt_fresh_cong2[where f = resolveStack, OF resolveStack_eqvt]
        eqvt_fresh_cong2[where f = removeAll, OF removeAll_eqvt])
  hence "n \<notin> set (removeAll x (S \<ominus>\<^sub>S is))" and "n \<notin> set (removeAll x (S \<ominus>\<^sub>S is'))" by (metis set_not_fresh)+
  hence [simp]: "removeAll n (removeAll x (S \<ominus>\<^sub>S is)) = removeAll x (S \<ominus>\<^sub>S is)"
    by simp

  from  `n # x # S \<ominus>\<^sub>S is' = n # x # S \<ominus>\<^sub>S is`
        `n \<notin> heapVars is'` `n \<notin> heapVars is` `x \<notin> heapVars is'` `x \<notin> heapVars is`
        `atom n \<sharp> x` `n \<notin> set (removeAll x (S \<ominus>\<^sub>S is'))`
  have [simp]: "removeAll x (S \<ominus>\<^sub>S is') = removeAll x (S \<ominus>\<^sub>S is)"
    by simp
  *)
  
  have [simp]: "dropChain is' x S \<ominus>\<^sub>S (z,y) # is' = dropChain is' x S \<ominus>\<^sub>S is'"
    by (metis resolveStack_fresh_noop[OF dropChain_fresh[OF `atom z \<sharp> S`]])

  from  `set ((z, y) # is') \<subseteq> set is''` 
  have "heapVars ((z, y) # is') \<subseteq> heapVars is''" unfolding heapVars_def by (metis image_mono)
  hence "z \<in> heapVars is''" by simp
  with `valid_ind is''`
  have "atom z \<sharp> \<Theta> \<ominus>\<^sub>H is''"
    by (auto intro!: resolveHeap'_fresh)
 
  {
    from is' `x \<notin> fdom \<Gamma>` `x \<notin> heapVars is` `x \<notin> heapVars is'` `n \<notin> heapVars is` `n \<notin> heapVars is'` `atom z \<sharp> is` `atom z \<sharp> is'`  `atom n \<sharp> x` `valid_ind is` `atom n \<sharp> \<Gamma>` `atom n \<sharp> \<Delta>`
    have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> App (Var n) (y \<ominus> is))(n f\<mapsto> e \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>n # x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub>  (\<Delta> \<ominus>\<^sub>H is')(n f\<mapsto>Lam [z]. (e' \<ominus> is'))"
      by (simp add: resolveExp_App resolveExp_Var resolveExp_Lam)
  } moreover {
    from is'' `atom z \<sharp> \<Delta>` `atom z \<sharp> x`  `atom z \<sharp> is'` `x \<notin> heapVars is'` `x \<notin> heapVars is` `valid_ind is`
    have "(\<Delta> \<ominus>\<^sub>H is')(x f\<mapsto> (e' \<ominus> is')[z::=(y \<ominus> is)]) \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Theta> \<ominus>\<^sub>H is''"
      by (simp add: resolve_subst)
  }
  ultimately
  have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> App (e \<ominus> is) (y \<ominus> is)) \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub>x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Theta> \<ominus>\<^sub>H is''"
    apply(rule Application[rotated 3])
    using  `atom n \<sharp> x`  `atom n \<sharp> z`  `atom n \<sharp> is`  `atom n \<sharp> is'`  `atom n \<sharp> is''` `atom n \<sharp> \<Gamma>` 
          `atom n \<sharp> \<Delta>`  `atom n \<sharp> e` `atom n \<sharp> y`  `atom n \<sharp> \<Theta>`  `atom n \<sharp> S`
    using  `atom z \<sharp> x` `atom z \<sharp> is`  `atom z \<sharp> is'`  `atom z \<sharp> \<Gamma>` 
          `atom z \<sharp> \<Delta>` `atom z \<sharp> e` `atom z \<sharp> y` `atom z \<sharp> S`
    using `atom z \<sharp> \<Theta> \<ominus>\<^sub>H is''`
    using `x \<notin> fdom \<Gamma>`
      apply (auto simp add: fresh_Pair fresh_append 
        intro: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
         eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
        eqvt_fresh_cong2[where f = resolveHeap', OF resolveHeap'_eqvt]
        eqvt_fresh_cong2[where f = resolveStack, OF resolveStack_eqvt]
        eqvt_fresh_cong3[where f = dropChain, OF dropChain_eqvt]
        eqvt_fresh_cong2[where f = removeAll, OF removeAll_eqvt]
        resolveHeapOneFresh subst_is_fresh(1))
      done

  with `x \<notin> heapVars is` `valid_ind is`
  have "\<Gamma>(x f\<mapsto> App e y) \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<times>\<^bsub> (x # S) \<ominus>\<^sub>S is\<^esub> \<Theta> \<ominus>\<^sub>H is''"
    by (simp add: resolveExp_App)
  moreover
  note `ind_for is'' _`
  moreover
  note `valid_ind is''`
  moreover
  from `set is \<subseteq> set is'` and `_ \<subseteq> set is''`
  have "set is \<subseteq> set is''" by auto
  moreover

  { fix x'
    assume "x' \<in> heapVars is''"
    hence "x' \<noteq> x" and "x' \<noteq> n" 
      using `x \<notin> heapVars is''` `atom n \<sharp> is''` by (auto dest: heapVars_not_fresh)

    assume "x' \<in> fdom \<Gamma>"
    with reds_doesnt_forget[OF ApplicationInd.hyps(17), simplified] `x' \<noteq> x` `x' \<noteq> n`
    have "x' \<in> fdom \<Delta>" by auto
    moreover
    have "x' \<noteq> z" by (metis `z \<notin> fdom \<Delta>` `x' \<in> fdom \<Delta>`)
    moreover
    note `x' \<in> heapVars is''` hV'
    ultimately
    have "x' \<in> heapVars is'" by auto
    with hV `x' \<in> fdom \<Gamma>`
    have "x' \<in> heapVars is" by auto
  }
  with `x \<notin> heapVars is''`
  have "heapVars is'' \<inter> fdom (\<Gamma>(x f\<mapsto> App e y)) \<subseteq> heapVars is"
    by auto
  moreover
  from `x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S (z, y) # is'`
  have "x # S \<ominus>\<^sub>S is'' = x # S \<ominus>\<^sub>S is" by simp
  ultimately 
  show ?case by auto
next
case (VariableNoBH x \<Gamma> y S \<Delta> "is")
  from `\<Gamma>(x f\<mapsto> Var y) \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>y # x # S\<^esub> \<Delta>`
  have "x \<noteq> y" by (metis var_not_self)

  from result_evaluated[OF `_ \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>_\<^esub> _`]
  have "isLam (\<Delta> f! y)" by simp

  from second_stack_element_unchanged[OF `_ \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>_\<^esub> _`] `x \<noteq> y`
  have "lookup \<Delta> x = Some (Var y)" by simp

  from stack_bound[OF `_ \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>_\<^esub> _`]
  have "y \<in> fdom \<Delta>" by simp

  from VariableNoBH(3)[OF  `ind_for is _` `valid_ind is`]
  obtain is' where is': "\<Gamma>(x f\<mapsto> Var y) \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>y # x # S \<ominus>\<^sub>S is\<^esub> \<Delta> \<ominus>\<^sub>H is'"
    and "ind_for is' \<Delta>"
    and "set is \<subseteq> set is'"
    and "valid_ind is'"
    and hV: "heapVars is' \<inter> fdom (\<Gamma>(x f\<mapsto> Var y)) \<subseteq> heapVars is"
    and "y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is"
    by blast

  show ?case
  proof(cases "x \<in> heapVars is")
  case True
    from True `ind_for is _`
    have "(x,y) \<in> set is" by (auto simp add: ind_for_def heapVars_def)

    from `valid_ind is` `(x, y) \<in> set is`
    have [simp]: "x \<ominus> is = y \<ominus> is"
      by (rule resolve_var_same_image)

    from `(x,y) \<in> set is` `set is \<subseteq> set is'`
    have "(x,y) \<in> set is'" by auto
    with `valid_ind is'`
    have [simp]: "x \<ominus> is' = y \<ominus> is'"
      by (rule resolve_var_same_image)

    from `(x,y) \<in> set is`
    have [simp]: "y # x # S \<ominus>\<^sub>S is = x # S \<ominus>\<^sub>S is" by simp

    from `(x,y) \<in> set is'`
    have [simp]: "y # x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is'" by simp

    from `set is \<subseteq> set is'`
    have "heapVars is \<subseteq> heapVars is'" by (metis heapVars_def image_mono)
    with `x \<in> heapVars is`
    have "x \<in> heapVars is'" by auto

    from is' `x \<in> heapVars is` `x \<in> heapVars is'`
    have "\<Gamma>(x f\<mapsto> Var y) \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> fmap_copy \<Delta> y x \<ominus>\<^sub>H is'" by simp
    moreover

    from `lookup \<Delta> x = Some (Var y)` `y \<in> fdom \<Delta>` result_evaluated[OF `_ \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>_\<^esub> _`, simplified]   `ind_for is' _`
    have "ind_for is' (fmap_copy \<Delta> y x)"
      by (rule ind_for_copy) 
    moreover
    note `set is \<subseteq> set is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> fdom (\<Gamma>(x f\<mapsto> Var y)) \<subseteq> heapVars is" by auto
    moreover
    from `y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is`
    have "x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is" by simp
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

    from is'  `x \<notin> heapVars is` `x \<notin> heapVars is'` `valid_ind is`
    have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> Var (y \<ominus> is)) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>(y \<ominus> is) # x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Delta> \<ominus>\<^sub>H is'"
      by (simp add: resolveExp_Var)
    hence "y \<ominus> is \<noteq> x" by (metis var_not_self)

    have [simp]: "fmap_copy \<Delta> y x \<ominus>\<^sub>H is' = fmap_copy (\<Delta> \<ominus>\<^sub>H is') (y \<ominus> is') x"
      using `valid_ind is'` `isLam (\<Delta> f! y)` `ind_for is' \<Delta>` `x \<notin> heapVars is'`
      by (rule resolveHeap_fmap_copy)

    from is' `x \<notin> heapVars is` `x \<notin> heapVars is'` `valid_ind is`
    have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> Var (y \<ominus> is)) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>(y \<ominus> is) # x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Delta> \<ominus>\<^sub>H is'"
      by (simp add: resolveExp_Var)
    from second_stack_element_unchanged[OF this] `y \<ominus> is \<noteq> x` `x \<notin> heapVars is'`
    have "(\<Delta> f! x) \<ominus> is' = Var (y \<ominus> is)" by (auto simp add: lookup_resolveHeap')
    with  `lookup \<Delta> x = Some (Var y)`
    have [simp]:"y \<ominus> is' = y \<ominus> is" by (simp add: resolveExp_Var)
  
    have "x \<notin> fdom (\<Gamma> \<ominus>\<^sub>H is)" using `x \<notin> fdom \<Gamma>` by simp
    moreover
    from is'  `x \<notin> heapVars is` `x \<notin> heapVars is'` `valid_ind is`
    have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> Var (y \<ominus> is)) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>(y \<ominus> is) # x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> \<Delta> \<ominus>\<^sub>H is'"
      by (simp add: resolveExp_Var)
    ultimately
    have "(\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> Var (y \<ominus> is)) \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # (dropChain is x S \<ominus>\<^sub>S is)\<^esub> fmap_copy (\<Delta> \<ominus>\<^sub>H is') (y \<ominus> is) x"
      by (rule reds.VariableNoBH)
    hence "\<Gamma>(x f\<mapsto> Var y) \<ominus>\<^sub>H is \<Down>\<^sup>\<times>\<^sup>\<surd>\<^sup>\<times>\<^bsub>x # S \<ominus>\<^sub>S is\<^esub> fmap_copy \<Delta> y x \<ominus>\<^sub>H is'"
      using  `x \<notin> heapVars is`  `x \<notin> heapVars is'` `valid_ind is`
      by (simp add: resolveExp_Var)
    moreover

    from `lookup \<Delta> x = Some (Var y)` `y \<in> fdom \<Delta>` result_evaluated[OF `_ \<Down>\<^sup>\<surd>\<^sup>\<surd>\<^sup>\<times>\<^bsub>_\<^esub> _`, simplified]   `ind_for is' _`
    have "ind_for is' (fmap_copy \<Delta> y x)"
      by (rule ind_for_copy) 
    moreover
    note `set is \<subseteq> set is'` `valid_ind is'`
    moreover
    from hV
    have "heapVars is' \<inter> fdom (\<Gamma>(x f\<mapsto> Var y)) \<subseteq> heapVars is" by auto
    moreover
    from `y # x # S \<ominus>\<^sub>S is' = y # x # S \<ominus>\<^sub>S is`
         `valid_ind is` `valid_ind is'`
         `x \<notin> heapVars is` `x \<notin> heapVars is'`       
    have "x # S \<ominus>\<^sub>S is' = x # S \<ominus>\<^sub>S is"
      by auto
    (*
    moreover
    from `x \<notin> heapVars is'`
    have "fst (hd ((x, z) # \<Delta>')) \<notin> heapVars is'" by simp
    *)
    ultimately
    show ?thesis by blast
  qed
next
case (Let as \<Gamma> x S body u \<Delta> "is")
  show ?case sorry
qed

end
