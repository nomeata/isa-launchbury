theory Indirections
imports Terms "Nominal-Utils" "AList-Utils-Nominal" "FMap-Heap" "FMap-Nominal"
begin


type_synonym indirections = "(var \<times> var) list "

class resolvable =
  fixes resolve :: "'a \<Rightarrow> indirections \<Rightarrow> 'a" (infixl "\<ominus>" 60)
  assumes resolve_append[simp]: "x \<ominus> (is'@is) = x \<ominus> is' \<ominus> is"
  assumes resolve_Nil[simp]: "x \<ominus> [] = x"

class resolvable_eqvt = resolvable + pt + 
  assumes resolve_eqvt: "p \<bullet> (x \<ominus> is) = (p \<bullet> x) \<ominus> (p \<bullet> is)"
  assumes resolve_fresh_noop[simp]: "atom a \<sharp> x \<Longrightarrow> x \<ominus> ((a, b) # is) = x \<ominus> is"

declare resolve_eqvt[eqvt]

instantiation list :: (resolvable) resolvable 
begin
  definition resolve_list :: "'a list \<Rightarrow> indirections \<Rightarrow> 'a list"
  where "m \<ominus> is = map (\<lambda>x. x \<ominus> is) m"

  lemma resolve_list_Nil[simp]: "[] \<ominus> is = []"
    unfolding resolve_list_def by simp
  
  lemma resolve_list_Cons[simp]: "(x # xs) \<ominus> is = (x \<ominus> is) # (xs \<ominus> is)"
    unfolding resolve_list_def by simp
instance
  apply default
  apply (induct_tac "x", auto)
  apply (simp add: resolve_list_def)
  done
end

instance list :: (resolvable_eqvt) resolvable_eqvt
  apply default
  apply (simp add: resolve_list_def)
  apply (simp add: resolve_list_def fresh_list_elem)
  done

instantiation var :: resolvable_eqvt
begin
  fun resolve_var :: "var \<Rightarrow> indirections \<Rightarrow> var"  where
    "v \<ominus> [] = (v::var)"
    | "v \<ominus> ((x,y)#is) = v[x ::v= y] \<ominus> is"

  lemma resolve_var_append: "(v::var) \<ominus> (is'@is) = v \<ominus> is' \<ominus> is"
    by (induct "is'" arbitrary: v) auto
instance
  apply default
  apply (rule resolve_var_append)
  apply (simp)
  apply (induct_tac x "is" rule:resolve_var.induct, simp+)
  done
end

lemma resove_var_noop[simp]: "x \<notin> heapVars is \<Longrightarrow> x \<ominus> is = x"
  by (induct x "is" rule: resolve_var.induct) auto

instantiation exp :: resolvable_eqvt
begin
  fun resolve_exp :: "exp \<Rightarrow> indirections \<Rightarrow> exp" where
    "e \<ominus> [] = (e::exp)"
    | "e \<ominus> ((x,y)#is) = (e[x ::= y]) \<ominus> is"

  lemma resolve_exp_append: "(e::exp) \<ominus> (is'@is) = e \<ominus> is' \<ominus> is"
    by (induct "is'" arbitrary: e) auto

  lemma resolve_exp_eqvt[eqvt]: "p \<bullet> ((e::exp) \<ominus> is) = (p \<bullet> e) \<ominus> (p \<bullet> is)"
    by (induction e "is" rule:resolve_exp.induct) simp+

instance 
  apply default
  apply (rule resolve_exp_append)
  apply simp
  apply (rule resolve_exp_eqvt)
  apply (simp add: subst_fresh_noop)
  done
end

instantiation assn :: resolvable_eqvt
begin
  fun resolve_assn :: "assn \<Rightarrow> indirections \<Rightarrow> assn" where
    "as \<ominus> [] = (as::assn)"
    | "as \<ominus> ((x,y)#is) = (as[x ::a= y]) \<ominus> is"

  lemma resolve_assn_append: "(as::assn) \<ominus> (is'@is) = as\<ominus> is' \<ominus> is"
    by (induct "is'" arbitrary: as) auto

  lemma resolve_assn_eqvt[eqvt]: "p \<bullet> ((as::assn) \<ominus> is) = (p \<bullet> as) \<ominus> (p \<bullet> is)"
    by (induction as "is" rule:resolve_assn.induct) simp+

instance
  apply default
  apply (rule resolve_assn_append)
  apply simp
  apply (rule resolve_assn_eqvt)
  apply (simp add: subst_assn_fresh_noop)
  done
end

lemma resolve_var_fresh: "atom ` heapVars is \<sharp>* v \<Longrightarrow> (v::var) \<ominus> is = v"
  by (induct "is" rule:resolve_var.induct)(auto simp add: fresh_star_def fresh_def )

lemma resolve_var_fresh'[simp]: "atom v \<sharp> is \<Longrightarrow> (v::var) \<ominus> is = v"
  by (induct "is" rule:resolve_var.induct)(auto simp add: fresh_Cons fresh_Pair)

lemma resolve_var_list_fresh: "atom ` heapVars is \<sharp>* L \<Longrightarrow> (L::var list) \<ominus> is = L"
  by (induct L) (auto simp add: fresh_star_list resolve_var_fresh)


lemma resolveExp_Lam: "atom x \<sharp> is \<Longrightarrow> (Lam [x]. e) \<ominus> is = Lam [x]. (e \<ominus> is)"
  apply (induction "is" arbitrary: e)
  apply simp
  apply (auto simp add: fresh_Cons)
  done

lemma resolveExp_App: "App e x \<ominus> is = App (e \<ominus> is) (x \<ominus> is)"
  by (induction "is" arbitrary: e x) auto

lemma resolveExp_Var: "Var x \<ominus> is = Var (x \<ominus> is)"
  by (induction "is" arbitrary: x) auto

lemma resolveExp_Let: "set (bn as) \<sharp>* is \<Longrightarrow> (Let as e) \<ominus> is = Let (as \<ominus> is) (e \<ominus> is)"
  by (induction "is" arbitrary: as e) (auto simp add: fresh_star_list)

lemma resolve_assn_ANil[simp]: "ANil \<ominus> is = ANil"
  by (induction "is") auto

lemma resolve_assn_ACons[simp]: "x \<notin> heapVars is \<Longrightarrow> (ACons x e as) \<ominus> is = (ACons (x \<ominus> is) (e \<ominus> is) (as \<ominus> is))"
  by (induction "is" arbitrary: x e as) auto

definition resolveHeap' :: "Heap \<Rightarrow> indirections \<Rightarrow> Heap"  (infixl "\<ominus>\<^sub>H" 60) where
  "\<Gamma> \<ominus>\<^sub>H is = fmap_map (\<lambda>e. e \<ominus> is) (\<Gamma> f|` (- heapVars is))"

lemma resolveHeap'_empty[simp]: "f\<emptyset> \<ominus>\<^sub>H is = f\<emptyset>"
  unfolding resolveHeap'_def by auto

lemma resolveHeap'_Nil[simp]: "\<Gamma> \<ominus>\<^sub>H [] = \<Gamma>"
  unfolding resolveHeap'_def by auto

lemma resolveHeap'fdom[simp]:
  "fdom (\<Gamma> \<ominus>\<^sub>H is) = fdom \<Gamma> - heapVars is"
  unfolding resolveHeap'_def by auto

lemma resolveHeap'_fmap_upd[simp]: "x \<in> heapVars is \<Longrightarrow> (\<Gamma>(x f\<mapsto> e)) \<ominus>\<^sub>H is = \<Gamma> \<ominus>\<^sub>H is"
  unfolding resolveHeap'_def by auto

lemma resolveHeap'_fmap_upd_other[simp]: "x \<notin> heapVars is \<Longrightarrow> (\<Gamma>(x f\<mapsto> e)) \<ominus>\<^sub>H is = (\<Gamma> \<ominus>\<^sub>H is)(x f\<mapsto> e \<ominus> is)"
  unfolding resolveHeap'_def by simp

lemma resolveHeap'_fun_merge[simp]: "fdom \<Delta> \<inter> heapVars is = {} \<Longrightarrow> (\<Gamma> f++ \<Delta>) \<ominus>\<^sub>H is = (\<Gamma> \<ominus>\<^sub>H is) f++ (\<Delta> \<ominus>\<^sub>H is)"
  by (induction \<Delta> rule:fmap_induct) (auto simp add: fun_merge_upd)

lemma resolveHeap'_fmap_copy[simp]: "x \<in> heapVars is \<Longrightarrow> (fmap_copy \<Gamma> y x) \<ominus>\<^sub>H is = \<Gamma> \<ominus>\<^sub>H is"
  unfolding resolveHeap'_def by simp

lemma resolveHeap'_fmap_copy_other[simp]: "x \<notin> heapVars is \<Longrightarrow> y \<notin> heapVars is \<Longrightarrow> (fmap_copy \<Gamma> y x) \<ominus>\<^sub>H is = fmap_copy (\<Gamma> \<ominus>\<^sub>H is) y x"
  unfolding resolveHeap'_def by auto

lemma resolveHeap'_fresh_Cons[simp]: "atom y \<sharp> \<Gamma> \<Longrightarrow> \<Gamma> \<ominus>\<^sub>H (y,x)#is = \<Gamma> \<ominus>\<^sub>H is"
  unfolding resolveHeap'_def
  by (rule fmap_map_cong[OF resolve_fresh_noop])
     (auto dest: set_mp[OF fran_fmap_restr_subset] intro: fmap_restr_cong simp add: fresh_def supp_fmap supp_set_elem_finite)

lemma resolveHeap'_eqvt[eqvt]: "p \<bullet> resolveHeap' \<Gamma> is = resolveHeap' (p \<bullet> \<Gamma>) (p \<bullet> is)"
  unfolding resolveHeap'_def
  by (simp add: fmap_restr_eqvt Compl_eqvt)

fun resolveHeapOne :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> heap"  where
  "resolveHeapOne [] _ _ = []"
 | "resolveHeapOne ((x,e)#\<Gamma>) a b = (if a = x then (resolveHeapOne \<Gamma> a b) else (x, e[a ::= b]) # (resolveHeapOne \<Gamma> a b))"

lemma resolveHeapOneFresh: "atom y \<sharp> x \<Longrightarrow> atom y \<sharp> resolveHeapOne \<Gamma> y x"
  by (induction \<Gamma> y x rule:resolveHeapOne.induct)
     (auto simp add: fresh_Nil fresh_Cons fresh_Pair)

lemma resolveHeapOne_eqvt[eqvt]: "p \<bullet> resolveHeapOne \<Gamma> a b = resolveHeapOne (p \<bullet> \<Gamma>) (p \<bullet> a) (p \<bullet> b)"
  by (induction \<Gamma> a b rule:resolveHeapOne.induct) simp_all

lemma resolveHeapOneNoop[simp]: "atom y \<sharp> \<Gamma> \<Longrightarrow> resolveHeapOne \<Gamma> y x = \<Gamma>"
  by (induction \<Gamma> y x rule:resolveHeapOne.induct)
     (auto simp add: fresh_Nil fresh_Cons fresh_Pair subst_fresh_noop)

fun resolveHeap :: "heap \<Rightarrow> indirections \<Rightarrow> heap" (infixl "\<ominus>\<^sub>h" 60) where
  "\<Gamma> \<ominus>\<^sub>h [] = \<Gamma>"
 | "\<Gamma> \<ominus>\<^sub>h ((a,b)#is) = resolveHeapOne \<Gamma> a b \<ominus>\<^sub>h is"
  
lemma resolveHeapNil[simp]: "[] \<ominus>\<^sub>h is = []"
  by (induct "[]::heap" "is" rule:resolveHeap.induct) simp_all

lemma resolveHeapConsRemoved[simp]: "x \<in> heapVars is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = \<Gamma> \<ominus>\<^sub>h is"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  apply (erule disjE)
  apply auto
  done

lemma resolveHeapCons[simp]: "x \<notin> heapVars is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = (x, e \<ominus> is) # (\<Gamma> \<ominus>\<^sub>h is)"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  done

lemma resolveHeapConsRemoved'[simp]: "x \<in> heapVars is \<Longrightarrow> (y,z)#(x,e)#\<Gamma> \<ominus>\<^sub>h is = ((y,z)#\<Gamma>) \<ominus>\<^sub>h is"
  apply (cases "y \<in> heapVars is")
  apply simp_all
  done

lemma resolveHeapOneDelete[simp]: "resolveHeapOne (delete x \<Gamma>) a b = delete x (resolveHeapOne \<Gamma> a b)"
  by (induct \<Gamma> a b rule:resolveHeapOne.induct) auto

lemma resolveHeapDelete[simp]: "delete x \<Gamma> \<ominus>\<^sub>h is = delete x (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct \<Gamma> "is" arbitrary: x rule:resolveHeap.induct) simp_all

lemma resolveHeapOneHeapVars[simp]:
  "heapVars (resolveHeapOne \<Gamma> a b) = heapVars \<Gamma> - {a}"
  by (induct \<Gamma> a b rule:resolveHeapOne.induct) auto

lemma resolveHeapHeapVars[simp]:
  "heapVars (\<Gamma> \<ominus>\<^sub>h is) = heapVars \<Gamma> - heapVars is"
  by (induct \<Gamma> "is" rule:resolveHeap.induct) auto

lemma resolveHeapOneDeleted[simp]:
  "delete a (resolveHeapOne \<Gamma> a b \<ominus>\<^sub>h is) = resolveHeapOne \<Gamma> a b \<ominus>\<^sub>h is"
  by (rule delete_no_there, simp)

lemma resolveHeapDeleted[simp]: "x \<in> heapVars is \<Longrightarrow> delete x (\<Gamma> \<ominus>\<^sub>h is) = \<Gamma> \<ominus>\<^sub>h is"
  by (rule delete_no_there, simp)

lemma resolveHeap_eqvt[eqvt]: "p \<bullet> resolveHeap \<Gamma> is = resolveHeap (p \<bullet> \<Gamma>) (p \<bullet> is)"
  by(induction \<Gamma> "is" rule:resolveHeap.induct) simp_all

lemma resolveHeap_append[simp]: "\<Gamma> \<ominus>\<^sub>h (is'@is) = \<Gamma> \<ominus>\<^sub>h is' \<ominus>\<^sub>h is"
  apply (induct \<Gamma> "is'" rule:resolveHeap.induct)
  apply (auto)
  done

lemma resolveHeapOne_set: "(y, e) \<in> set \<Gamma> \<Longrightarrow> y \<noteq> a \<Longrightarrow> (y, e[a ::= b]) \<in> set (resolveHeapOne \<Gamma> a b)"
  by (induct \<Gamma> a b rule:resolveHeapOne.induct) auto

lemma resolveHeap_set: "(y, e) \<in> set \<Gamma> \<Longrightarrow> y \<notin> heapVars is \<Longrightarrow> (y, e \<ominus> is) \<in> set (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct \<Gamma> "is" arbitrary: e rule:resolveHeap.induct) (auto dest: resolveHeapOne_set)

definition indirection_related :: "heap \<Rightarrow> exp \<Rightarrow> indirections \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" where
  "indirection_related \<Gamma> e is \<Gamma>' e' = (resolveHeap \<Gamma> is = \<Gamma>' \<and>  e \<ominus> is = e')"

lemma subst_subst: "a \<noteq> y \<Longrightarrow> b \<noteq> y \<Longrightarrow> e[y ::= x][a ::= b] = (e[a ::= b])[y ::= x[a ::v= b]]"
    and  "a \<noteq> y \<Longrightarrow> b \<noteq> y \<Longrightarrow> as[y ::a= x][a ::a= b] = (as[a ::a= b])[y ::a= x[a ::v= b]]"
  apply (nominal_induct e and as avoiding: x y a b  rule:exp_assn.strong_induct)
  apply (auto simp add: fresh_star_Pair)
  done

lemma resolve_subst: "atom y \<sharp> is \<Longrightarrow> e[y ::= x] \<ominus> is = (e \<ominus> is)[y ::= (x \<ominus> is)]"
proof (induct e "is" arbitrary: x y rule: resolve_exp.induct)
case goal1 thus ?case by simp
next
case (goal2 e a b "is" x y)
  from goal2(2)
  have ab_ne_y: "a \<noteq> y" "b \<noteq> y" and  "atom y \<sharp> is" 
   by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)

  have "e[y::=x] \<ominus> (a, b) # is = e[y::=x][a ::= b] \<ominus> is" by simp
  also
  have "\<dots> = e[a ::= b][y ::=x[a ::v= b]] \<ominus> is"
    by (rule arg_cong[OF subst_subst[OF ab_ne_y]])
  also
  have "\<dots> = (e[a ::= b] \<ominus> is)[y ::= (x[a ::v= b]  \<ominus> is)]"
    by (rule goal2(1)[OF `atom y \<sharp> is`])
  also
  have "\<dots> = (e \<ominus> (a, b) # is)[y ::= (x \<ominus> (a, b) # is)]"
    by simp
  finally show ?case.
qed

lemma
  flip_subst: "atom y' \<sharp> (e,x) \<Longrightarrow> ((y \<leftrightarrow> y') \<bullet> e)[y' ::=x ] = e[y ::= x]"
    and  "atom y \<notin> set (bn as) \<Longrightarrow> atom y' \<sharp> (as,x) \<Longrightarrow> ((y \<leftrightarrow> y') \<bullet> as)[y' ::a=x ] = as[y ::a= x]"
proof (nominal_induct e and as avoiding: y y' x rule:exp_assn.strong_induct)
case (Let as exp y y' x)
  have "atom y \<notin> set (bn as)"
    using Let(1) by (auto simp add: fresh_star_def)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> bn as = bn as"
    apply -
    apply (rule flip_fresh_fresh)
    using calculation apply (simp add: fresh_def supp_of_atom_list)
    using  Let.hyps(2) apply (metis fresh_def fresh_star_def not_self_fresh supp_of_atom_list)
    done
  moreover note Let
  ultimately
  show ?case
    by (auto simp add: fresh_Pair fresh_star_Pair fresh_star_def simp del: exp_assn.eq_iff)
next
qed (auto simp add: fresh_Pair fresh_star_Pair exp_assn.bn_defs  flip_fresh_fresh simp del: exp_assn.eq_iff)

lemma supp_atom_set: "supp L = atom ` set L"
  apply (induct L)
  apply (simp add: supp_Nil)
  apply (clarsimp simp add: supp_Nil supp_Cons supp_at_base)
  done

inductive valid_ind :: "indirections \<Rightarrow> bool" where
  ValidIndNil[simp]: "valid_ind []" |
  ValidIndCons: "valid_ind is \<Longrightarrow> atom x \<sharp> (is,y) \<Longrightarrow> valid_ind ((x,y) # is)"

lemma heapVarFresh: "x \<in> heapVars is \<Longrightarrow> atom x \<sharp> ((v::var) \<ominus> is)" oops

lemma resolveHeap_fresh:  "valid_ind is \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> atom x \<sharp> (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct arbitrary: \<Gamma> rule:valid_ind.induct)
     (auto simp add: fresh_Pair resolveHeapOneFresh eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt])

lemma resolve_expr_fresh:
  assumes "valid_ind is"
  assumes "x \<in> heapVars is"
  shows "atom x \<sharp> ((e :: exp) \<ominus> is)"
using assms
  by (induct arbitrary: e rule:valid_ind.induct)
     (auto simp add: fresh_Pair eqvt_fresh_cong2[where f = resolve, OF resolve_eqvt])

lemma resolveHeap'_fresh:
  assumes "valid_ind is"
  assumes "x \<in> heapVars is"
  shows "atom x \<sharp> (\<Gamma> \<ominus>\<^sub>H is)"
proof (induction \<Gamma> rule:fmap_induct)
  case empty show ?case by auto
next
  case (update \<Gamma> x' v)
  show ?case
  proof(cases "x' \<in> heapVars is")
    case True with update assms
    show ?thesis by auto
  next
    case False
    moreover
    hence "x \<noteq> x'" using assms(2) by auto
    ultimately
    show ?thesis
    using update assms
    by (auto simp add: resolve_expr_fresh eqvt_fresh_cong3[where f = fmap_upd, OF fmap_upd_eqvt])
  qed
qed

lemma resolveHeapOne_distinctVars: "distinctVars \<Gamma> \<Longrightarrow> distinctVars (resolveHeapOne \<Gamma> a b)"
  by (induct \<Gamma> a b rule:resolveHeapOne.induct) (auto simp add: distinctVars_Cons)

lemma resolveHeap_distinctVars[simp]: "distinctVars \<Gamma> \<Longrightarrow> distinctVars (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct \<Gamma> "is" rule:resolveHeap.induct) (auto simp add: resolveHeapOne_distinctVars)

lemma resolve_var_same_image[dest]: "valid_ind is \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> x \<ominus> is = y \<ominus> is"
  apply (induct  "is" rule: valid_ind.induct)
  apply (auto simp add: fresh_Pair)
  apply (metis fresh_Pair fresh_list_elem not_self_fresh)
  by (metis fresh_Pair fresh_list_elem not_self_fresh)


lemma valid_ind_smaller_index:
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

lemma valid_ind_induct[consumes 1, case_names NoInd Ind, induct pred: valid_ind]:
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
      have "i < j" by (rule valid_ind_smaller_index)
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


lemma valid_ind_different: "valid_ind is \<Longrightarrow> (x,y) \<in> set is \<Longrightarrow> x \<noteq> y"
  by (induct  "is" rule: valid_ind.induct) (auto simp add: fresh_Pair)

lemma valid_ind_in_is: "valid_ind is \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> x \<ominus> is \<in> snd `set is"
  apply (induct x rule: valid_ind_induct)
  apply auto
  apply (case_tac "y \<in> heapVars is")
  apply (auto simp add: resolve_var_same_image intro: imageI)
  by (metis image_iff snd_conv)

lemma resolve_var_fresh_self: "valid_ind is \<Longrightarrow> atom (y \<ominus> is) \<sharp> is \<Longrightarrow> y \<notin> heapVars is"
  apply (auto dest!: valid_ind_in_is)
  by (metis fresh_Pair fresh_list_elem not_self_fresh)

lemma resolve_var_modifies: "valid_ind is \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> x \<noteq> x \<ominus> is" 
  by (induction "is" rule: valid_ind.induct)
     (auto simp add: fresh_Pair dest: resolve_var_fresh_self)

lemma resolve_resolved: "valid_ind is \<Longrightarrow> x \<ominus> is \<notin> heapVars is"
  by (induct x rule:valid_ind_induct) (simp_all add: resolve_var_same_image)

lemma valid_ind_idemp[simp]: "valid_ind is \<Longrightarrow> (y::var) \<ominus> is \<ominus> is = y \<ominus> is"
   by (intro resove_var_noop resolve_resolved)


end
