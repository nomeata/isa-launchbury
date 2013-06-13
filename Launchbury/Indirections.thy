theory Indirections
imports Terms "Nominal-Utils" DistinctVars
begin

type_synonym indirections = "(var \<times> var) list "

class resolvable =
  fixes resolve :: "'a \<Rightarrow> indirections \<Rightarrow> 'a" (infixl "\<ominus>" 60)
  assumes resolve_append[simp]: "x \<ominus> (is'@is) = x \<ominus> is' \<ominus> is"

class resolvable_eqvt = resolvable + pt + 
  assumes resolve_eqvt: "p \<bullet> (x \<ominus> is) = (p \<bullet> x) \<ominus> (p \<bullet> is)"

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
  by (induct_tac "x")auto
end

instance list :: (resolvable_eqvt) resolvable_eqvt
  by default (simp_all add: resolve_list_def)

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
  apply (rule resolve_exp_eqvt)
  done
end

lemma resolve_var_fresh: "atom ` heapVars is \<sharp>* v \<Longrightarrow> (v::var) \<ominus> is = v"
  by (induct "is" rule:resolve_var.induct)(auto simp add: fresh_star_def fresh_def )

lemma resolve_var_list_fresh: "atom ` heapVars is \<sharp>* L \<Longrightarrow> (L::var list) \<ominus> is = L"
  by (induct L) (auto simp add: fresh_star_Cons resolve_var_fresh)


lemma resolveExp_Lam: "atom x \<sharp> is \<Longrightarrow> (Lam [x]. e) \<ominus> is = Lam [x]. (e \<ominus> is)"
  apply (induction "is" arbitrary: e)
  apply simp
  apply (auto simp add: fresh_Cons)
  done

lemma resolveExp_App: "App e x \<ominus> is = App (e \<ominus> is) (x \<ominus> is)"
  by (induction "is" arbitrary: e x) auto

lemma resolveExp_Var: "Var x \<ominus> is = Var (x \<ominus> is)"
  by (induction "is" arbitrary: x) auto

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

lemma resolveHeapOneDelete[simp]: "resolveHeapOne (delete x \<Gamma>) a b = delete x (resolveHeapOne \<Gamma> a b)"
  by (induct \<Gamma> a b rule:resolveHeapOne.induct) auto

lemma resolveHeapDelete[simp]: "delete x \<Gamma> \<ominus>\<^sub>h is = delete x (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct \<Gamma> "is" arbitrary: x rule:resolveHeap.induct) simp_all

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

lemma change_Lam_Variable:
  assumes "atom y' \<sharp> e'" and "atom y' \<sharp> y"
  shows   "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')"
proof-
  from assms
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y]. e'"
    by -(rule flip_fresh_fresh, (simp add: fresh_Pair)+)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')"
    by simp
  ultimately
  show "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')" by simp
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
  ValidIndNil: "valid_ind []" |
  ValidIndCons: "valid_ind is \<Longrightarrow> atom x \<sharp> (is,y) \<Longrightarrow> valid_ind ((x,y) # is)"

lemma heapVarFresh: "x \<in> heapVars is \<Longrightarrow> atom x \<sharp> ((v::var) \<ominus> is)" oops

lemma resolveHeap_fresh:  "valid_ind is \<Longrightarrow> x \<in> heapVars is \<Longrightarrow> atom x \<sharp> (\<Gamma> \<ominus>\<^sub>h is)"
  by (induct arbitrary: \<Gamma> rule:valid_ind.induct)
     (auto simp add: fresh_Pair resolveHeapOneFresh eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt])
end
