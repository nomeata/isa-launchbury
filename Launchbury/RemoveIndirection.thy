theory RemoveIndirection
imports LaunchburyCombined "Nominal-Utils" 
begin

type_synonym indirections = "(var \<times> var) list "

inductive IndirectionList :: "indirections \<Rightarrow> bool" where
  NilIndirection: "IndirectionList []"
  | ConsIndirection: "IndirectionList is \<Longrightarrow> atom i \<sharp> is \<Longrightarrow> IndirectionList ((i,x) # is)"

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

lemma subst_fresh_noop: "atom x \<sharp> e \<Longrightarrow> e[x ::= y] = e"
  and "atom x \<sharp> as \<Longrightarrow> as[x ::a= y] = as"
apply (nominal_induct  e and as avoiding: x y rule:exp_assn.strong_induct)
apply (auto simp add: fresh_Pair fresh_star_Pair simp del: exp_assn.eq_iff)
by (metis fresh_star_def not_self_fresh)

lemma resolve_var_fresh: "atom ` fst ` set is \<sharp>* v \<Longrightarrow> (v::var) \<ominus> is = v"
  by (induct "is" rule:resolve_var.induct)(auto simp add: fresh_star_def fresh_def )

lemma resolve_var_list_fresh: "atom ` fst ` set is \<sharp>* L \<Longrightarrow> (L::var list) \<ominus> is = L"
  by (induct L) (auto simp add: fresh_star_Cons resolve_var_fresh)


lemma resolveExp_Lam: "atom x \<sharp> is \<Longrightarrow> (Lam [x]. e) \<ominus> is = Lam [x]. (e \<ominus> is)"
  apply (induction "is" arbitrary: e)
  apply simp
  apply (auto simp add: fresh_Cons)
  done

lemma resolveExp_App: "App e x \<ominus> is = App (e \<ominus> is) (x \<ominus> is)"
  apply (induction "is" arbitrary: e x)
  apply simp
  apply auto
  done

fun resolveHeapOne :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> heap"  where
  "resolveHeapOne [] _ _ = []"
 | "resolveHeapOne ((x,e)#\<Gamma>) a b = (if a = x then (resolveHeapOne \<Gamma> a b) else (x, e[a ::= b]) # (resolveHeapOne \<Gamma> a b))"


lemma resolveHeapOneFresh: "atom y \<sharp> resolveHeapOne \<Gamma> y x"
  sorry

fun resolveHeap :: "heap \<Rightarrow> indirections \<Rightarrow> heap" (infixl "\<ominus>\<^sub>h" 60) where
  "\<Gamma> \<ominus>\<^sub>h [] = \<Gamma>"
 | "\<Gamma> \<ominus>\<^sub>h ((a,b)#is) = resolveHeapOne \<Gamma> a b \<ominus>\<^sub>h is"
  
lemma resolveHeapNil[simp]: "[] \<ominus>\<^sub>h is = []"
  by (induct "[]::heap" "is" rule:resolveHeap.induct) simp_all

lemma resolveHeapConsRemoved[simp]: "x \<in> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = \<Gamma> \<ominus>\<^sub>h is"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  apply (erule disjE)
  apply auto
  done

lemma resolveHeapCons[simp]: "x \<notin> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = (x, e \<ominus> is) # (\<Gamma> \<ominus>\<^sub>h is)"
  apply (induct "(x,e)#\<Gamma>" "is" arbitrary: x e \<Gamma> rule:resolveHeap.induct)
  apply simp_all
  done

lemma resolveHeap_eqvt[eqvt]: "p \<bullet> resolveHeap \<Gamma> is = resolveHeap (p \<bullet> \<Gamma>) (p \<bullet> is)"
sorry
(*
proof (induction \<Gamma> "is" rule:resolveHeap.induct)
  case goal1 thus ?case by simp
next
  case (goal2 x "is" e \<Gamma>)
  hence "p \<bullet> x \<in> fst ` set (p \<bullet> is)" by (metis delete_eqvt delete_id delete_notin_dom permute_eq_iff)
  with goal2
  show ?case by simp
next
  case (goal3 x "is" e \<Gamma>)
  hence "p \<bullet> x \<notin> fst ` set (p \<bullet> is)" by (metis delete_eqvt delete_id delete_notin_dom)
  with goal3
  show ?case by simp
qed
*)

lemma resolveHeap_append[simp]: "\<Gamma> \<ominus>\<^sub>h (is'@is) = \<Gamma> \<ominus>\<^sub>h is' \<ominus>\<^sub>h is"
  apply (induct \<Gamma> "is'" rule:resolveHeap.induct)
  apply (auto)
  done

definition indirection_related :: "heap \<Rightarrow> exp \<Rightarrow> indirections \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool" where
  "indirection_related \<Gamma> e is \<Gamma>' e' = (resolveHeap \<Gamma> is = \<Gamma>' \<and>  e \<ominus> is = e')"

find_theorems "?x(?b \<leftrightarrow> ?c)(?d \<leftrightarrow> ?e)"

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

theorem
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> (* supp is \<subseteq> supp \<Gamma> \<union> supp L \<Longrightarrow> *)
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : z \<ominus> (is'@is))
       \<and> atom ` (fst ` set is') \<sharp>* L" 
proof (nominal_induct \<Gamma> e i u L \<Delta> z avoiding: "is"  rule:reds.strong_induct )
case (Lambda x \<Gamma> L e i u "is")[simp]
  have "resolveHeap \<Gamma> is : Lam [x]. (e \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u \<^bsub>L \<ominus> is\<^esub>  \<Gamma> \<ominus>\<^sub>h is : Lam [x]. (e \<ominus> is)"
    by (rule LambdaI)
  then
  show ?case
    apply -
    apply(rule exI[where x = "[]"])
    apply (simp add: resolveExp_Lam supp_set_empty fresh_star_def)
    done
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z u e' "is")
  from Application(10)
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x # L) \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : (Lam [y]. e') \<ominus> (is'@is)"
      and "atom ` fst ` set is' \<sharp>* (x # L)" by auto

  from this(2)
  have "atom ` fst ` set is' \<sharp>* x" and "atom ` fst ` set is' \<sharp>*  L"
    by (simp_all add: fresh_star_Pair fresh_star_Cons)

  from Application(12)
  obtain "is''"
  where is'':"\<Delta> \<ominus>\<^sub>h is'@is : (e'[y::=x]) \<ominus> is'@is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is'@is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)"
          and "atom ` fst ` set is'' \<sharp>* L" by blast

  from `atom \` fst \` set is' \<sharp>* x`
  have [simp]: "x \<ominus> is' = x"
    by (rule resolve_var_fresh)
  from `atom \` fst \` set is' \<sharp>* L`
  have [simp]: "L \<ominus> is' = L"
    by (rule resolve_var_list_fresh)

  (* Because is' is introduced later the strong induction does not provide us
     with @{term "atom y \<sharp> is'"}, so we need to shuffle variables around. *)
  obtain y' :: var where "atom y' \<sharp> (y, is, is', is'', e', e, \<Gamma>, x, \<Delta>, \<Theta>, z, L)" by (rule obtain_fresh)
  hence "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y]. e'"
    by -(rule  flip_fresh_fresh, (simp add: fresh_Pair)+)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e') = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')"
    by simp
  ultimately
  have "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')" by simp
  with is' `atom y' \<sharp> _` `atom y \<sharp> e` 
  have "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is'@is)# (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y']. (((y \<leftrightarrow> y') \<bullet> e') \<ominus> (is'@is))"
    by (simp add: fresh_Pair flip_fresh_fresh resolveExp_Lam fresh_append resolve_var_append del: exp_assn.eq_iff)
  moreover
  { note is''
    also
    have "e'[y::=x] = ((y \<leftrightarrow> y') \<bullet> e')[y' ::= x]"
      apply (rule flip_subst[symmetric])
      using `atom y' \<sharp> _`
      apply (simp add: fresh_Pair fresh_append)
      done
    also
    from `atom y' \<sharp> _`
    have "\<dots> \<ominus> is' @ is = (((y \<leftrightarrow> y') \<bullet> e') \<ominus> (is'@is))[y' ::= (x \<ominus> (is'@is))]" 
       by (simp add: resolve_subst fresh_Pair fresh_append)
    also
    have "L \<ominus> is' @ is = L \<ominus> is" by simp
    finally      
    have "\<Delta> \<ominus>\<^sub>h is'@is : (((y \<leftrightarrow> y') \<bullet> e') \<ominus> (is'@is))[y' ::= (x \<ominus> (is'@is))] \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)".
  }
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : App (e \<ominus> is) (x \<ominus> is' @ is) \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ is' @ is : z \<ominus> is'' @ is' @ is"
    apply (rule reds.Application[rotated])
    using Application(1-8) `atom y' \<sharp> _`
    apply (auto simp add: fresh_Pair fresh_append
          intro!: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
           eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
          eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt])
    done
  moreover
  from `atom \` fst \` set is' \<sharp>* L` `atom \` fst \` set is'' \<sharp>* L`
  have "atom ` (fst ` (set (is'' @ is'))) \<sharp>* L"
    by (auto simp add: fresh_star_def)
  ultimately
  show ?case
    by -(rule exI[where x = "is''@is'"], simp add: resolveExp_App resolve_var_append)
next
case (ApplicationInd y \<Gamma> e x L \<Delta> z u e' \<Theta>  "is")
  from ApplicationInd(8)
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x # L) \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : (Lam [y]. e') \<ominus> (is'@is)"
      and "atom ` fst ` set is' \<sharp>* (x # L)" by auto

  from this(2)
  have "atom ` fst ` set is' \<sharp>* x" and "atom ` fst ` set is' \<sharp>*  L"
    by (simp_all add: fresh_star_Pair fresh_star_Cons)

  from ApplicationInd(10)
  obtain "is''"
  where is'':"(y, Var x) # \<Delta> \<ominus>\<^sub>h ((y,x)#is'@is) : e' \<ominus> ((y,x)#is'@is)  \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> (y,x)#is'@is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@(y,x)#is'@is) : z \<ominus> (is''@(y,x)#is'@is)"
          and "atom ` fst ` set is'' \<sharp>* L" by blast

  from `atom \` fst \` set is' \<sharp>* x`
  have [simp]: "x \<ominus> is' = x"
    by (rule resolve_var_fresh)
  from `atom \` fst \` set is' \<sharp>* L`
  have [simp]: "L \<ominus> is' = L"
    by (rule resolve_var_list_fresh)

  from `atom y \<sharp> L`
  have [simp]: "\<And> is. L \<ominus> (y, x) # is = L \<ominus> is"
    by (induction L)(auto simp add: fresh_Cons)

  from `atom y \<sharp> \<Delta>`
  have [simp]:"resolveHeapOne \<Delta> y x = \<Delta>"
    apply (induction \<Delta> y x rule:resolveHeapOne.induct)
    apply (auto simp add: fresh_Cons fresh_Pair subst_fresh_noop)
    done 

  presume "supp is \<subseteq> supp \<Gamma> \<union> supp e \<union> supp L"
  with `atom y \<sharp> \<Gamma>`  `atom y \<sharp> e` `atom y \<sharp> L`
  have "atom y \<sharp> is" by (auto simp add: fresh_def)

  have "atom y \<sharp> is'" sorry

  from is' `atom y \<sharp> is` `atom y \<sharp> is'`
  have "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is)# (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y]. (e' \<ominus> (is'@is))"   
    by (simp add: resolveExp_Lam)
  hence "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is) # (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y]. (e' \<ominus> is'@is)"
    by simp
  moreover
  thm is''
  from is''  `atom y \<sharp> is`  `atom y \<sharp> is'`
  have "\<Delta> \<ominus>\<^sub>h is' @ is : (e' \<ominus> is'@is)[y::=(x \<ominus> is)] \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ (y,x)# is' @ is : z \<ominus> is'' @ (y,x)# is' @ is"
    by (simp add: resolve_subst)
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : App (e \<ominus> is) (x \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ (y,x) # is' @ is : z \<ominus> is'' @ (y,x)# is' @ is"
    apply (rule reds.Application[rotated])
    using ApplicationInd(1-6) `atom y \<sharp> is`  `atom y \<sharp> is'`
    apply (auto simp add: fresh_Pair fresh_append 
          intro: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
           eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
          eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt]
          resolveHeapOneFresh subst_is_fresh(1))
    done
  moreover
  from `atom \` fst \` set is' \<sharp>* L` `atom \` fst \` set is'' \<sharp>* L` `atom y \<sharp> L`
  have "atom ` (fst ` (set (is'' @ (y,x)# is'))) \<sharp>* L"
    by (auto simp add: fresh_star_def)
  ultimately
  show ?case
    by -(rule exI[where x = "is''@(y,x)#is'"], simp add: resolveExp_App resolve_var_append)
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
