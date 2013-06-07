theory RemoveIndirection
imports LaunchburyCombined "Nominal-Utils" 
begin

type_synonym indirections = "(var \<times> var) list "

inductive IndirectionList :: "indirections \<Rightarrow> bool" where
  NilIndirection: "IndirectionList []"
  | ConsIndirection: "IndirectionList is \<Longrightarrow> atom i \<sharp> is \<Longrightarrow> IndirectionList ((i,x) # is)"

class resolvable =
  fixes resolve :: "'a \<Rightarrow> indirections \<Rightarrow> 'a" (infixl "\<ominus>" 60)

class resolvable_eqvt = resolvable + pt + 
  assumes resolve_eqvt: "p \<bullet> (x \<ominus> is) = (p \<bullet> x) \<ominus> (p \<bullet> is)"

declare resolve_eqvt[eqvt]

instantiation list :: (resolvable) resolvable 
begin
  definition resolve_list :: "'a list \<Rightarrow> indirections \<Rightarrow> 'a list"
  where "m \<ominus> is = map (\<lambda>x. x \<ominus> is) m"
instance ..
end

instance list :: (resolvable_eqvt) resolvable_eqvt
  by default (simp_all add: resolve_list_def)

lemma resolve_list_Cons[simp]: "(x # xs) \<ominus> is = (x \<ominus> is) # (xs \<ominus> is)"
  unfolding resolve_list_def by simp

instantiation var :: resolvable 
begin
  fun resolve_var :: "var \<Rightarrow> indirections \<Rightarrow> var"  where
    "v \<ominus> [] = (v::var)"
    | "v \<ominus> ((x,y)#is) = v[x ::v= y] \<ominus> is"
instance ..
end

instance var ::  resolvable_eqvt
  apply default
  apply (induct_tac x "is" rule:resolve_var.induct)
  apply (simp+)
  done


instantiation exp :: resolvable 
begin
  fun resolve_exp :: "exp \<Rightarrow> indirections \<Rightarrow> exp" where
    "e \<ominus> [] = (e::exp)"
    | "e \<ominus> ((x,y)#is) = (e[x ::= y]) \<ominus> is"
instance ..
end

lemma resolve_exp_eqvt[eqvt]: "p \<bullet> ((e::exp) \<ominus> is) = (p \<bullet> e) \<ominus> (p \<bullet> is)"
  by (induction e "is" rule:resolve_exp.induct) simp+

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


function resolveHeap :: "heap \<Rightarrow> indirections \<Rightarrow> heap" (infixl "\<ominus>\<^sub>h" 60) where
  "[] \<ominus>\<^sub>h is = []"
 | "x \<in> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = \<Gamma>  \<ominus>\<^sub>h is"
 | "x \<notin> fst ` set is \<Longrightarrow> (x,e)#\<Gamma> \<ominus>\<^sub>h is = (x, e \<ominus> is)# (\<Gamma> \<ominus>\<^sub>h is)"
  apply (metis neq_Nil_conv surjective_pairing)
  apply auto
  done
termination by lexicographic_order

lemma resolveHeap_eqvt[eqvt]: "p \<bullet> resolveHeap \<Gamma> is = resolveHeap (p \<bullet> \<Gamma>) (p \<bullet> is)"
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
  "\<Gamma> : e \<Down>\<^sup>i\<^sup>u\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> supp is \<subseteq> supp \<Gamma> \<union> supp L \<Longrightarrow>
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>False\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : z \<ominus> (is'@is))
       \<and> supp (fst ` set is') \<sharp>* supp (\<Gamma>, L)" 
proof (nominal_induct \<Gamma> e i u L \<Delta> z avoiding: "is"  rule:reds.strong_induct )
case (Lambda x \<Gamma> L e i u "is")[simp]
  have "resolveHeap \<Gamma> is : Lam [x]. (e \<ominus> is) \<Down>\<^sup>False\<^sup>u \<^bsub>L \<ominus> is\<^esub>  \<Gamma> \<ominus>\<^sub>h is : Lam [x]. (e \<ominus> is)"
    by (rule LambdaI)
  then
  show ?case
    apply -
    apply(rule exI[where x = "[]"])
    apply (simp add: resolveExp_Lam supp_set_empty fresh_star_def)
    done
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z u e' "is")
    from Application(13)
    have "supp is \<subseteq> supp \<Gamma> \<union> supp (x # L)" by (auto simp add: supp_Cons)
    from Application(10)[OF this]
    obtain "is'"
    where is': "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>False\<^sup>u\<^bsub>(x # L) \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : (Lam [y]. e') \<ominus> (is'@is)"
        and "supp (fst ` set is') \<sharp>* supp (\<Gamma>, x # L)" by auto

    have "supp (is'@is) \<subseteq> supp \<Delta> \<union> supp L" sorry
    from Application(12)[OF this]
    obtain "is''"
    where is'':"\<Delta> \<ominus>\<^sub>h is'@is : (e'[y::=x]) \<ominus> is'@is \<Down>\<^sup>False\<^sup>u\<^bsub>L \<ominus> is'@is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)"
            and "supp (fst ` set is'') \<sharp>* supp (\<Delta>, L)" by auto

    have [simp]: "x \<ominus> is' @ is = x \<ominus> is" sorry
    have [simp]: "L \<ominus> is' @ is = L \<ominus> is" sorry

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
    have "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>False\<^sup>u\<^bsub>(x \<ominus> is'@is)# (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y']. (((y \<leftrightarrow> y') \<bullet> e') \<ominus> (is'@is))"
      by (simp add: fresh_Pair flip_fresh_fresh resolveExp_Lam fresh_append del: exp_assn.eq_iff)
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
    also note `L \<ominus> is' @ is = L \<ominus> is`
    finally      
    have "\<Delta> \<ominus>\<^sub>h is'@is : (((y \<leftrightarrow> y') \<bullet> e') \<ominus> (is'@is))[y' ::= (x \<ominus> (is'@is))] \<Down>\<^sup>False\<^sup>u\<^bsub>L \<ominus> is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@is'@is) : z \<ominus> (is''@is'@is)".
  }
  ultimately
  thm reds.Application[rotated, OF this(1), OF this(2)]
  have "\<Gamma> \<ominus>\<^sub>h is : App (e \<ominus> is) (x \<ominus> is' @ is) \<Down>\<^sup>False\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ is' @ is : z \<ominus> is'' @ is' @ is"
    apply (rule reds.Application[rotated])
    using Application(1-8) `atom y' \<sharp> _`
    apply (auto simp add: fresh_Pair fresh_append
          intro!: eqvt_fresh_cong2[where f = "resolve :: exp \<Rightarrow> indirections \<Rightarrow> exp", OF resolve_exp_eqvt] 
           eqvt_fresh_cong2[where f = "resolve :: 'a::resolvable_eqvt \<Rightarrow> indirections \<Rightarrow> 'a", OF resolve_eqvt] 
          eqvt_fresh_cong2[where f = resolveHeap, OF resolveHeap_eqvt])
    done
  moreover
  have "supp (fst ` (set is'' \<union> set is')) \<sharp>* supp (\<Gamma>, L)"
    sorry
  ultimately
  show ?case
    by -(rule exI[where x = "is''@is'"], simp add: resolveExp_App)
next

qed  

end
