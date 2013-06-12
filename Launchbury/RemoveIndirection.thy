theory RemoveIndirection
imports LaunchburyCombined Indirections "Nominal-Utils" 
begin

theorem
  "\<Gamma> : e \<Down>\<^sup>\<surd>\<^sup>u\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> supp is \<subseteq> supp \<Gamma> \<union> supp e \<union> supp L \<Longrightarrow>
  \<exists> is'. (\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : z \<ominus> (is'@is))
       \<and> atom ` (fst ` set is') \<sharp>* L 
       \<and> supp is' \<subseteq> supp \<Delta> \<union> supp z \<union> supp L
       \<and> set (vars::atom list) \<sharp>* is'"
proof (nominal_induct \<Gamma> e "\<surd>" u L \<Delta> z avoiding: "is" vars rule:reds.strong_induct )
case (Lambda x \<Gamma> L e  u "is" vars)[simp]
  have "resolveHeap \<Gamma> is : Lam [x]. (e \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u \<^bsub>L \<ominus> is\<^esub>  \<Gamma> \<ominus>\<^sub>h is : Lam [x]. (e \<ominus> is)"
    by (rule LambdaI)
  then
  show ?case
    apply -
    apply(rule exI[where x = "[]"])
    apply (simp add: resolveExp_Lam supp_set_empty fresh_star_def fresh_Nil supp_Nil)
    done
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
case (ApplicationInd y \<Gamma> e x L u \<Delta> e' \<Theta> z "is" vars)
  from `supp is \<subseteq> supp \<Gamma> \<union> supp (App e x) \<union> supp L`
        and `atom y \<sharp> \<Gamma>` `atom y \<sharp> e`  `atom y \<sharp> x`  `atom y \<sharp> L` 
  have "atom y \<sharp> is" by (auto simp add: fresh_def exp_assn.supp)

  from `supp is \<subseteq> supp \<Gamma> \<union> supp (App e x) \<union> supp L`
  have "supp is \<subseteq> supp \<Gamma> \<union> supp e \<union> supp (y # x # L)" by (auto simp add: supp_Cons exp_assn.supp)
  from ApplicationInd(6)[OF this]
  obtain "is'"
  where is': "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(y # x # L) \<ominus> is\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : (Lam [y]. e') \<ominus> (is'@is)"
      and "atom ` fst ` set is' \<sharp>* (y # x # L)"
      and "set vars \<sharp>* is'"
      and "supp is' \<subseteq> supp \<Delta> \<union> supp (Lam [y]. e') \<union> supp (y # x # L)"
      by blast

  from this(2)
  have  "atom ` fst ` set is' \<sharp>* y" and "atom ` fst ` set is' \<sharp>* x" and "atom ` fst ` set is' \<sharp>*  L"
    by (simp_all add: fresh_star_Pair fresh_star_Cons)

  have "atom y \<sharp> \<Delta>" using ApplicationInd by (auto dest!: reds_fresh_L)
 
  have "supp is' \<subseteq> supp \<Delta> \<union> supp (Lam [y]. e') \<union> supp (x # L)" sorry
  with `atom y \<sharp> \<Delta>` `atom y \<sharp> x` `atom y \<sharp> L`
  have "atom y \<sharp> is'" by (auto simp add: fresh_def supp_Cons exp_assn.supp)

  (*
  from `_ \<sharp>* is'`
  have "atom y \<sharp> is'" and  "set vars \<sharp>* is'"
    by (auto simp add: fresh_star_def)
  *)

  have "supp is' \<subseteq> supp \<Delta> \<union> supp (Lam [y]. e') \<union> supp L" sorry
  moreover
  have "supp is \<subseteq> supp ((y, Var x) # \<Delta>) \<union> supp e' \<union> supp L" sorry
  ultimately
  have "supp ((y,x)#is'@is) \<subseteq> supp ((y, Var x) # \<Delta>) \<union> supp e' \<union> supp L"
     by (auto simp add: supp_Cons exp_assn.supp supp_Pair supp_append)
  from ApplicationInd(8)[OF this]
  obtain "is''"
  where is'':"(y, Var x) # \<Delta> \<ominus>\<^sub>h ((y,x)#is'@is) : e' \<ominus> ((y,x)#is'@is)  \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> (y,x)#is'@is \<^esub> \<Theta> \<ominus>\<^sub>h (is''@(y,x)#is'@is) : z \<ominus> (is''@(y,x)#is'@is)"
          and "atom ` fst ` set is'' \<sharp>* L"
          and "supp is'' \<subseteq> supp \<Theta> \<union> supp z \<union> supp L"
          and "set vars \<sharp>* is''"
          by blast

  (* Because is' is introduced later the strong induction does not provide us
     with @{term "atom y \<sharp> is'"}, so we need to shuffle variables around. *)
  obtain y' :: var where "atom y' \<sharp> (y, is, is', is'', e', e, \<Gamma>, x, \<Delta>, \<Theta>, z, L)" by (rule obtain_fresh)
  hence "Lam [y]. e' =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e')" 
    by -(rule change_Lam_Variable, simp_all add: fresh_Pair)

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

  (*
  presume "set vars \<sharp>* (\<Gamma>, App e x, \<Theta>, z)"
  hence "set vars \<sharp>* x" and "set vars \<sharp>* \<Theta>" by (auto simp add: fresh_star_def fresh_Pair)
  *)
  have "set vars \<sharp>* x" sorry

  (*
  from reds_doesnt_forget[OF ApplicationInd(9)]
  have "y \<in> heapVars \<Theta>" by simp
  with `set vars \<sharp>* \<Theta>`
  have "set vars \<sharp>* y" by (metis fresh_ineq_at_base fresh_star_def heapVars_not_fresh)
  *)
  have "set vars \<sharp>* y" sorry

  (*
  presume "supp is \<subseteq> supp \<Gamma> \<union> supp e \<union> supp L"
  with `atom y \<sharp> \<Gamma>`  `atom y \<sharp> e` `atom y \<sharp> L`
  have "atom y \<sharp> is" by (auto simp add: fresh_def)
  *)
  (*
  have "atom y \<sharp> is" sorry
  *)

  {
    note is'
    also have "(Lam [y]. e' \<ominus> (is'@is)) = Lam [y]. (e' \<ominus> (is'@is))"
      using `atom y \<sharp> is` `atom y \<sharp> is'` by (simp add: resolveExp_Lam fresh_Pair)
    also have "y # x # L \<ominus> is = (y \<ominus> is) # (x \<ominus> is) # (L \<ominus> is)" by simp
    finally
    have "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(y \<ominus> is) # (x \<ominus> is) # (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y]. (e' \<ominus> is'@is)".
    hence "\<Gamma> \<ominus>\<^sub>h is : e \<ominus> is \<Down>\<^sup>\<times>\<^sup>u\<^bsub>(x \<ominus> is) # (L \<ominus> is)\<^esub> \<Delta> \<ominus>\<^sub>h (is'@is) : Lam [y]. (e' \<ominus> is'@is)"
      by (rule reds_smaller_L) auto
  }
  moreover
  {
    note is''
    also have "(y, Var x) # \<Delta> \<ominus>\<^sub>h (y, x) # is' @ is  = \<Delta> \<ominus>\<^sub>h is'@is" by simp
    also have "e' \<ominus> (y, x) # is' @ is =  (e' \<ominus> is'@is)[y::=(x \<ominus> is)]"
      using `atom y \<sharp> is`  `atom y \<sharp> is'` by (simp add: resolve_subst)
    find_theorems subst flip
    also have "L \<ominus> (y, x) # is' @ is = L \<ominus> is" by simp
    finally
    have "\<Delta> \<ominus>\<^sub>h is' @ is : (e' \<ominus> is'@is)[y::=(x \<ominus> is)] \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub>
              \<Theta> \<ominus>\<^sub>h is'' @ (y,x)# is' @ is : z \<ominus> is'' @ (y,x)# is' @ is".
  }
  ultimately
  have "\<Gamma> \<ominus>\<^sub>h is : App (e \<ominus> is) (x \<ominus> is) \<Down>\<^sup>\<times>\<^sup>u\<^bsub>L \<ominus> is\<^esub> \<Theta> \<ominus>\<^sub>h is'' @ (y,x) # is' @ is : z \<ominus> is'' @ (y,x)# is' @ is"
    apply (rule reds.Application[rotated])
    using ApplicationInd(1-6) `atom y \<sharp> is`  `atom y \<sharp> is'` `atom y \<sharp> \<Delta>` `atom y' \<sharp> _`
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
  moreover
  from `set vars \<sharp>* is'` and  `set vars \<sharp>* is''` and `set vars \<sharp>* y` and `set vars \<sharp>* x`
  have "set vars \<sharp>* (is''@ (y,x)# is')"
    by (simp add: fresh_star_append fresh_star_Cons fresh_star_Pair)
  moreover
  have "supp (is'' @ (y, x) # is') \<subseteq> supp \<Theta> \<union> supp z \<union> supp L" sorry
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
