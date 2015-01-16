theory CoCallImplFTreeCorrect
imports CoCallImplFTree CoCallAnalysisSpec FTreeAnalysisSpec CallFutureCardinality
begin

hide_const Multiset.single

lemma valid_lists_many_calls:
  assumes "\<not> one_call_in_path x p"
  assumes "p \<in> valid_lists S G"
  shows "x \<in> ccManyCalls G"
using assms(2,1)
proof(induction rule:valid_lists.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons xs x')
  show ?case
  proof(cases "one_call_in_path x xs")
    case False
    from Cons.IH[OF this]
    show ?thesis.
  next
    case True
    with `\<not> one_call_in_path x (x' # xs)`
    have [simp]: "x' = x" by (auto split: if_splits)

    have "x \<in> set xs"
    proof(rule ccontr)
      assume "x \<notin> set xs"
      hence "no_call_in_path x xs" by (metis no_call_in_path_set_conv)
      hence "one_call_in_path x (x # xs)" by simp
      with Cons show False by simp
    qed
    with `set xs \<subseteq> ccNeighbors x' G`
    have "x \<in> ccNeighbors x G" by auto
    thus ?thesis by simp
  qed
qed

context CoCallArityEdom
begin
 lemma carrier_Fexp': "carrier (Fexp e\<cdot>a) \<subseteq> fv e"
    unfolding Fexp_simp carrier_ccFTree
    by (rule Aexp_edom)

end


context CoCallArityCorrect
begin


lemma carrier_AnalBinds_below:
  "carrier ((Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom ((ABinds \<Delta>)\<cdot>(Aheap \<Delta> e\<cdot>a))"
by (auto simp add: Fexp.AnalBinds_lookup Fexp_def split: option.splits 
         elim!: set_mp[OF edom_mono[OF monofun_cfun_fun[OF ABind_below_ABinds]]])

sublocale FTreeAnalysisCarrier Fexp
  apply default unfolding Fexp_simp carrier_ccFTree..

sublocale FTreeAnalysisCorrect Fexp
proof default
  fix x e a

  from edom_mono[OF Aexp_App]
  have *: "{x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> edom (Aexp (App e x)\<cdot>a)" by auto

  have **: "{x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> insert x (fv e)"
    by (intro subset_trans[OF *] subset_trans[OF Aexp_edom]) auto

  have "many_calls x \<otimes>\<otimes> Fexp e\<cdot>(inc\<cdot>a) = many_calls x \<otimes>\<otimes> ccFTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))"
    unfolding Fexp_simp..
  also have "\<dots> = ccFTree {x} (ccProd {x} {x}) \<otimes>\<otimes> ccFTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))"
    unfolding many_calls_ccFTree..
  also have "\<dots> \<sqsubseteq> ccFTree ({x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a))) (ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (rule interleave_ccFTree)
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp (App e x)\<cdot>a)) (ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (rule ccFTree_mono1[OF *])
  also have "ccProd {x} {x} \<squnion> ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (edom (Aexp e\<cdot>(inc\<cdot>a))) = ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} ({x} \<union> (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (simp add: ccProd_union2[symmetric] del: ccProd_union2)
  also have "ccProd {x} ({x} \<union> (edom (Aexp e\<cdot>(inc\<cdot>a)))) \<sqsubseteq> ccProd {x} (insert x (fv e))"
    by (rule ccProd_mono2[OF **])
  also have "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a"
    by (rule ccExp_App)
  also have "ccFTree (edom (Aexp (App e x)\<cdot>a)) (ccExp (App e x)\<cdot>a) =  Fexp (App e x)\<cdot>a"
    unfolding Fexp_simp..
  finally
  show "many_calls x \<otimes>\<otimes> Fexp e\<cdot>(inc\<cdot>a) \<sqsubseteq> Fexp (App e x)\<cdot>a"
    by this simp_all
next
  fix y e n
  from edom_mono[OF Aexp_Lam]
  have *: "edom (Aexp e\<cdot>(pred\<cdot>n)) - {y} \<subseteq> edom (Aexp (Lam [y]. e)\<cdot>n)" by auto

  have "without y (Fexp e\<cdot>(pred\<cdot>n)) = without y (ccFTree (edom (Aexp e\<cdot>(pred\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n)))"
    unfolding Fexp_simp..
  also have "\<dots> = ccFTree (edom (Aexp e\<cdot>(pred\<cdot>n)) - {y}) (ccExp e\<cdot>(pred\<cdot>n))"
    by (rule  without_ccFTree)
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (ccExp e\<cdot>(pred\<cdot>n))"
    by (rule ccFTree_mono1[OF *])
  also have "\<dots> = ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (cc_restr ((edom (Aexp (Lam [y]. e)\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n)))"
    by (rule ccFTree_cc_restr)
  also have "(cc_restr ((edom (Aexp (Lam [y]. e)\<cdot>n))) (ccExp e\<cdot>(pred\<cdot>n))) \<sqsubseteq> (cc_restr (fv (Lam [y]. e)) (ccExp e\<cdot>(pred\<cdot>n)))"
    by (rule cc_restr_mono1[OF Aexp_edom])
  also have "\<dots> \<sqsubseteq> ccExp (Lam [y]. e)\<cdot>n"
    by (rule ccExp_Lam)
  also have "ccFTree (edom (Aexp (Lam [y]. e)\<cdot>n)) (ccExp (Lam [y]. e)\<cdot>n) = Fexp (Lam [y]. e)\<cdot>n"
    unfolding Fexp_simp..
  finally
  show "without y (Fexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Fexp (Lam [y]. e)\<cdot>n" by this simp_all
next
  fix e y x a

  from edom_mono[OF Aexp_subst]
  have *: "edom (Aexp e[y::=x]\<cdot>a) \<subseteq> insert x (edom (Aexp e\<cdot>a) - {y})" by simp


  have "Fexp e[y::=x]\<cdot>a = ccFTree (edom (Aexp e[y::=x]\<cdot>a)) (ccExp e[y::=x]\<cdot>a)"
    unfolding Fexp_simp..
  also have "\<dots> \<sqsubseteq> ccFTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a)"
    by (rule ccFTree_mono1[OF *])
  also have "\<dots> \<sqsubseteq> many_calls x \<otimes>\<otimes> without x (\<dots>)"
    by (rule paths_many_calls_subset)
  also have "without x (ccFTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a))
    = ccFTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e[y::=x]\<cdot>a)"
    by simp
  also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e\<cdot>a)"
    by (rule ccFTree_cong_below[OF ccExp_subst]) auto
  also have "\<dots> = without y (ccFTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a))"
    by simp (metis Diff_insert Diff_insert2)
  also have "ccFTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a) \<sqsubseteq> ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)"
    by (rule ccFTree_mono1) auto
  also have "\<dots> = Fexp e\<cdot>a"
    unfolding Fexp_simp..
  finally
  show "Fexp e[y::=x]\<cdot>a \<sqsubseteq> many_calls x \<otimes>\<otimes> without y (Fexp e\<cdot>a)"
    by this simp_all
next
  fix v a
  have "up\<cdot>a \<sqsubseteq> (Aexp (Var v)\<cdot>a) v" by (rule Aexp_Var)
  hence "v \<in> edom (Aexp (Var v)\<cdot>a)" by (auto simp add: edom_def)
  hence "[v] \<in> valid_lists (edom (Aexp (Var v)\<cdot>a)) (ccExp (Var v)\<cdot>a)"
    by auto
  thus "single v \<sqsubseteq> Fexp (Var v)\<cdot>a"
    unfolding Fexp_simp by (auto intro: single_below)
next
  fix scrut e1 a e2
  have "ccFTree (edom (Aexp e1\<cdot>a)) (ccExp e1\<cdot>a) \<oplus>\<oplus> ccFTree (edom (Aexp e2\<cdot>a)) (ccExp e2\<cdot>a)
    \<sqsubseteq> ccFTree (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a)"
      by (rule either_ccFTree)
  note both_mono2'[OF this]
  also
  have "ccFTree (edom (Aexp scrut\<cdot>0)) (ccExp scrut\<cdot>0) \<otimes>\<otimes> ccFTree (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a)
    \<sqsubseteq> ccFTree (edom (Aexp scrut\<cdot>0) \<union> (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a))) (ccExp scrut\<cdot>0 \<squnion> (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)))"
    by (rule interleave_ccFTree)
  also
  have "edom (Aexp scrut\<cdot>0) \<union> (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) = edom (Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a)" by auto
  also
  have "Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a \<sqsubseteq> Aexp (scrut ? e1 : e2)\<cdot>a"
    by (rule Aexp_IfThenElse)
  also
  have "ccExp scrut\<cdot>0 \<squnion> (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) \<sqsubseteq>
        ccExp (scrut ? e1 : e2)\<cdot>a"
    by (rule ccExp_IfThenElse)
  finally
  show "Fexp scrut\<cdot>0 \<otimes>\<otimes> (Fexp e1\<cdot>a \<oplus>\<oplus> Fexp e2\<cdot>a) \<sqsubseteq> Fexp (scrut ? e1 : e2)\<cdot>a"
    unfolding Fexp_simp
    by this simp_all
next
  fix e
  assume "isVal e"
  hence [simp]: "ccExp e\<cdot>0 = ccSquare (fv e)" by (rule ccExp_pap)
  thus "repeatable (Fexp e\<cdot>0)"
    unfolding Fexp_simp by (auto intro: repeatable_ccFTree_ccSquare[OF Aexp_edom])
qed

definition Fheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fheap \<Gamma> e = (\<Lambda> a. if nonrec \<Gamma> then ccFTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a) else ftree_restr (edom (Aheap \<Gamma> e\<cdot>a)) anything)"

lemma Fheap_simp: "Fheap \<Gamma> e\<cdot>a = (if nonrec \<Gamma> then ccFTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a) else ftree_restr (edom (Aheap \<Gamma> e\<cdot>a)) anything)"
  unfolding Fheap_def by simp

lemma carrier_Fheap':"carrier (Fheap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    unfolding Fheap_simp carrier_ccFTree by simp

sublocale FTreeAnalysisCardinalityHeap Fexp Aexp Aheap Fheap
proof default
  fix \<Gamma> e a
  show "carrier (Fheap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    by (rule carrier_Fheap')
next
  fix x \<Gamma> p e a
  assume "x \<in> thunks \<Gamma>"
  
  assume "\<not> one_call_in_path x p"
  hence "x \<in> set p" by (rule more_than_one_setD)
  
  assume "p \<in> paths (Fheap \<Gamma> e\<cdot>a)" with `x \<in> set p`
  have "x \<in> carrier (Fheap \<Gamma> e\<cdot>a)" by (auto simp add: Union_paths_carrier[symmetric])
  hence "x \<in> edom (Aheap \<Gamma> e\<cdot>a)"
    unfolding Fheap_simp by (auto split: if_splits)
  
  show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  proof(cases "nonrec \<Gamma>")
    case False
    from False `x \<in> thunks \<Gamma>`  `x \<in> edom (Aheap \<Gamma> e\<cdot>a)`
    show ?thesis  by (rule aHeap_thunks_rec)
  next
    case True
    with `p \<in> paths (Fheap \<Gamma> e\<cdot>a)`
    have "p \<in> valid_lists (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a)" by (simp add: Fheap_simp)

    with `\<not> one_call_in_path x p`
    have "x \<in> ccManyCalls (ccExp e\<cdot>a)" by (rule valid_lists_many_calls)
  
    from True `x \<in> thunks \<Gamma>` this
    show ?thesis by (rule aHeap_thunks_nonrec)
  qed
next
  fix \<Delta> e a

  show "ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>)  (Fexp e\<cdot>a)) \<sqsubseteq> Fexp (Let \<Delta> e)\<cdot>a"
  unfolding Fexp_simp
  proof (rule below_ccFTreeI)
    have "carrier (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
       = carrier (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))) - domA \<Delta>"
        by auto
    also
    have "carrier (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)))
         \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
    proof (rule carrier_substitute_below)
    show "carrier (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)" by simp
    next
      fix x
      assume "x \<in> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
      show "carrier ((ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
      proof(cases "map_of \<Delta> x")
        case None thus ?thesis by (simp add: Fexp.AnalBinds_lookup)
      next
        case (Some e')
        hence "carrier ((ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) = carrier (fup\<cdot>(Fexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))"
            by (simp add: Fexp.AnalBinds_lookup)
        also have "\<dots> \<subseteq> edom (fup\<cdot>(Aexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))"
          by (auto simp add: Fexp_simp)
        also have "\<dots> = edom (ABind x e'\<cdot>(Aheap \<Delta> e\<cdot>a))" by (simp add: ABind_def)
        also have "\<dots> \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))" using Some
          by (rule edom_mono[OF monofun_cfun_fun[OF ABind_below_ABinds]])
        also have "\<dots> \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)" by simp
        finally show ?thesis.
      qed
    qed
    also have "\<dots> \<subseteq> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a)"
      by (rule edom_mono[OF Aexp_Let])
    also have "edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a) - domA \<Delta> = edom (Aexp (Let \<Delta> e)\<cdot>a)"
      by (auto dest: set_mp[OF edom_Aheap] set_mp[OF Aexp_edom])
    finally
    show "carrier (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
          \<subseteq> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)"  by this auto
  next
    let ?x = "ccApprox (ftree_restr (- domA \<Delta>) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))"
  
    have "?x = cc_restr (- domA \<Delta>) ?x"  by simp
    also have "\<dots> \<sqsubseteq> cc_restr (- domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)"
    proof(rule cc_restr_mono2[OF wild_recursion_thunked])
    (*
      have "ccLinear (domA \<Delta>) (ccExp e\<cdot>a)" using linear by (rule linear_Exp)
      thus "ccLinear (domA \<Delta>) (ccApprox (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)))"
        by auto
    next
    *)
      have "ccExp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Exp)
      thus "ccApprox (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
        by (auto intro: below_trans[OF cc_restr_below_arg])
    next
      fix x
      assume "x \<notin> domA \<Delta>"
      thus "(Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x = empty"
        by (metis Fexp.AnalBinds_not_there empty_is_bottom)
    next
      fix x
      assume "x \<in> domA \<Delta>"
      then obtain e' where e': "map_of \<Delta> x = Some e'" by (metis domA_map_of_Some_the)
      
      (*
      thus "ccLinear (domA \<Delta>) (ccApprox ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x))"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        with linear e'
        have "ccLinear (domA \<Delta>) (ccExp e'\<cdot>a')" by (rule linear_Heap)
        thus ?thesis using up e' by (auto simp add: Fexp.AnalBinds_lookup Fexp_simp)
      qed
      *)
      
      show "ccApprox ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        with e'
        have "ccExp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Heap)
        thus ?thesis using up e'
          by (auto simp add: Fexp.AnalBinds_lookup Fexp_simp  intro: below_trans[OF cc_restr_below_arg])
      qed

      show "ccProd (ccNeighbors x (ccHeap \<Delta> e\<cdot>a)- {x} \<inter> thunks \<Delta>) (carrier ((Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Fexp.AnalBinds_lookup)
      next
        case (up a')
        have subset: "(carrier (fup\<cdot>(Fexp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))) \<subseteq> fv e'"
          using up e' by (auto simp add: Fexp.AnalBinds_lookup carrier_Fexp dest!: set_mp[OF Aexp_edom])
        
        from e' up
        have "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
          by (rule ccHeap_Extra_Edges)
        then
        show ?thesis using e'
          by (simp add: Fexp.AnalBinds_lookup  Fexp_simp ccProd_comm  below_trans[OF ccProd_mono1[OF subset]])
      qed
    qed
    also have "\<dots> \<sqsubseteq> ccExp (Let \<Delta> e)\<cdot>a"
      by (rule ccExp_Let)
    finally
    show "ccApprox (ftree_restr (- domA \<Delta>) (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (ccFTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a))))
        \<sqsubseteq> ccExp (Terms.Let \<Delta> e)\<cdot>a" by this simp_all

  qed

  have "carrier (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
  proof(rule carrier_substitute_below)
    from edom_mono[OF Aexp_Let[of \<Delta> e a]]
    show "carrier (Fexp e\<cdot>a) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"  by (simp add: Fexp_def)
  next
    fix x
    assume "x \<in> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    hence "x \<in> edom (Aheap \<Delta> e\<cdot>a) \<or> x : (edom (Aexp (Let \<Delta> e)\<cdot>a))" by simp
    thus "carrier ((Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    proof
      assume "x \<in> edom (Aheap \<Delta> e\<cdot>a)"
      
      have "carrier ((Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))"
        by (rule carrier_AnalBinds_below)
      also have "\<dots> \<subseteq> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Terms.Let \<Delta> e)\<cdot>a)"
        using edom_mono[OF Aexp_Let[of \<Delta> e a]] by simp
      finally show ?thesis by simp
    next
      assume "x \<in> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)"
      hence "x \<notin> domA \<Delta>" by (auto  dest: set_mp[OF Aexp_edom])
      hence "(Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x = \<bottom>"
        by (rule Fexp.AnalBinds_not_there)
      thus ?thesis by simp
    qed
  qed
  hence "carrier (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> - domA \<Delta>"
    by (rule order_trans) (auto dest: set_mp[OF Aexp_edom])
  hence "ftree_restr (domA \<Delta>)            (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
      = ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (ftree_restr (domA \<Delta>) (substitute (Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)))"
    by -(rule ftree_restr_noop[symmetric], auto)
  also
  have "\<dots> = ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))"
    by (simp add: inf.absorb2[OF edom_Aheap ])
  also
  (*
  have "substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a) \<sqsubseteq> singles (calledOnce \<Delta> e a)"
  proof(rule substitute_below_singlesI)
    show "Fexp e\<cdot>a \<sqsubseteq> singles (calledOnce \<Delta> e a)"
      unfolding Fexp_simp
      using calledOnce_exp
      by (auto intro!: ccFTree_below_singleI)
  next
    fix x
    show "carrier ((Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<inter> calledOnce \<Delta> e a = {}"
      using calledOnce_heap[unfolded disjoint_iff_not_equal]
      by (force simp add: Fexp.AnalBinds_lookup Fexp_simp split: option.split)
  qed
  hence "ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
      \<sqsubseteq> ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (singles (calledOnce \<Delta> e a))"
    by (rule ftree_restr_mono)
  *)
  have "\<dots> \<sqsubseteq> Fheap \<Delta> e \<cdot>a"
  proof(cases "nonrec \<Delta>")
    case False
    have "ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
      \<sqsubseteq> ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) anything"
    by (rule ftree_restr_mono) simp
    also have "\<dots> = Fheap \<Delta> e\<cdot>a"
      by (simp add:  Fheap_simp False)
    finally show ?thesis.
  next
    case True[simp]

    from True
    have "ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Fexp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a))
       = ftree_restr (edom (Aheap \<Delta> e\<cdot>a)) (Fexp e\<cdot>a)"
      by (rule nonrecE) (rule ftree_rest_substitute, auto simp add: carrier_Fexp fv_def fresh_def dest!: set_mp[OF edom_Aheap] set_mp[OF Aexp_edom])
    also have "\<dots> = ccFTree (edom (Aexp e\<cdot>a) \<inter> edom (Aheap \<Delta> e\<cdot>a)) (ccExp e\<cdot>a)"
      by (simp add: Fexp_simp)
    also have "\<dots> \<sqsubseteq> ccFTree (edom (Aexp e\<cdot>a) \<inter> domA \<Delta>) (ccExp e\<cdot>a)"
      by (rule ccFTree_mono1[OF Int_mono[OF order_refl edom_Aheap]])
    also have "\<dots> \<sqsubseteq> ccFTree (edom (Aheap \<Delta> e\<cdot>a)) (ccExp e\<cdot>a)"
      by (rule ccFTree_mono1[OF edom_mono[OF Aheap_nonrec[OF True], simplified]])
    also have "\<dots> \<sqsubseteq> Fheap \<Delta> e\<cdot>a"
      by (simp add: Fheap_simp)
    finally
    show ?thesis by this simp_all
  qed
  finally
  show "ftree_restr (domA \<Delta>) (substitute (ExpAnalysis.AnalBinds Fexp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<sqsubseteq> Fheap \<Delta> e\<cdot>a".

qed
end

(* TODO: Unused stuff from here, mostly about singles. Might be useful later. *)


lemma paths_singles: "xs \<in> paths (singles S) \<longleftrightarrow> (\<forall>x \<in> S. one_call_in_path x xs)"
  by transfer (auto simp add: one_call_in_path_filter_conv)

lemma paths_singles': "xs \<in> paths (singles S) \<longleftrightarrow> (\<forall>x \<in> (set xs \<inter> S). one_call_in_path x xs)"
  apply transfer
  apply (auto simp add: one_call_in_path_filter_conv)
  apply (erule_tac x = x in ballE)
  apply auto
  by (metis (poly_guards_query) filter_empty_conv le0 length_0_conv)

lemma both_below_singles1:
  assumes "t \<sqsubseteq> singles S"
  assumes "carrier t' \<inter> S = {}"
  shows "t \<otimes>\<otimes> t' \<sqsubseteq> singles S"
proof (rule ftree_belowI)
  fix xs
  assume "xs \<in> paths (t \<otimes>\<otimes> t')"
  then obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> ys \<otimes> zs" by (auto simp add: paths_both)
  with assms 
  have "ys \<in> paths (singles S)" and "set zs \<inter> S = {}"
    by (metis below_ftree.rep_eq contra_subsetD paths.rep_eq, auto simp add: Union_paths_carrier[symmetric])
  with `xs \<in> ys \<otimes> zs`
  show "xs \<in> paths (singles S)"
    by (induction) (auto simp add: paths_singles no_call_in_path_set_conv interleave_set dest: more_than_one_setD split: if_splits)
qed


lemma paths_ftree_restr_singles: "xs \<in> paths (ftree_restr S' (singles S)) \<longleftrightarrow> set xs \<subseteq> S' \<and> (\<forall>x \<in> S. one_call_in_path x xs)"
proof
  show "xs \<in> paths (ftree_restr S' (singles S)) \<Longrightarrow>  set xs \<subseteq> S' \<and> (\<forall>x \<in> S. one_call_in_path x xs)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric] paths_singles)
next
  assume *: "set xs \<subseteq> S' \<and> (\<forall>x\<in>S. one_call_in_path x xs)"
  hence "set xs \<subseteq> S'" by auto
  hence [simp]: "filter (\<lambda> x'. x' \<in> S') xs = xs" by (auto simp add: filter_id_conv)
  
  from *
  have "xs \<in> paths (singles S)"
     by (auto simp add: paths_singles')
  hence "filter (\<lambda> x'. x' \<in> S') xs \<in> filter (\<lambda>x'. x' \<in> S') ` paths (singles S)"
    by (rule imageI)
  thus "xs \<in> paths (ftree_restr S' (singles S))"
    by (auto simp add: filter_paths_conv_free_restr[symmetric] )
qed



(* TODO: unused *)
lemma substitute_not_carrier:
  assumes "x \<notin> carrier t"
  assumes "\<And> x'. x \<notin> carrier (f x')"
  shows "x \<notin>  carrier (substitute f T t)"
proof-
  have "ftree_restr ({x}) (substitute f T t) = ftree_restr ({x}) t"
  proof(rule ftree_rest_substitute)
    fix x'
    from `x \<notin> carrier (f x')`
    show "carrier (f x') \<inter> {x} = {}" by auto
  qed
  hence "x \<notin> carrier (ftree_restr ({x}) (substitute f T t)) \<longleftrightarrow> x \<notin> carrier (ftree_restr ({x}) t)" by metis
  with assms(1)
  show ?thesis by simp
qed

(* TODO: unused *)
lemma substitute_below_singlesI:
  assumes "t \<sqsubseteq> singles S"
  assumes "\<And> x. carrier (f x) \<inter> S = {}"
  shows "substitute f T t \<sqsubseteq> singles S"
proof(rule ftree_belowI)
  fix xs
  assume "xs \<in> paths (substitute f T t)"
  thus "xs \<in> paths (singles S)"
  using assms
  proof(induction f T t xs arbitrary: S rule: substitute_induct)
    case Nil
    thus ?case by simp
  next
    case (Cons f T t x xs)

    from `x#xs \<in> _`
    have xs: "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by auto
    moreover

    from `t \<sqsubseteq> singles S`
    have "nxt t x \<sqsubseteq> singles S" 
      by (metis "FTree-HOLCF.nxt_mono" below_trans nxt_singles_below_singles)
    from this `carrier (f x) \<inter> S = {}`
    have "nxt t x \<otimes>\<otimes> f x \<sqsubseteq> singles S"
      by (rule both_below_singles1)
    moreover
    { fix x'
      from  `carrier (f x') \<inter> S = {}`
      have "carrier (f_nxt f T x x') \<inter> S = {}"
        by (auto simp add: f_nxt_def)
    }
    ultimately
    have IH: "xs \<in> paths (singles S)"
      by (rule Cons.IH) 
  
  show ?case
    proof(cases "x \<in> S")
      case True
      with `carrier (f x) \<inter> S = {}`
      have "x \<notin> carrier (f x)" by auto
      moreover
      from `t \<sqsubseteq> singles S`
      have "nxt t x \<sqsubseteq> nxt (singles S) x" by (rule nxt_mono)
      hence "carrier (nxt t x) \<subseteq> carrier (nxt (singles S) x)" by (rule carrier_mono)
      from set_mp[OF this] True
      have "x \<notin> carrier (nxt t x)" by auto
      ultimately
      have "x \<notin> carrier (nxt t x \<otimes>\<otimes> f x)" by simp
      hence "x \<notin> carrier (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))"
      proof(rule substitute_not_carrier)
        fix x'  
        from `carrier (f x') \<inter> S = {}` `x \<in> S`
        show "x \<notin> carrier (f_nxt f T x x')" by (auto simp add: f_nxt_def)
      qed
      with xs
      have "x \<notin> set xs" by (auto simp add: Union_paths_carrier[symmetric])
      with IH
      have "xs \<in> paths (without x (singles S))" by (rule paths_withoutI)
      thus ?thesis using True by (simp add: Cons_path)
    next
      case False
      with IH
      show ?thesis by (simp add: Cons_path)
    qed
  qed
qed

end

