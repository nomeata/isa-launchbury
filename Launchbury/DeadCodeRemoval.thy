theory DeadCodeRemoval
imports Terms Substitution
begin

nominal_function
  remove_dead_code :: "exp \<Rightarrow> exp"
where
  "remove_dead_code (Lam [x]. e) = Lam [x]. remove_dead_code e"
| "remove_dead_code (App e x) = App (remove_dead_code e) x"
| "remove_dead_code (Var x) = Var x"
| "remove_dead_code (Let as e) =
    (if domA as \<inter> fv e = {} then remove_dead_code e
                           else Let (map_ran (\<lambda> _ e. remove_dead_code e) as) (remove_dead_code e))"
| "remove_dead_code (Bool b) = Bool b"
| "remove_dead_code (scrut ? e1 : e2) = (remove_dead_code scrut ? remove_dead_code e1 : remove_dead_code e2)"
proof-
case goal1 thus ?case
  unfolding remove_dead_code_graph_aux_def eqvt_def 
  apply rule
  apply perm_simp
  apply rule
  done
next
case goal3 thus ?case
  by (metis Terms.Let_def exp_assn.exhaust(1) heapToAssn_asToHeap)
next
case (goal4 x e x' e')
  from goal4(5)
  show ?case
  proof (rule eqvt_lam_case)
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Lam [x]. e"
    hence *: "supp \<pi> \<sharp>* Lam [x]. remove_dead_code_sumC e"
      by (auto simp add:  fresh_star_def fresh_eqvt_at[OF goal4(1)] exp_assn.fsupp)
      
    have "Lam [(\<pi> \<bullet> x)]. remove_dead_code_sumC (\<pi> \<bullet> e) =  \<pi> \<bullet> Lam [x]. remove_dead_code_sumC e"
        by (simp add: pemute_minus_self eqvt_at_apply'[OF goal4(1)])
    also have "\<dots> = Lam [x]. remove_dead_code_sumC e" by (rule perm_supp_eq[OF *])
    finally show  "Lam [(\<pi> \<bullet> x)]. remove_dead_code_sumC (\<pi> \<bullet> e) = Lam [x]. remove_dead_code_sumC e".
  qed
next
case (goal19 as body as' body')
  from goal19(13)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
  
    from goal19(1,3) have eqvt_at1: "eqvt_at remove_dead_code_sumC body" by auto

    assume assm: "supp \<pi> \<sharp>* Let as body"

    show "(if domA (\<pi> \<bullet> as) \<inter> fv (\<pi> \<bullet> body) = {} then remove_dead_code_sumC (\<pi> \<bullet> body) else Let (map_ran (\<lambda>_. remove_dead_code_sumC) (\<pi> \<bullet> as)) (remove_dead_code_sumC (\<pi> \<bullet> body))) =
         (if domA as \<inter> fv body = {} then remove_dead_code_sumC body else Let (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body))"
    proof(rule if_cong)
      show cond_eqvt: "domA (\<pi> \<bullet> as) \<inter> fv (\<pi> \<bullet> body) = {} \<longleftrightarrow> domA as \<inter> fv body = {}" 
        by (metis empty_eqvt permute_eq_iff inter_eqvt fv_eqvt domA)
    next
      assume "domA as \<inter> fv body \<noteq> {}"
      from goal19(2)[OF this]
      have eqvt_at2: "eqvt_at (map_ran (\<lambda>_. remove_dead_code_sumC)) as" by (induction as) (fastforce simp add: eqvt_at_def)+

      have *: "supp \<pi> \<sharp>* Let (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)" using assm
        by (auto simp add:  fresh_star_def fresh_eqvt_at[OF eqvt_at1] fresh_eqvt_at[OF eqvt_at2] finite_supp)


      have "Let  (map_ran (\<lambda>_. remove_dead_code_sumC) (\<pi> \<bullet> as)) (remove_dead_code_sumC (\<pi> \<bullet> body)) = \<pi> \<bullet> Let (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)"
          by (simp add: eqvt_at_apply'[OF eqvt_at1]  eqvt_at_apply'[OF eqvt_at2])
      also have "\<dots> = Let (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)" by (rule perm_supp_eq[OF *])
      finally show  "Let (map_ran (\<lambda>_. remove_dead_code_sumC) (\<pi> \<bullet> as)) (remove_dead_code_sumC (\<pi> \<bullet> body)) =  Let (map_ran (\<lambda>_. remove_dead_code_sumC) as) (remove_dead_code_sumC body)" .
    next
      assume "domA as \<inter> fv body = {}"
      with `supp \<pi> \<sharp>* Let as body`
      have "supp \<pi> \<sharp>* body" by (auto simp add: fv_def fresh_star_def fresh_def Let_supp)
      hence "\<pi> \<bullet> body = body" by (rule perm_supp_eq)
      thus "remove_dead_code_sumC (\<pi> \<bullet> body) = remove_dead_code_sumC body" by simp
    qed
  qed
qed auto
nominal_termination (eqvt) by lexicographic_order

lemma subst_remove_dead_code: "(remove_dead_code e)[y::=x] = remove_dead_code (e [y::=x])"
  and "(map_ran (\<lambda> _ e. remove_dead_code e) \<Gamma>)[y::h=x] = map_ran (\<lambda> _ e. remove_dead_code e) (\<Gamma>[y::h=x])"
proof (nominal_induct e and \<Gamma>  avoiding: y x rule:exp_heap_strong_induct)
case (Let \<Gamma> e y x)
  thus ?case
  by (cases "domA \<Gamma> \<inter> fv e = {}") (auto simp add: fresh_star_at_base fv_subst_eq fresh_star_Pair pure_fresh)
qed auto

end
