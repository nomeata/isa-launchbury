theory AbstractTransform
imports Terms Up TransformTools
begin


locale AbstractAnalProp =
  fixes PropApp :: "exp \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> ('a::cont_pt)"
  fixes PropLam :: "var \<Rightarrow> exp \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes PropLetBody :: "heap \<Rightarrow> exp \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes PropLetHeap :: "heap \<Rightarrow> exp \<Rightarrow> 'a \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>)"
  assumes PropApp_eqvt: "\<pi> \<bullet> PropApp \<equiv> PropApp"
  assumes PropLam_eqvt: "\<pi> \<bullet> PropLam \<equiv> PropLam"
  assumes PropLetBody_eqvt: "\<pi> \<bullet> PropLetBody \<equiv> PropLetBody"
  assumes PropLetHeap_eqvt: "\<pi> \<bullet> PropLetHeap \<equiv> PropLetHeap"

locale AbstractTransform = AbstractAnalProp +
  constrains PropApp :: "exp \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> ('a::pure_cont_pt)"
  fixes TransVar :: "'a \<Rightarrow> var \<Rightarrow> exp"
  fixes TransVar1 :: "'a \<Rightarrow> var \<Rightarrow> exp"
  fixes TransApp :: "'a \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> exp"
  fixes TransLam :: "'a \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp"
  fixes TransLet :: "'a \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> exp"
  assumes TransVar_eqvt: "\<pi> \<bullet> TransVar = TransVar"
  assumes TransVar1_eqvt: "\<pi> \<bullet> TransVar1 = TransVar1"
  assumes TransApp_eqvt: "\<pi> \<bullet> TransApp = TransApp"
  assumes TransLam_eqvt: "\<pi> \<bullet> TransLam = TransLam"
  assumes TransLet_eqvt: "\<pi> \<bullet> TransLet = TransLet"
  assumes SuppTransLam: "supp (TransLam a v e) \<subseteq> supp e - supp v"
  assumes SuppTransLet: "supp (TransLet a ae \<Gamma> e) \<subseteq> supp (\<Gamma>, e) - atom ` domA \<Gamma>"
begin
  nominal_function transform where
    "transform a (App e x) = TransApp a (transform (PropApp e x a) e) x"
  | "transform a (Lam [x]. e) = TransLam a x (transform (PropLam x e a) e)"
  | "transform a (Var x) = TransVar a x"
  | "transform a (Var1 x) = TransVar1 a x"
  | "transform a (Let \<Delta> e) = TransLet a  (PropLetHeap \<Delta> e a)
        (map_transform transform (PropLetHeap \<Delta> e a) \<Delta>)
        (transform (PropLetBody \<Delta> e a) e)"
proof-
case goal1
  note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt] TransVar1_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]
  show ?case
  unfolding eqvt_def transform_graph_aux_def
    apply rule
    apply perm_simp
    apply (rule refl)
    done
  case (goal3 P x)
    show ?case
    proof (cases x)
      fix a b
      assume "x = (a, b)"
      thus ?case
      using goal3
      apply (cases b rule:Terms.exp_strong_exhaust)
      apply auto
      done
    qed
  next
case (goal9 a x e a' x' e')
  from goal9(5)
  have "a' = a" and  "Lam [x]. e = Lam [x']. e'" by simp_all
  from this(2)
  show ?case
  unfolding `a' = a`
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm

    have "supp (TransLam a x (transform_sumC (PropLam x e a, e))) \<subseteq> supp (Lam [x]. e)"
      apply (rule subset_trans[OF SuppTransLam])
      apply (auto simp add:  exp_assn.supp supp_Pair supp_at_base pure_supp exp_assn.fsupp dest!: set_mp[OF supp_eqvt_at[OF goal9(1)], rotated])
      done
    moreover
    assume "supp \<pi> \<sharp>* (Lam [x]. e)" 
    ultimately
    have *: "supp \<pi> \<sharp>* TransLam a x (transform_sumC (PropLam x e a, e))" by (auto simp add: fresh_star_def fresh_def)

    note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt] TransVar1_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]

    have "TransLam a (\<pi> \<bullet> x) (transform_sumC (PropLam (\<pi> \<bullet> x) (\<pi> \<bullet> e) a, \<pi> \<bullet> e))
        = TransLam a (\<pi> \<bullet> x) (transform_sumC (\<pi> \<bullet>  (PropLam x e a, e)))"
      by perm_simp rule
    also have "\<dots> = TransLam a (\<pi> \<bullet> x) (\<pi> \<bullet> transform_sumC (PropLam x e a, e))"
      unfolding eqvt_at_apply'[OF goal9(1)]..
    also have "\<dots> = \<pi> \<bullet> (TransLam a x (transform_sumC (PropLam x e a, e)))"
      by simp
    also have "\<dots> = TransLam a x (transform_sumC (PropLam x e a, e))"
      by (rule perm_supp_eq[OF *])
    finally show "TransLam a (\<pi> \<bullet> x) (transform_sumC (PropLam (\<pi> \<bullet> x) (\<pi> \<bullet> e) a, \<pi> \<bullet> e)) = TransLam a x (transform_sumC (PropLam x e a, e))" by simp
  qed
next
case (goal18 a as body a' as' body')
  note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransVar_eqvt[eqvt] TransVar1_eqvt[eqvt]  TransApp_eqvt[eqvt]  TransLam_eqvt[eqvt] TransLet_eqvt[eqvt]

  from supp_eqvt_at[OF goal18(1)]
  have "\<And> x e a. (x, e) \<in> set as \<Longrightarrow> supp (transform_sumC (a, e)) \<subseteq> supp e"
    by (auto simp add: exp_assn.fsupp supp_Pair pure_supp)
  hence supp_map: "\<And>ae. supp (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) ae as) \<subseteq> supp as"
    by (rule supp_map_transform_step)

  from goal18(9)
  have "a' = a" and  "Terms.Let as body = Terms.Let as' body'" by simp_all
  from this(2)
  show ?case
  unfolding `a' = a`
  proof (rule eqvt_let_case)
    have "supp (TransLet a  (PropLetHeap as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap as body a) as) (transform_sumC (PropLetBody as body a, body))) \<subseteq> supp (Terms.Let as body)"
      by (auto simp add: Let_supp supp_Pair pure_supp exp_assn.fsupp
               dest!: set_mp[OF supp_eqvt_at[OF goal18(2)], rotated] set_mp[OF SuppTransLet] set_mp[OF supp_map])
    moreover
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Terms.Let as body"
    ultimately
    have *: "supp \<pi> \<sharp>* TransLet a  (PropLetHeap as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap as body a) as) (transform_sumC (PropLetBody as body a, body))"
      by (auto simp add: fresh_star_def fresh_def)

    have "TransLet a (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (map_transform (\<lambda>x0 x1. (\<pi> \<bullet> transform_sumC) (x0, x1)) (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (\<pi> \<bullet> as)) ((\<pi> \<bullet> transform_sumC) (PropLetBody (\<pi> \<bullet> as) (\<pi> \<bullet> body) a, \<pi> \<bullet> body)) = 
        \<pi> \<bullet> (TransLet a (PropLetHeap as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap as body a) as) (transform_sumC (PropLetBody as body a, body)))"
       by (simp del: Let_eq_iff Pair_eqvt add:  eqvt_at_apply[OF goal18(2)])
    also have "\<dots> = (TransLet a  (PropLetHeap as body a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap as body a) as) (transform_sumC (PropLetBody as body a, body)))"
      by (rule perm_supp_eq[OF *])
    also
    have "map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (\<pi> \<bullet> as)
        = map_transform (\<lambda>x xa. (\<pi> \<bullet> transform_sumC) (x, xa)) (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (\<pi> \<bullet> as)"
        apply (rule map_transform_fundef_cong[OF _ refl refl])
        apply (subst (asm) set_eqvt[symmetric])
        apply (subst (asm) mem_permute_set)
        apply (auto simp add: permute_self  dest: eqvt_at_apply''[OF goal18(1)[where aa = "(- \<pi> \<bullet> a)" for a], where p = \<pi>, symmetric])
        done
    moreover
    have "(\<pi> \<bullet> transform_sumC) (PropLetBody (\<pi> \<bullet> as) (\<pi> \<bullet> body) a, \<pi> \<bullet> body) = transform_sumC (PropLetBody (\<pi> \<bullet> as) (\<pi> \<bullet> body) a, \<pi> \<bullet> body)"
      using eqvt_at_apply''[OF goal18(2), where p = \<pi>] by perm_simp
    ultimately
    show "TransLet a (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap (\<pi> \<bullet> as) (\<pi> \<bullet> body) a) (\<pi> \<bullet> as)) (transform_sumC (PropLetBody (\<pi> \<bullet> as) (\<pi> \<bullet> body) a, \<pi> \<bullet> body)) =
          TransLet a (PropLetHeap as body a)   (map_transform (\<lambda>x0 x1. transform_sumC (x0, x1)) (PropLetHeap as body a) as) (transform_sumC (PropLetBody as body a, body))" by metis
    qed
  qed auto
  nominal_termination by lexicographic_order
end

locale AbstractTransformBound = AbstractAnalProp + supp_bounded_transform  +
  constrains PropApp :: "exp \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> 'a::pure_cont_pt"
  constrains trans :: "'a::pure_cont_pt \<Rightarrow> exp \<Rightarrow> exp"
  assumes TransBound_eqvt: "\<pi> \<bullet> trans = trans"
begin
  sublocale AbstractTransform PropApp PropLam PropLetBody PropLetHeap
      "(\<lambda> a. Var)"
      "(\<lambda> a. Var1)"
      "(\<lambda> a. App)"
      "(\<lambda> a. Terms.Lam)"
      "(\<lambda> a ae \<Gamma> e . Let (map_transform trans ae \<Gamma>) e)"
  proof-
  note PropApp_eqvt[eqvt_raw] PropLam_eqvt[eqvt_raw] PropLetBody_eqvt[eqvt_raw] PropLetHeap_eqvt[eqvt_raw] TransBound_eqvt[eqvt]
  case goal1
  show ?case
  apply default
  apply ((perm_simp, rule)+)[5]
  apply (auto simp add: exp_assn.supp supp_at_base)[1]
  apply (auto simp add: Let_supp supp_Pair supp_at_base dest: set_mp[OF supp_map_transform])[1]
  done
  qed

end


end
