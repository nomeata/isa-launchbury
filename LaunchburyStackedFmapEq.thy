theory LaunchburyStackedFmapEq
imports LaunchburyStacked LaunchburyStackedFmap
begin

lemma reds_order_irrelevant:
 assumes "\<Gamma> : (x, e) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Delta>'"
 and "distinctVars (((x,e) # \<Gamma>') @ \<Gamma>)"
 shows "fmap_of \<Gamma> : x \<mapsto> e : fmap_of \<Gamma>' \<Down> fmap_of \<Delta> : x \<mapsto> z : fmap_of \<Delta>'"
proof-
  {
  fix \<Gamma> \<Gamma>' \<Delta> \<Delta>'
  have "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars (\<Gamma>' @ \<Gamma>) \<Longrightarrow>
        fmap_of \<Gamma> : fst (hd \<Gamma>') \<mapsto> snd (hd \<Gamma>') : fmap_of (tl \<Gamma>') \<Down> fmap_of \<Delta> : fst (hd \<Delta>') \<mapsto> snd (hd \<Delta>') : fmap_of (tl \<Delta>')"
  proof(induct rule:LaunchburyStacked.reds_distinct_ind)
  case (Lambda x y e \<Gamma>' \<Gamma>) show ?case by (auto intro: LaunchburyStackedFmap.reds.intros)
  next
  case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z e')
    obtain x' z' \<Theta>'' where [simp]: "\<Theta>' = (x', z') # \<Theta>''"
      by (metis Application(10) distinct_redsD1 neq_Nil_conv prod.exhaust stack_not_empty)
    hence [simp]: "x' = x"
      by (metis Application(10) distinct_redsD1 fst_conv hd.simps stack_same_head)
    have [simp]: "x \<notin> fst ` set \<Delta>'"
       using Application(6)
       by (simp add: distinctVars_append distinctVars_Cons heapVars_def image_Un)

    show ?case
    apply simp
    proof (rule LaunchburyStackedFmap.reds.Application[where n = n and z = z])
      show "atom n \<sharp> (fmap_of \<Gamma>, fmap_of \<Gamma>', fmap_of \<Delta>, fmap_delete x (fmap_of \<Delta>'(x f\<mapsto> App (Var n) y)), x, e, y, fmap_of \<Theta>, fmap_of \<Theta>'', z', z)"
        using Application(1)
        by (simp add: fmap_delete_noop fresh_Pair eqvt_fresh_cong1[where f = fmap_of, OF fmap_of_eqvt] eqvt_fresh_cong3[where f = fmap_upd, OF fmap_upd_eqvt] exp_assn.fresh fresh_Cons)
      show "atom z \<sharp> (fmap_of \<Gamma>, fmap_of \<Gamma>', fmap_of \<Delta>, fmap_delete x (fmap_of \<Delta>'(x f\<mapsto> App (Var n) y)), x, e, y, fmap_of \<Theta>, fmap_of \<Theta>'', z')"
        using Application(2)
        by (simp add: fmap_delete_noop fresh_Pair eqvt_fresh_cong1[where f = fmap_of, OF fmap_of_eqvt] eqvt_fresh_cong3[where f = fmap_upd, OF fmap_upd_eqvt] exp_assn.fresh fresh_Cons)
      show "fmap_of \<Gamma> : n \<mapsto> e : fmap_of \<Gamma>'(x f\<mapsto> App (Var n) y) \<Down> fmap_of \<Delta> : n \<mapsto> Lam [z]. e' : fmap_of \<Delta>'(x f\<mapsto> App (Var n) y)"
        using Application(9)
        by simp
      show "fmap_of \<Delta> : x \<mapsto> e'[z::=y] : fmap_delete x (fmap_of \<Delta>'(x f\<mapsto> App (Var n) y)) \<Down> fmap_of \<Theta> : x \<mapsto> z' : fmap_of \<Theta>''"
        using Application(11)
        by (simp add: fmap_delete_noop)
    qed
  next
  case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
    have [simp]:"delete x \<Delta>' = \<Delta>'"
      using Variable(4) by (simp add: distinctVars_append distinctVars_Cons heapVars_def image_Un)
    show ?case
    apply simp
    proof (rule LaunchburyStackedFmap.reds.Variable[where \<Delta>' = "fmap_of \<Delta>'(x f\<mapsto> Var y)" and x = x, simplified])
      show "y \<in> fdom (fmap_of \<Gamma>)"
        using Variable(1) apply simp by (metis fst_conv imageI)
      show "Some e = lookup (fmap_of \<Gamma>) y"
        using Variable(1) Variable(2) by (auto simp add: distinctVars_append distinctVars_Cons)
      show "fmap_delete y (fmap_of \<Gamma>) : y \<mapsto> e : fmap_of \<Gamma>'(x f\<mapsto> Var y) \<Down> fmap_of \<Delta> : y \<mapsto> z : fmap_of \<Delta>'(x f\<mapsto> Var y)"
        using Variable(7) by simp
    qed
  next
  case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
    obtain x' z' \<Delta>'' where [simp]: "\<Delta>' = (x', z') # \<Delta>''"
      by (metis Let(6) distinct_redsD1 neq_Nil_conv prod.exhaust stack_not_empty)
    hence [simp]: "x' = x"
      by (metis Let(6) distinct_redsD1 fst_conv hd.simps stack_same_head)
    show ?case
    apply simp
    proof (rule LaunchburyStackedFmap.reds.Let)
    show "set (bn as) \<sharp>* (fmap_of \<Gamma>, x, Terms.Let as body, fmap_of \<Gamma>')"
      using Let(1)
      by (simp add: fresh_star_Pair eqvt_fresh_star_cong1[where f = fmap_of, OF fmap_of_eqvt])
    show "distinctVars (asToHeap as)" by (rule local.Let.hyps(2))
    show "fmap_of \<Gamma> f++ fmap_of (asToHeap as) : x \<mapsto> body : fmap_of \<Gamma>' \<Down> fmap_of \<Delta> : x \<mapsto> z' : fmap_of \<Delta>''"
      using Let(7)
      by simp
    qed
  qed
  }
  from this[OF assms]
  show ?thesis by simp
qed


end
