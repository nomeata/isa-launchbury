theory LaunchburyStackedFmapEq
imports LaunchburyStacked LaunchburyStackedFmap
begin

lemma fresh_fmap_of_distinct[simp]:
  "distinctVars (l::('a::fs \<times> 'b::fs) list) \<Longrightarrow> a \<sharp> fmap_of l \<longleftrightarrow> a \<sharp> l"
  apply(induct l rule:distinctVars.induct)
  apply(auto simp add: fresh_Nil fresh_Pair fresh_Cons heapVars_def)
  done

lemma fresh_star_fmap_of_distinct[simp]:
  "distinctVars (l::('a::fs \<times> 'b::fs) list) \<Longrightarrow> a \<sharp>* fmap_of l \<longleftrightarrow> a \<sharp>* l"
  by (metis fresh_fmap_of_distinct fresh_star_def)

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


lemma reds_order_exists:
  assumes "fmap_of h\<Gamma> : x \<mapsto> e : fmap_of h\<Gamma>' \<Down> \<Delta> : x \<mapsto> z : \<Delta>'"
  and "distinctVars (((x,e)#h\<Gamma>')@ h\<Gamma>)"
  obtains h\<Delta> and h\<Delta>'
  where "h\<Gamma> : (x, e) # h\<Gamma>' \<Down> h\<Delta> : (x, z) # h\<Delta>'"
  and "\<Delta> = fmap_of h\<Delta>"
  and "\<Delta>' = fmap_of h\<Delta>'"
  and "distinctVars (((x,z)#h\<Delta>')@h\<Delta>)"
using assms
proof(induct "fmap_of h\<Gamma>" x e "fmap_of h\<Gamma>'" \<Delta> x z \<Delta>' arbitrary: h\<Gamma> h\<Gamma>' thesis rule: LaunchburyStackedFmap.reds.induct)
case (Lambda x y e h\<Gamma> h\<Gamma>' thesis)
  show ?case
  proof (rule Lambda.prems(1))
    show "h\<Gamma> : (x, Lam [y]. e) # h\<Gamma>' \<Down> h\<Gamma> : (x, Lam [y]. e) # h\<Gamma>'"
      by (rule LaunchburyStacked.reds.Lambda)
    show "distinctVars (((x, Lam [y]. e) # h\<Gamma>') @ h\<Gamma>)"
      by fact
  qed (rule refl)+
next
case (Application n \<Delta> x \<Delta>' e y \<Theta> \<Theta>' z' z e' h\<Gamma> h\<Gamma>' thesis)
  have "x \<notin> fst ` set h\<Gamma>'"
    using Application.prems(2)
    by (simp add: distinctVars_Cons distinctVars_append fresh_Pair heapVars_def image_Un)
    
  have "atom n \<sharp> h\<Gamma>"  "atom n \<sharp> h\<Gamma>'" 
    using Application(1) Application.prems(2)
    by (simp_all add: distinctVars_Cons distinctVars_append fresh_Pair)

  have "fmap_of h\<Gamma>'(x f\<mapsto> App (Var n) y) = fmap_of ((x, App (Var n) y) # h\<Gamma>')"
    by simp
  moreover
  have "distinctVars (((n, e) # (x, App (Var n) y) # h\<Gamma>') @ h\<Gamma>)"
    using Application.prems(2) Application(1)
    apply (simp add: distinctVars_Cons distinctVars_append fresh_Pair fresh_at_base)
    by (metis `atom n \<sharp> h\<Gamma>'` `atom n \<sharp> h\<Gamma>` heapVars_not_fresh)
  ultimately
  obtain h\<Delta> h\<Delta>'
    where *: "h\<Gamma> : (n, e) # (x, App (Var n) y) # h\<Gamma>' \<Down> h\<Delta> : (n, Lam [z]. e') # h\<Delta>'"
      and "\<Delta> = fmap_of h\<Delta>" and "\<Delta>' = fmap_of h\<Delta>'" and d: "distinctVars (((n, Lam [z]. e') # h\<Delta>')@h\<Delta>)"
    by (metis Application.hyps(4)[OF refl])
 
  have "h\<Delta>' = (x, App (Var n) y) # h\<Gamma>'"
    by (rule stack_unchanged[OF *])

  have "fmap_delete x \<Delta>' = fmap_of (delete x h\<Delta>')"
    using `\<Delta>' = _` by simp
  moreover have "distinctVars (((x, e'[z::=y]) # delete x h\<Delta>') @ h\<Delta>)"
    using d `h\<Delta>' = _`
    apply (simp add: distinctVars_Cons distinctVars_append )
    by (metis delete_no_there)
  ultimately
  obtain h\<Theta> h\<Theta>'
    where **: "h\<Delta> : (x, e'[z::=y]) # delete x h\<Delta>' \<Down> h\<Theta> : (x, z') # h\<Theta>'"
    and "\<Theta> = fmap_of h\<Theta>" and "\<Theta>' = fmap_of h\<Theta>'" and d2: "distinctVars (((x, z') # h\<Theta>') @ h\<Theta>)"
    by (metis Application.hyps(6)[OF `\<Delta> = _`])

  show ?case
  proof (rule Application.prems(1))
    show "h\<Gamma> : (x, App e y) # h\<Gamma>' \<Down> h\<Theta> : (x, z') # h\<Theta>'"
    proof (rule LaunchburyStacked.reds.Application)
      show "atom n \<sharp> (h\<Gamma>, h\<Gamma>', h\<Delta>, h\<Gamma>', x, e, y, h\<Theta>, (x, z') # h\<Theta>', z)"
        using Application(1) Application.prems(2) d d2 `\<Theta>' = _` `\<Delta> = _` `\<Theta> = _` 
        by (simp add: fresh_Pair fresh_Cons eqvt_fresh_star_cong1[where f = fmap_of, OF fmap_of_eqvt] distinctVars_append distinctVars_Cons)
      show "atom z \<sharp> (h\<Gamma>, h\<Gamma>', h\<Delta>, h\<Gamma>', x, e, y, h\<Theta>, (x, z') # h\<Theta>')"
        using Application(2) Application.prems(2) d d2 `\<Theta>' = _` `\<Delta> = _` `\<Theta> = _` 
        by (simp add: fresh_Pair fresh_Cons eqvt_fresh_star_cong1[where f = fmap_of, OF fmap_of_eqvt] distinctVars_append distinctVars_Cons)
      show "h\<Gamma> : (n, e) # (x, App (Var n) y) # h\<Gamma>' \<Down> h\<Delta> : (n, Lam [z]. e') # (x, App (Var n) y) # h\<Gamma>'"
        by (rule *[unfolded `h\<Delta>' = _`])
      show "h\<Delta> : (x, e'[z::=y]) # h\<Gamma>' \<Down> h\<Theta> : (x, z') # h\<Theta>'"
        using  ** `h\<Delta>' = _` `x \<notin> fst \` set h\<Gamma>'`
        by simp
    qed
    show "\<Theta> = fmap_of h\<Theta>" by fact
    show "\<Theta>' = fmap_of h\<Theta>'" by fact
    show "distinctVars (((x, z') # h\<Theta>') @ h\<Theta>)" by fact
  qed
next
case (Variable y e x \<Delta> z \<Delta>' h\<Gamma> h\<Gamma>' thesis)
  have "fmap_delete y (fmap_of h\<Gamma>) = fmap_of (delete y h\<Gamma>)" by simp
  moreover
  have "fmap_of h\<Gamma>'(x f\<mapsto> Var y) = fmap_of ((x, Var y) # h\<Gamma>')" by simp
  moreover
  have "distinctVars (((y, e) # (x, Var y) # h\<Gamma>') @ delete y h\<Gamma>)"
    using Variable(6) Variable(1)
    by (auto simp add: distinctVars_Cons distinctVars_append heapVars_from_set distinctVars_delete)
  ultimately
  obtain h\<Delta> h\<Delta>' where
    *: "delete y h\<Gamma> : (y, e) # (x, Var y) # h\<Gamma>' \<Down> h\<Delta> : (y, z) # h\<Delta>'"
    and "\<Delta> = fmap_of h\<Delta>" and "\<Delta>' = fmap_of h\<Delta>'" and d: "distinctVars (((y, z) # h\<Delta>') @ h\<Delta>)"
    by (metis Variable.hyps(4))

  have [simp]: "h\<Delta>' = (x, Var y) # h\<Gamma>'"
    by (rule stack_unchanged[OF *])

  have x: "x \<notin> fst ` set h\<Gamma>'"
    using Variable(6)
    by (auto simp add: distinctVars_Cons distinctVars_append heapVars_def)

  show ?case
  proof(rule Variable.prems(1))
    show "h\<Gamma> : (x, Var y) # h\<Gamma>' \<Down> (y, z) # h\<Delta> : (x, z) # tl h\<Delta>'"
    proof(rule LaunchburyStacked.reds.Variable)
      show "(y, e) \<in> set h\<Gamma>"
        using Variable(1,2)
        by (metis lookup_fmap_of map_of_is_SomeD)
      show "delete y h\<Gamma> : (y, e) # (x, Var y) # h\<Gamma>' \<Down> h\<Delta> : (y, z) # (x, Var y) # tl h\<Delta>'"
        using * by simp
    qed
    show "\<Delta>(y f\<mapsto> z) = fmap_of ((y, z) # h\<Delta>)"
      using `\<Delta> = _` by simp
    show "fmap_delete x \<Delta>' = fmap_of (tl h\<Delta>')"
      using `\<Delta>' = _` by (simp add: x)
    show "distinctVars (((x, z) # tl h\<Delta>') @ (y, z) # h\<Delta>)"
      using d
      by (auto simp add: distinctVars_Cons distinctVars_append)
  qed
next
case (Let as x body \<Delta> z \<Delta>' h\<Gamma> h\<Gamma>' thesis)
  have "set (bn as) \<sharp>* (((x, Terms.Let as body) # h\<Gamma>') @ h\<Gamma>)"
    using Let(1) Let(6)
    by (auto simp add: fresh_star_Pair fresh_star_list distinctVars_Cons distinctVars_append)
  hence "heapVars (asToHeap as) \<inter> heapVars (((x, Terms.Let as body) # h\<Gamma>') @ h\<Gamma>) = {}"
    by (rule fresh_assn_distinct)

  have "fmap_of h\<Gamma> f++ fmap_of (asToHeap as) = fmap_of (asToHeap as @ h\<Gamma>)"
    by simp
  moreover
  have "distinctVars (((x, body) # h\<Gamma>') @ (asToHeap as @ h\<Gamma>))"
    using Let(6) Let(2) Let(1) `_ = {}`
    by (auto simp add: distinctVars_Cons distinctVars_append fresh_star_Pair)
  ultimately
  obtain h\<Delta> h\<Delta>'
  where *: "asToHeap as @ h\<Gamma> : (x, body) # h\<Gamma>' \<Down> h\<Delta> : (x, z) # h\<Delta>'"
    and "\<Delta> = fmap_of h\<Delta>" and "\<Delta>' = fmap_of h\<Delta>'" and d: "distinctVars (((x, z) # h\<Delta>') @ h\<Delta>)"
  by (metis Let.hyps(4))

  show ?case
  proof(rule Let.prems(1))
    show "h\<Gamma> : (x, Terms.Let as body) # h\<Gamma>' \<Down> h\<Delta> : (x, z) # h\<Delta>'"
    proof(rule LaunchburyStacked.reds.Let)
      show "asToHeap as @ h\<Gamma> : (x, body) # h\<Gamma>' \<Down> h\<Delta> : (x, z) # h\<Delta>'" by fact
      show "set (bn as) \<sharp>* (h\<Gamma>, x, Terms.Let as body, h\<Gamma>')"
        using Let(1) Let(6)
        by (auto simp add: fresh_star_Pair fresh_star_list distinctVars_Cons distinctVars_append)
      show "distinctVars (asToHeap as)" by fact
    qed
  qed fact+ 
qed

end
