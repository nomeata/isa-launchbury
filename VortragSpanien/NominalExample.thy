theory NominalExample imports Main Nominal2 "../Launchbury/Nominal-Utils" begin

atom_decl var

term permute
thm supp_def
thm fresh_def
find_theorems fresh permute
thm Abs1_eq_iff(3)

nominal_datatype exp =
  Const int
| Var var
| Ass v::var i::int body::exp  binds v in body

lemma "Ass a 0 (Var a) = Ass b 0 (Var b)" by auto

nominal_primrec eval :: "(var \<times> int) list \<Rightarrow> exp \<Rightarrow> int" where
  "eval _ (Const i) = i" |
  "eval l (Var v) = (case map_of l v of Some i \<Rightarrow> i | None \<Rightarrow> 0)" |
  "atom v \<sharp> l \<Longrightarrow> eval l (Ass v i b) = eval ((v,i)#l) b"
unfolding eqvt_def eval_graph_aux_def
(* Equivariance of the defintion *)
apply (rule, simp)
apply (perm_simp)
(* Invariant (no invariant present *)
apply rule
(* Exhaustiveness *)
apply (case_tac x)
apply (rule_tac y = b and c = a in exp.strong_exhaust)
apply (auto simp add: fresh_star_def fresh_Pair)[3]
(* Well-definedness *)
apply auto[5]
(* Last case very ugly, unfortunately. *)
apply (auto simp add: Abs1_eq_iff fresh_Pair)
apply (drule_tac p = "(v \<leftrightarrow> va)" in eqvt_at_apply')
apply (auto simp add: permute_pure fresh_Pair fresh_perm flip_fresh_fresh)
done

termination (eqvt) by lexicographic_order
thm eval.induct[no_vars]

inductive all_zeros where
  AZConst: "all_zeros (Const 0)" |
  AZVar: "all_zeros (Var n)" |
  AZAss: "all_zeros e \<Longrightarrow> all_zeros (Ass v 0 e)"

equivariance all_zeros

nominal_inductive all_zeros avoids AZAss: "v"
  by (auto simp add: fresh_star_def fresh_Pair pure_fresh)


lemma "all_zeros e \<Longrightarrow> ran (map_of l) \<subseteq> {0} \<Longrightarrow> eval l e = 0"
proof (induct arbitrary: l rule: all_zeros.induct)
  case AZConst
  show "eval l (Const 0) = 0" by auto
next
  case (AZVar n)
  thus "eval l (Var n) = 0" by (auto split:option.splits simp add: ran_def)
next
  case (AZAss e v)
    obtain v'::var where "atom v' \<sharp> l" and "atom v' \<sharp> v" by (metis obtain_fresh fresh_Pair)
    from `ran (map_of l) \<subseteq> {0}`
    have "ran (map_of ((v,0)#l)) \<subseteq> {0}" by (auto simp add: ran_def)
    hence "eval ((v, 0) # l) e = 0" by (rule AZAss.hyps)
    thus "eval l (Ass v 0 e) = 0"
      (* Need "atom v \<sharp> l" to proceed, but that is not guaranteed! *)
oops

thm all_zeros.induct all_zeros.strong_induct

lemma "all_zeros e \<Longrightarrow> ran (map_of l) \<subseteq> {0} \<Longrightarrow> eval l e = 0"
proof (nominal_induct avoiding: l rule: all_zeros.strong_induct)
  case AZConst
  show "eval l (Const 0) = 0" by auto
next
  case (AZVar n)
  thus "eval l (Var n) = 0" by (auto split:option.splits simp add: ran_def)
next
  case (AZAss e v)
    from `ran (map_of l) \<subseteq> {0}`
    have "ran (map_of ((v,0)#l)) \<subseteq> {0}" by (auto simp add: ran_def)
    hence "eval ((v, 0) # l) e = 0" by (rule AZAss.hyps)
    thus "eval l (Ass v 0 e) = 0" using `atom v \<sharp> l` by simp
qed

end
