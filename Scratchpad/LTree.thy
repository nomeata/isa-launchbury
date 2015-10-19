theory LTree
imports Main  "$AFP/Coinductive/Coinductive_List"
begin

codatatype (lset: 'a) tree = Node (nxt : "'a \<Rightarrow> 'a tree option")

primcorec empty :: "'a tree"
  where "nxt empty = (\<lambda> _ . None)"

primcorec single :: "'a \<Rightarrow> 'a tree"
  where "nxt (single x) = (\<lambda> _ . None)(x := Some empty)"

primcorec many :: "'a \<Rightarrow> 'a tree"
  where "nxt (many x) = (\<lambda> x'. if x' = x then Some (many x) else None)"

primcorec anything :: "'a tree"
  where "nxt anything = (\<lambda> _ . Some anything)"

coinductive paths_aux :: "'a tree \<Rightarrow> 'a llist \<Rightarrow> bool"
  where "paths_aux t LNil"
      | "nxt t x = Some t' \<Longrightarrow> paths_aux t' l \<Longrightarrow> paths_aux t (LCons x l)"

definition paths :: "'a tree \<Rightarrow> 'a llist set" 
  where "paths t = Collect (paths_aux t)"
lemma elim_paths_aux[pred_set_conv]: "paths_aux t p \<longleftrightarrow> p \<in> paths t" unfolding paths_def by simp
lemmas paths_intros[intro?] = paths_aux.intros[unfolded elim_paths_aux]
lemmas paths_coinduct[consumes 1, coinduct set: paths] = paths_aux.coinduct[to_set]
lemmas paths_cases[consumes 1, cases set: paths] = paths_aux.cases[to_set]
lemmas paths_simpss = paths_aux.simps[to_set]

lemma "repeat x \<in> paths (many x)"
  apply (coinduction)
  apply (rule disjI2)
  apply auto
  apply (rule exI[where x = "repeat x"])
  apply auto
  apply (rule iterates)
  done

fun op_option :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
  where "op_option f (Some x) (Some y) = Some (f x y)"
      | "op_option f (Some x) None     = Some x"
      | "op_option f None     (Some y) = Some y"
      | "op_option f None     None     = None"
(*
primcorec or :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where "nxt (or t1 t2) = (\<lambda> x. op_option or (nxt t1 x) (nxt t2 x))"
*)
primcorec or :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where "nxt (or t1 t2) = (\<lambda> x.
           case (nxt t1 x) of Some t1' \<Rightarrow> (case nxt t2 x of Some t2' \<Rightarrow> Some (or t1' t2') | None \<Rightarrow> Some t1')
                              | None     \<Rightarrow> nxt t2 x)"

lemma or_simp:  "nxt (or t1 t2) x =  op_option or (nxt t1 x) (nxt t2 x)"
  by (cases "nxt t1 x", case_tac [!] "nxt t2 x") auto

(*
primcorec and_aux :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
      and and :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where "(and_aux t1 t2) = Node (\<lambda> x. case (nxt t1 x) of Some t1' \<Rightarrow> Some (and t1' t2) | None \<Rightarrow> None)"
       |"(and t1 t2) = or (and_aux t1 t2) (and_aux t2 t1)"

primcorec and :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
   where "(and t1 t2) = or (Node (\<lambda> x. case (nxt t1 x) of Some t1' \<Rightarrow> Some (and t1' t2) | None \<Rightarrow> None)) (Node (\<lambda> x. case (nxt t1 x) of Some t1' \<Rightarrow> Some (and t1' t2) | None \<Rightarrow> None))"

primcorec and :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
   where "nxt (and t1 t2) = (\<lambda> x.
      case (nxt t1 x) of Some t1' \<Rightarrow> (case nxt t2 x of Some t2' \<Rightarrow> Some (or (and t1' t2) (and t1 t2')) | None \<Rightarrow> Some (and t1' t2))
                         | None     \<Rightarrow> (case nxt t2 x of Some t2' \<Rightarrow> Some (and t1 t2')                     | None \<Rightarrow> None))"

primcorec and :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
   where "nxt (and t1 t2) = map_option (\<lambda> (x,y). (and x y, and x y)) o (\<lambda> x.
      case (nxt t1 x) of Some t1' \<Rightarrow> (case nxt t2 x of Some t2' \<Rightarrow> Some (or t1' t1, or t2 t2') | None \<Rightarrow> Some (t1', t2))
                         | None     \<Rightarrow> (case nxt t2 x of Some t2' \<Rightarrow> Some (t1, t2')                | None \<Rightarrow> None))"
*)

end
