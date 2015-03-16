theory LTree
imports Main  "$AFP/Coinductive/Coinductive_List"
begin

codatatype (lset: 'a) ltree = Node (lnext : "'a \<Rightarrow> 'a ltree option")

primcorec lempty :: "'a ltree"
  where "lnext lempty = (\<lambda> _ . None)"

primcorec single :: "'a \<Rightarrow> 'a ltree"
  where "lnext (single x) = (\<lambda> _ . None)(x := Some lempty)"

primcorec many :: "'a \<Rightarrow> 'a ltree"
  where "lnext (many x) = (\<lambda> x'. if x' = x then Some (many x) else None)"

primcorec lanything :: "'a ltree"
  where "lnext lanything = (\<lambda> _ . Some lanything)"

coinductive lpaths_aux :: "'a ltree \<Rightarrow> 'a llist \<Rightarrow> bool"
  where "lpaths_aux t LNil"
      | "lnext t x = Some t' \<Longrightarrow> lpaths_aux t' l \<Longrightarrow> lpaths_aux t (LCons x l)"

definition lpaths :: "'a ltree \<Rightarrow> 'a llist set" 
  where "lpaths t = Collect (lpaths_aux t)"
lemma elim_lpaths_aux[pred_set_conv]: "lpaths_aux t p \<longleftrightarrow> p \<in> lpaths t" unfolding lpaths_def by simp
lemmas lpaths_intros[intro?] = lpaths_aux.intros[unfolded elim_lpaths_aux]
lemmas lpaths_coinduct[consumes 1, coinduct set: lpaths] = lpaths_aux.coinduct[to_set]
lemmas lpaths_cases[consumes 1, cases set: lpaths] = lpaths_aux.cases[to_set]
lemmas lpaths_simpss = lpaths_aux.simps[to_set]

lemma "repeat x \<in> lpaths (many x)"
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
primcorec lor :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
  where "lnext (lor t1 t2) = (\<lambda> x. op_option lor (lnext t1 x) (lnext t2 x))"
*)
primcorec lor :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
  where "lnext (lor t1 t2) = (\<lambda> x.
           case (lnext t1 x) of Some t1' \<Rightarrow> (case lnext t2 x of Some t2' \<Rightarrow> Some (lor t1' t2') | None \<Rightarrow> Some t1')
                              | None     \<Rightarrow> lnext t2 x)"

lemma lor_simp:  "lnext (lor t1 t2) x =  op_option lor (lnext t1 x) (lnext t2 x)"
  by (cases "lnext t1 x", case_tac [!] "lnext t2 x") auto


primcorec land_aux :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
      and land :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
  where "(land_aux t1 t2) = Node (\<lambda> x. case (lnext t1 x) of Some t1' \<Rightarrow> Some (land t1' t2) | None \<Rightarrow> None)"
       |"(land t1 t2) = lor (land_aux t1 t2) (land_aux t2 t1)"


(*
primcorec land :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
   where "(land t1 t2) = lor (Node (\<lambda> x. case (lnext t1 x) of Some t1' \<Rightarrow> Some (land t1' t2) | None \<Rightarrow> None)) (Node (\<lambda> x. case (lnext t1 x) of Some t1' \<Rightarrow> Some (land t1' t2) | None \<Rightarrow> None))"
*)

primcorec land :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
   where "lnext (land t1 t2) = (\<lambda> x.
      case (lnext t1 x) of Some t1' \<Rightarrow> (case lnext t2 x of Some t2' \<Rightarrow> Some (lor (land t1' t2) (land t1 t2')) | None \<Rightarrow> Some (land t1' t2))
                         | None     \<Rightarrow> (case lnext t2 x of Some t2' \<Rightarrow> Some (land t1 t2')                     | None \<Rightarrow> None))"

primcorec land :: "'a ltree \<Rightarrow> 'a ltree \<Rightarrow> 'a ltree"
   where "lnext (land t1 t2) = map_option (\<lambda> (x,y). (land x y, land x y)) o (\<lambda> x.
      case (lnext t1 x) of Some t1' \<Rightarrow> (case lnext t2 x of Some t2' \<Rightarrow> Some (lor t1' t1, lor t2 t2') | None \<Rightarrow> Some (t1', t2))
                         | None     \<Rightarrow> (case lnext t2 x of Some t2' \<Rightarrow> Some (t1, t2')                | None \<Rightarrow> None))"


end
