theory ITree
imports "HOLCF"
begin

default_sort countable

domain ('a::countable) tree' = Node (lazy next' :: "'a discr \<rightarrow> 'a tree'")

type_synonym 'a tree = "'a discr \<rightarrow> 'a tree'"

definition mkt :: "('a \<Rightarrow> 'a tree') \<Rightarrow> 'a tree'"
  where "mkt f = Node\<cdot>(\<Lambda> x. f (undiscr x))"
lemma mkt_cont: "cont (\<lambda> x. mkt x)"
  unfolding mkt_def
  by (intro cont2cont cont_fun)
lemmas cont_compose[OF mkt_cont, cont2cont, simp]

abbreviation tnext ::"'a tree' \<Rightarrow> 'a \<Rightarrow> 'a tree'"
 where "tnext t x \<equiv> next'\<cdot>t\<cdot>(Discr x)"

lemma mkt_not_bot[simp]: "\<not> mkt f = \<bottom>"
  by (auto simp add: mkt_def)

lemma tnext_mkt[simp]: "tnext (mkt f) x = f x"
  by (auto simp add: mkt_def)

fixrec lempty :: "'a::countable tree'"
  where "lempty = mkt (\<lambda> _. \<bottom>)"

context
  fixes x :: "'a::countable"
begin
  fixrec single :: "'a tree'"
    where "single = mkt (\<lambda> x'. if x' = x then lempty else \<bottom>)"

  fixrec many :: "'a tree'"
    where [simp del]: "many = mkt (\<lambda> x'. if x' =  x then many else \<bottom>)"
end

lemma many_not_bot[simp]: "many x \<noteq> \<bottom>"
  by (subst many.simps) simp

lemma tnext_many[simp]: "tnext (many x) x' = (if x' =  x then many x else \<bottom>)"
  by (subst many.simps) simp

fixrec lanything :: "'a::countable tree'"
  where "lanything = Node\<cdot>(\<Lambda> x'. lanything)"

inductive paths_aux :: "'a tree' \<Rightarrow> 'a list \<Rightarrow> bool"
  where "paths_aux t []"
      | "tnext t x = t' \<Longrightarrow> t' \<noteq> \<bottom> \<Longrightarrow> paths_aux t' l \<Longrightarrow> paths_aux t (x#l)"
definition paths :: "'a tree' \<Rightarrow> 'a list set" 
  where "paths t = Collect (paths_aux t)"
lemma elim_paths_aux[pred_set_conv]: "paths_aux t p \<longleftrightarrow> p \<in> paths t" unfolding paths_def by simp
lemmas paths_intros[intro?] = paths_aux.intros[unfolded elim_paths_aux]
lemmas paths_induct[consumes 1, induct set: paths] = paths_aux.induct[to_set]
lemmas paths_cases[consumes 1, cases set: paths] = paths_aux.cases[to_set]
lemmas paths_simpss = paths_aux.simps[to_set]

lemma "replicate n x \<in> paths (many x)"
 by(induction n) (auto intro: paths_intros )

lemma "p \<in> paths (many x) \<Longrightarrow> (\<forall> x' \<in> set p. x' = x)"
  by (induction "many x" p arbitrary: x rule: paths_induct)
     (auto  split: if_splits)

fun op_option :: "('a::cpo \<rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
  where "op_option f (Some x) (Some y) = Some (f\<cdot>x\<cdot>y)"
      | "op_option f (Some x) None     = Some x"
      | "op_option f None     (Some y) = Some y"
      | "op_option f None     None     = None"

fixrec or' :: "'a tree' \<rightarrow> 'a tree' \<rightarrow> 'a tree'"
 where "or'\<cdot>t1\<cdot>t2 = mkt (\<lambda> x. or'\<cdot>(tnext t1 x)\<cdot>(tnext t2 x))"
print_theorems

lemma or'_bot: "f \<noteq> \<bottom> \<Longrightarrow> or'\<cdot>\<bottom>\<cdot>f \<sqsubseteq> f"
  apply (induction arbitrary: f rule: or'.induct)
  apply auto
  apply (case_tac f)
  apply simp
  apply (simp add: mkt_def)
  apply (rule cfun_belowI)
  apply simp
  
  

  apply (subst or'.simps)
  apply (simp del: or'.simps)


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
