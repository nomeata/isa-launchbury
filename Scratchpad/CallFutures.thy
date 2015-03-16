theory CallFutures
imports Vars "Nominal-Utils" "Set-Cpo"
begin

type_synonym future = "var \<Rightarrow> nat"

definition no_future :: future where [simp]: "no_future v = 0"

definition possible :: "var \<Rightarrow> future \<Rightarrow> bool"
  where "possible v f = (f v > 0)"

inductive_set domF :: "future \<Rightarrow> var set" for f
  where "possible v f \<Longrightarrow> v \<in> domF f"

lemma possible_eqvt[eqvt]: "\<pi> \<bullet> possible v f = possible (\<pi> \<bullet> v) (\<pi> \<bullet> f)"
  unfolding possible_def by simp

definition after :: "var \<Rightarrow> future \<Rightarrow> future"
  where "after v f = (f(v := f v - 1))"

lemma after_eqvt[eqvt]: "\<pi> \<bullet> after v f = after (\<pi> \<bullet> v) (\<pi> \<bullet> f)"
  unfolding after_def by simp

lemma after_swap: "after x (after y f) = after y (after x f)"
  unfolding after_def by auto

definition without :: "var \<Rightarrow> future \<Rightarrow> future"
  where "without v f = (f(v := 0))"

lemma without_eqvt[eqvt]: "\<pi> \<bullet> without v f = without (\<pi> \<bullet> v) (\<pi> \<bullet> f)"
  unfolding without_def by simp

type_synonym futures = "var \<Rightarrow> future set"

definition combine :: "future \<Rightarrow> future \<Rightarrow> future"
  where [simp]: "combine f1 f2 v = f1 v + f2 v"

lemma combine_nofuture[simp]: "combine no_future f = f" by auto
lemma combine_nofuture2[simp]: "combine f no_future = f" by auto

definition future_add :: "future set \<Rightarrow> future set \<Rightarrow> future set"
  where "future_add fs fs' = fs \<union> fs' \<union> {f . \<exists> f1 \<in> fs. \<exists> f2 \<in> fs'. f = combine f1 f2}"

lemma future_add_subset1:
  "fs \<subseteq> future_add fs fs'"
    unfolding future_add_def by auto
lemma future_add_subset2:
  "fs' \<subseteq> future_add fs fs'"
    unfolding future_add_def by auto

lemma future_addE:
  assumes "f \<in> future_add fs fs'"
  obtains "f \<in> fs" | "f \<in> fs'" | f' f'' where "f = combine f' f''" "f' \<in> fs" "f'' \<in> fs'"
  using assms
  unfolding future_add_def by auto

lemma combine_comm: "combine f f' = combine f' f" 
  by (auto simp add: combine_def)

lemma combine_assoc[simp]: "combine f (combine f' f'') = combine (combine f f') f''" 
  by (auto simp add: combine_def)


lemma combine_mem_add_subset[intro]:
  "f \<in> fs \<Longrightarrow> f' \<in> fs' \<Longrightarrow> combine f f' \<in> future_add fs fs'"
  unfolding future_add_def
  by auto

lemma future_add_assoc:
  "future_add fs (future_add fs' fs'') = future_add (future_add fs fs') fs''"
  apply (auto elim!: future_addE 
           intro: set_mp[OF future_add_subset1] set_mp[OF future_add_subset2])
  apply auto
  apply (auto simp add: combine_assoc[symmetric] simp del: combine_assoc)
  done
  
lemma future_add_comm:
  "future_add fs fs' = future_add fs' fs"
  unfolding future_add_def
  apply (auto elim!: future_addE)
  apply (subst combine_comm, auto)+
  done

lemma future_add_twist:
  "future_add fs (future_add fs' fs'') = future_add (future_add fs' fs) fs''"
  by (metis future_add_assoc future_add_comm)
  
(*
definition may_call :: "var \<Rightarrow> future set \<Rightarrow> future set"
  where "may_call v fs = {f . \<exists> f' \<in> fs. \<forall> x. x \<noteq> v \<longrightarrow> f x = f' x}"
*)

definition many_calls :: "var set \<Rightarrow> future set"
  where "many_calls S = {f . \<forall> x. x \<notin> S \<longrightarrow> f x = 0}"

lemma not_future_many_calls[simp]:
  "no_future \<in> many_calls S" by (simp add: many_calls_def)

lemma not_future_upd_many_calls[simp, intro]: 
  "x \<in> S \<Longrightarrow> f \<in> many_calls S \<Longrightarrow> f(x := n) \<in> many_calls S" by (simp add: many_calls_def)

definition may_call :: "var \<Rightarrow> future set \<Rightarrow> future set"
  where "may_call v fs = future_add (many_calls {v}) fs"

lemma may_call_multiple_calls: "(\<exists>f\<in>may_call x fs. Suc 0 < f x') \<longleftrightarrow> x' = x \<or> (\<exists>f\<in>fs. 1 < f x')"
  unfolding may_call_def
  apply rule
  apply (auto elim!: future_addE simp add: many_calls_def  intro: set_mp[OF future_add_subset1] set_mp[OF future_add_subset2])
  apply (rule bexI[where x = "no_future(x:=2)"])
  apply (auto intro: set_mp[OF future_add_subset1] set_mp[OF future_add_subset2])
  done  

lemma future_add_may_call_twist:
  "future_add fs (may_call x fs') = future_add (may_call x fs) fs'"
  unfolding may_call_def by (metis future_add_assoc future_add_comm)

(* http://stackoverflow.com/questions/16603886/inductive-set-with-non-fixed-parameters *)

inductive paths' :: "futures \<Rightarrow> future set \<Rightarrow> var list \<Rightarrow> bool" for G
  where "paths' G current []"
  | "f \<in> current \<Longrightarrow> possible x f \<Longrightarrow> paths' G (future_add {after x f} (G x)) path \<Longrightarrow> paths' G current (x#path)"

definition paths  :: "futures \<Rightarrow> future set \<Rightarrow> var list set" 
  where "paths G current = Collect (paths' G current)"
lemma elim_paths'[pred_set_conv]: "paths' G f p \<longleftrightarrow> p \<in> paths G f" unfolding paths_def by simp

lemmas paths_intros[intro?] = paths'.intros[unfolded elim_paths']
lemmas paths_induct[consumes 1, induct set: paths] = paths'.induct[to_set]
lemmas paths_cases[consumes 1, cases set: paths] = paths'.cases[to_set]
lemmas paths_simpss = paths'.simps[to_set]

lemma possible_no_future[simp]: "possible xa no_future \<longleftrightarrow> False"
  by (auto simp add: possible_def no_future_def)

lemma possible_upd[simp]: "possible x' (f(x := n)) \<longleftrightarrow> (x = x' \<and> n > 0) \<or> (possible x' f \<and> x' \<noteq> x)"
  by (auto simp add: possible_def no_future_def)

lemma after_upd[simp]: "after x (f(x := n)) = f(x := n - 1)"
  by (auto simp add: after_def)

lemma [simp]: "x \<noteq> y \<Longrightarrow> after x (f(y := n)) =( after x f)(y := n)"
  by (auto simp add: after_def)

lemma no_future_upd0[simp]: "no_future(x := 0) = no_future"
  by (auto simp add: no_future_def)


(*
lemma may_call_cont: "cont (may_call v)" sorry
lemmas may_call_cont[cont2cont, simp]
*)

definition restrict_future :: "var set \<Rightarrow> future \<Rightarrow> future"
  where "restrict_future S f x = (if x \<in> S then f x else 0)"


text {* Some tests *}

lemma cons_eq_replicate[simp]: "x'#xs = replicate n x \<longleftrightarrow> x' = x \<and> n > 0 \<and> xs = replicate (n - 1) x"
  by (cases n) auto

lemma snoc_eq_replicate[simp]: "xs @ [x'] = replicate n x  \<longleftrightarrow> x' = x \<and> n > 0 \<and> xs = replicate (n - 1) x"
proof-
  have "xs @ [x'] = replicate n x \<longleftrightarrow> rev (xs @ [x']) = rev (replicate n x)" by (metis rev_rev_ident)
  also have "\<dots> \<longleftrightarrow> rev (xs @ [x']) = replicate n x" by (metis rev_replicate)
  also have "\<dots> \<longleftrightarrow> x'# (rev xs)  = replicate n x" by (metis rev.simps(2) rev_rev_ident)
  also have "\<dots> \<longleftrightarrow> x' = x \<and> n > 0 \<and> rev xs = replicate (n - 1) x" by (rule cons_eq_replicate)
  also have "\<dots> \<longleftrightarrow> x' = x \<and> n > 0 \<and> xs = replicate (n - 1) x" by (metis rev_rev_ident rev_replicate)
  finally show ?thesis.
qed 

lemma [simp]: "replicate n x @ [x'] = replicate n' x \<longleftrightarrow> n' = Suc n \<and> x' = x"
  by auto
(*

lemma
  fixes G current
  assumes [simp]:"G = ((\<lambda> _. {})(x := current))"
  assumes [simp]:"current = {no_future(x := 1)}"
  shows "paths G current = {replicate n x | n. True}"
proof(rule set_eqI, rule)
  fix p
  assume "p \<in> paths G current"
  from  this `current = _` 
  show "p \<in> {replicate n x |n. True}" by (induction) auto
next
  fix p
  assume "p \<in> {replicate n x |n. True}"
  then obtain n where "p = replicate n x" by auto
  thus "p \<in> paths G current"
  by (induction p arbitrary: n)(auto intro: paths_intros)
qed   

lemma
  assumes [simp]: "x\<noteq>y"
  assumes [simp]:"G = ((\<lambda> _. {})(x := current, y := {no_future}))"
  assumes [simp]:"current = {no_future(x := 1), no_future(y := 1)}"
  shows "paths G current = {replicate n x | n. True} \<union> {replicate n x @ [y]| n. True}"
proof(rule set_eqI, rule)
  fix p
  assume "p \<in> paths G current"
  hence "(current = {no_future} \<Longrightarrow> p = [])" and "current = {no_future(x := 1), no_future(y := 1)} \<Longrightarrow> p \<in> {replicate n x | n. True} \<union>  {replicate n x @ [y]| n. True}"
    by induction (auto, arith+)
  with `current = _`
  show "p \<in> {replicate n x | n. True} \<union>  {replicate n x @ [y]| n. True}" by blast
next
  fix p
  {
  fix n
  have "replicate n x \<in> paths G current"
    by (induction n) (auto intro: paths_intros (1) paths_intros(2)[where f = "no_future(x := Suc 0)"])
  moreover
  have "replicate n x @ [y] \<in> paths G current"
    by (induction n) (auto intro: paths_intros(1) paths_intros(2)[where f = "no_future(x := Suc 0)"]  paths_intros(2)[where f = "no_future(y := Suc 0)"])
  moreover
  note calculation
  }
  moreover
  assume  "p \<in> {replicate n x | n. True} \<union>  {replicate n x @ [y]| n. True}"
  ultimately
  show "p \<in> paths G current" by blast
qed
*)

end
