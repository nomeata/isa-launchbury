theory EtaExpansionSestoft
imports EtaExpansion Sestoft
begin

theorem eta_expansion_correct:
  assumes "set T \<subseteq> range Arg"
  shows "(\<Gamma>, eta_expand (length T) e, T@S) \<Rightarrow>\<^sup>* (\<Gamma>, e, T@S)"
using assms
proof(induction T arbitrary: e)
  case Nil show ?case by simp
next
  case (Cons se T)
  from Cons(2) obtain x where "se = Arg x" by auto

  from Cons have prem: "set T \<subseteq> range Arg" by simp
  
  have "(\<Gamma>, eta_expand (Suc (length T)) e, Arg x # T @ S) = (\<Gamma>, Lam [fresh_var e]. eta_expand (length T) (App e (fresh_var e)), Arg x # T @ S)" by simp
  also have "\<dots> \<Rightarrow> (\<Gamma>, (eta_expand (length T) (App e (fresh_var e)))[fresh_var e ::= x], T @ S)" by (rule app\<^sub>2)
  also have "\<dots> = (\<Gamma>, (eta_expand (length T) (App e x)), T @ S)" unfolding subst_eta_expand by simp
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Gamma>, App e x, T @ S)" by (rule Cons.IH[OF prem])
  also have "\<dots> \<Rightarrow> (\<Gamma>, e, Arg x # T @ S)"  by (rule app\<^sub>1)
  finally show ?case using `se = _` by simp
qed

fun arg_prefix :: "stack \<Rightarrow> nat" where
  "arg_prefix [] = 0"
| "arg_prefix (Arg x # S) = Suc (arg_prefix S)"
| "arg_prefix (Upd x # S) = 0"
| "arg_prefix (Dummy x # S) = 0"

theorem eta_expansion_correct':
  assumes "n \<le> arg_prefix S"
  shows "(\<Gamma>, eta_expand n e, S) \<Rightarrow>\<^sup>* (\<Gamma>, e, S)"
proof-
  from assms
  have "set (take n S) \<subseteq> range Arg" and "length (take n S) = n"
    apply (induction S arbitrary: n rule: arg_prefix.induct)
    apply auto
    apply (case_tac n, auto)+
    done
  hence "S = take n S @ drop n S" by (metis append_take_drop_id)
  with eta_expansion_correct[OF `_ \<subseteq> _`] `length _ = _`
  show ?thesis by metis
qed
 
definition eta_expand_heap :: "(var \<Rightarrow> nat) \<Rightarrow> heap \<Rightarrow> heap"
  where "eta_expand_heap f \<Gamma> = map_ran (\<lambda> x e. eta_expand (f x) e) \<Gamma>"

lemma eta_expand_heap_Nil[simp]: 
  "eta_expand_heap exp [] = []"
  unfolding eta_expand_heap_def by simp
lemma eta_expand_heap_Cons[simp]: 
  "eta_expand_heap exp ((x, e) # \<Gamma>) = (x, eta_expand (exp x) e) # eta_expand_heap exp \<Gamma>"
  unfolding eta_expand_heap_def by simp
lemma eta_expand_heap_append[simp]:
  "eta_expand_heap exp (\<Delta> @ \<Gamma>) = eta_expand_heap exp \<Delta> @ eta_expand_heap exp \<Gamma>"
  by (induction \<Delta>) auto

lemma fresh_eta_expand_heap[simp]: "a \<sharp> eta_expand_heap exp \<Gamma> \<longleftrightarrow> a \<sharp> \<Gamma>"
  by (induction \<Gamma>) (auto simp add: fresh_Cons fresh_Pair)

theorem bound_eta_expansion_correct:
  fixes exp :: "var \<Rightarrow> nat"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S')"
  assumes "\<not> boring_step (\<Delta>, z, S')"
  assumes "\<And> x e'. e = Var x \<Longrightarrow> map_of \<Gamma> x = Some e' \<Longrightarrow> (if isLam e' then exp x \<le> arg_prefix S else exp x = 0)"
  assumes "exp ` (- domA \<Gamma>) \<subseteq> {0}"
  shows "(eta_expand_heap exp \<Gamma>, e, S) \<Rightarrow>\<^sup>* (eta_expand_heap exp \<Delta>, z, S')"
using assms
proof(induction "(\<Gamma>, e, S)" "(\<Delta>, z, S')" arbitrary: \<Gamma> e S \<Delta> z S'  rule: step_induction)
case (thunk \<Gamma> x e S)
  from thunk.prems thunk.hyps
  have "exp x = 0" by auto
  hence "eta_expand (exp x) e = e" by simp
   
  from `map_of \<Gamma> x = Some e`
  have "map_of (eta_expand_heap exp \<Gamma>) x = Some (eta_expand (exp x) e)"
    unfolding eta_expand_heap_def by (metis  map_ran_conv option.simps(9))
  hence "(eta_expand_heap exp \<Gamma>, Var x, S) \<Rightarrow> (delete x (eta_expand_heap exp \<Gamma>), e, Upd x # S)"
    unfolding `eta_expand (exp x) e = e`
    by (rule step.var\<^sub>1)
  also have "delete x (eta_expand_heap exp \<Gamma>) = eta_expand_heap exp (delete x \<Gamma>)" 
    by (simp add: eta_expand_heap_def map_ran_delete)
  finally
  show "(eta_expand_heap exp \<Gamma>, Var x, S) \<Rightarrow>\<^sup>* (eta_expand_heap exp (delete x \<Gamma>), e, Upd x # S)"..
next
case (lamvar \<Gamma> x e S)
  from lamvar.prems lamvar.hyps
  have "exp x \<le> arg_prefix S" by auto

  from `map_of \<Gamma> x = Some e`
  have "map_of (eta_expand_heap exp \<Gamma>) x = Some (eta_expand (exp x) e)"
    unfolding eta_expand_heap_def by (metis map_ran_conv option.simps(9))
  hence "(eta_expand_heap exp \<Gamma>, Var x, S) \<Rightarrow> (delete x (eta_expand_heap exp \<Gamma>), eta_expand (exp x) e, Upd x # S)"
    by (rule step.var\<^sub>1)
  hence "(eta_expand_heap exp \<Gamma>, Var x, S) \<Rightarrow>\<^sup>* (delete x (eta_expand_heap exp \<Gamma>), eta_expand (exp x) e, Upd x # S)"..
  also have "\<dots> \<Rightarrow> ((x, eta_expand (exp x) e) # delete x (eta_expand_heap exp \<Gamma>), eta_expand (exp x) e, S)"
    using isLam_eta_expand(1)[OF `isLam _`] by (auto intro: var\<^sub>2)
  also have "\<dots> \<Rightarrow>\<^sup>* ((x, eta_expand (exp x) e) # delete x (eta_expand_heap exp \<Gamma>), e, S)"
     by (rule eta_expansion_correct') fact
  also have "delete x (eta_expand_heap exp \<Gamma>) = eta_expand_heap exp (delete x \<Gamma>)" 
    by (simp add: eta_expand_heap_def map_ran_delete)
  finally
  show ?case by simp
next
case (let\<^sub>1 \<Delta> \<Gamma> S e)
  from fresh_distinct[OF let\<^sub>1(1)] let\<^sub>1(4)
  have "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> exp x = 0" by auto
  hence "eta_expand_heap exp \<Delta> = \<Delta>" by (induction \<Delta>) auto
  with let\<^sub>1
  show ?case by (fastforce intro: step.intros simp add: fresh_star_def )
next
case (refl)
  show ?case..
next
case trans
  thus ?case 
oops

end
