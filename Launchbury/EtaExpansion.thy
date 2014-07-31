theory EtaExpansion
imports Sestoft
begin

definition fresh_var :: "exp \<Rightarrow> var" where
  "fresh_var e = (SOME v. v \<notin> fv e)"

lemma fresh_var_not_free:
  "fresh_var e \<notin>  fv e"
proof-
  obtain v :: var where "atom v \<sharp> e" by (rule obtain_fresh)
  hence "v \<notin> fv e" by (metis fv_not_fresh)
  thus ?thesis unfolding fresh_var_def by (rule someI)
qed

lemma fresh_var_fresh[simp]:
  "atom (fresh_var e) \<sharp> e"
  by (metis fresh_var_not_free fv_not_fresh)

lemma fresh_var_subst[simp]:
  "e[fresh_var e::=x] = e"
  by (metis fresh_var_fresh subst_fresh_noop)

fun eta_expand :: "nat \<Rightarrow> exp \<Rightarrow> exp" where
   "eta_expand 0 e = e"
|  "eta_expand (Suc n) e = (Lam [fresh_var e]. eta_expand n (App e (fresh_var e)))"

lemma eta_expand_eqvt[eqvt]:
  "\<pi> \<bullet> (eta_expand n e) = eta_expand (\<pi> \<bullet> n) (\<pi> \<bullet> e)"
  apply (induction n arbitrary: e \<pi>)
  apply (auto simp add: fresh_Pair permute_pure)
  apply (metis fresh_at_base_permI fresh_at_base_permute_iff fresh_var_fresh subst_fresh_noop subst_swap_same)
  done

lemma change_Lam_Variable:
  assumes "y' \<noteq> y \<Longrightarrow> atom y' \<sharp> (e,  y)"
  shows   "Lam [y]. e =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)"
proof(cases "y' = y")
  case True thus ?thesis by simp
next
  case False
  from assms[OF this]
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e) = Lam [y]. e"
    by -(rule flip_fresh_fresh, (simp add: fresh_Pair)+)
  moreover
  have "(y \<leftrightarrow> y') \<bullet> (Lam [y]. e) = Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)"
    by simp
  ultimately
  show "Lam [y]. e =  Lam [y']. ((y \<leftrightarrow> y') \<bullet> e)" by (simp add: fresh_Pair)
qed

lemma subst_eta_expand: "(eta_expand n e)[x ::= y] = eta_expand n (e[x ::= y])"
proof (induction n arbitrary: e)
case 0 thus ?case by simp
next
case (Suc n)
  obtain z :: var where "atom z \<sharp> (e, fresh_var e, x, y)" by (rule obtain_fresh)
  
  have "(eta_expand (Suc n) e)[x::=y] = (Lam [fresh_var e]. eta_expand n (App e (fresh_var e)))[x::=y]" by simp
  also have "\<dots> = (Lam [z]. eta_expand n (App e z))[x::=y]"
    apply (subst change_Lam_Variable[where y' = z])
    using `atom z \<sharp> _`
    by (auto simp add: fresh_Pair eta_expand_eqvt pure_fresh permute_pure flip_fresh_fresh intro!: eqvt_fresh_cong2[where f = eta_expand, OF eta_expand_eqvt])
  also have "\<dots> = Lam [z]. (eta_expand n (App e z))[x::=y]"
    using `atom z \<sharp> _` by simp
  also have "\<dots> = Lam [z]. eta_expand n (App e z)[x::=y]" unfolding Suc.IH..
  also have "\<dots> = Lam [z]. eta_expand n (App e[x::=y] z)"
    using `atom z \<sharp> _` by simp
  also have "\<dots> = Lam [fresh_var (e[x::=y])]. eta_expand n (App e[x::=y] (fresh_var (e[x::=y])))"
    apply (subst change_Lam_Variable[where y' = "fresh_var (e[x::=y])"])
    using `atom z \<sharp> _`
    by (auto simp add: fresh_Pair eqvt_fresh_cong2[where f = eta_expand, OF eta_expand_eqvt] pure_fresh eta_expand_eqvt  flip_fresh_fresh subst_pres_fresh simp del: exp_assn.eq_iff)
  also have "\<dots> = eta_expand (Suc n) e[x::=y]" by simp
  finally show ?case.
qed

theorem eta_expandsion_correct:
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

end    
