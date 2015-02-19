theory SestoftCorrect
imports BalancedTraces Launchbury Sestoft
begin


lemma lemma_2:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and "L = flattn S"
  shows "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
using assms
proof(induction arbitrary: S  rule:reds.induct)
  case (Lambda \<Gamma> x e L)
  show ?case..
next
  case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  note `L = flattn S`[simp]
  
  have "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e, Arg x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, Lam [y]. e', Arg x# S)" by (rule Application) simp
  also have "\<dots> \<Rightarrow> (\<Delta>, e'[y ::= x], S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Theta>, z, S)" by (rule Application) simp
  finally show ?case.
next
case (Variable \<Gamma> x e L \<Delta> z S)
  have "isLam z"
  proof-
    from result_evaluated_fresh[OF Variable(2)]
    obtain y e' where "z = Lam [y]. e'" by blast
    thus ?thesis by simp
  qed

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all

  note `L = flattn S`[simp]

  from `isLam z` have "isVal z" by (induction z rule:exp_induct) auto

  from `map_of \<Gamma> x = Some e`
  have "(\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e, Upd x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, Upd x # S)" by (rule Variable) simp
  also have "\<dots> \<Rightarrow> ((x,z)#\<Delta>, z, S)" using `x \<notin> domA \<Delta>` `isVal z` by (rule var\<^sub>2)
  finally show ?case.
next
case (Let as \<Gamma> L body \<Delta> z S)
  from Let(1) Let(4)
  have "atom ` domA as \<sharp>* \<Gamma>" and "atom ` domA as \<sharp>* S" by (auto simp add: fresh_star_Pair)
  hence "(\<Gamma>, Terms.Let as body, S) \<Rightarrow> (as@\<Gamma>, body, S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, S)" by (rule Let) fact
  finally show ?case.
qed

type_synonym trace = "conf list"

fun stack :: "conf \<Rightarrow> stack" where "stack (\<Gamma>, e, S) = S"
                 
interpretation traces step.

abbreviation trace_syn ("_ \<Rightarrow>\<^sup>*\<^bsub>_\<^esub> _" [50,50,50] 50) where "trace_syn \<equiv> trace"

lemma conf_trace_induct_final[consumes 1, case_names trace_nil trace_cons]:
  "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> final \<Longrightarrow> (\<And> \<Gamma> e S. final = (\<Gamma>, e, S) \<Longrightarrow> P \<Gamma> e S [] (\<Gamma>, e, S)) \<Longrightarrow> (\<And>\<Gamma> e S T \<Gamma>' e' S'. (\<Gamma>', e', S') \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> final \<Longrightarrow> P \<Gamma>' e' S' T final \<Longrightarrow> (\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S') \<Longrightarrow> P \<Gamma> e S ((\<Gamma>', e', S') # T) final) \<Longrightarrow> P \<Gamma> e S T final"
  by (induction "(\<Gamma>, e, S)" T final arbitrary: \<Gamma> e S rule: trace_induct_final) auto

interpretation balance_trace step  stack
  apply default
  apply (erule step.cases)
  apply auto
  done

abbreviation bal_syn ("_ \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>_\<^esub> _" [50,50,50] 50) where "bal_syn \<equiv> bal"

lemma lambda_stop:
  assumes "isVal e"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
  shows "T=[]"
  using assms
  apply -
  apply (erule balE)
  apply (erule trace.cases)
  apply simp
  apply auto
  apply (auto elim!: step.cases)
  done

nominal_function bool_free :: "exp \<Rightarrow> bool" where
    "bool_free (Lam [x]. e) \<longleftrightarrow> bool_free e"
  | "bool_free (Var x) \<longleftrightarrow> True"
  | "bool_free (App e x) \<longleftrightarrow> bool_free e"
  | "bool_free (Terms.Let \<Gamma> e) \<longleftrightarrow> (\<forall> (x, e) \<in> set \<Gamma>. bool_free e) \<and> bool_free e"
  | "bool_free (Bool b) \<longleftrightarrow> False"
  | "bool_free (scrut ? e\<^sub>1 : e\<^sub>2) \<longleftrightarrow> False"
proof-
case goal1 thus ?case
  unfolding bool_free_graph_aux_def eqvt_def 
  apply rule
  apply perm_simp
  apply rule
  done
next
case goal3 thus ?case
  by (metis Terms.Let_def exp_assn.exhaust(1) heapToAssn_asToHeap)
next
case (goal4 x e x' e')
  from goal4(5)
  show ?case
  proof (rule eqvt_lam_case)
    fix \<pi> :: perm
    assume "supp \<pi> \<sharp>* Lam [x]. e"
      
    have "bool_free_sumC (\<pi> \<bullet> e) = \<pi> \<bullet> bool_free_sumC e"
        by (simp add: pemute_minus_self eqvt_at_apply'[OF goal4(1)])
    also have "\<dots> = bool_free_sumC e" by (simp add: permute_pure)
    finally show  "bool_free_sumC (\<pi> \<bullet> e) = bool_free_sumC e".
  qed
next
case (goal19 as body as' body')
  from goal19(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
  
    from goal19(2,4) have eqvt_at1: "eqvt_at bool_free_sumC body" by auto

    assume assm: "supp \<pi> \<sharp>* Let as body"
    
    have "(\<forall> (x,e)\<in>set (\<pi> \<bullet> as). bool_free_sumC e) \<longleftrightarrow> - \<pi> \<bullet> (\<forall> (x,e)\<in>set (\<pi> \<bullet> as). bool_free_sumC e)"
      by (simp add: permute_pure unpermute_def)
    also have "\<dots> = (\<forall> (x,e)\<in>set as. (- \<pi> \<bullet> bool_free_sumC) e)"
      by perm_simp (simp add: pemute_minus_self)
    also have "\<dots> = (\<forall> (x,e)\<in>set as. bool_free_sumC e)"
      apply (rule ball_cong[OF refl])
      apply (rule prod.case_cong[OF refl])
      apply (rule eqvt_at_apply)
      apply (metis goal19(1))
      done
    finally
    have "(\<forall> (x,e)\<in>set (\<pi> \<bullet> as). bool_free_sumC e) \<longleftrightarrow> (\<forall> (x,e)\<in>set as. bool_free_sumC e)".
    moreover
    have "bool_free_sumC (\<pi> \<bullet> body) \<longleftrightarrow>  bool_free_sumC body" 
      by (metis (full_types) True_eqvt eqvt_at1  eqvt_at_apply' eqvt_bound)
    ultimately
    show "((\<forall>a\<in>set (\<pi> \<bullet> as). case a of (x, x0) \<Rightarrow> bool_free_sumC x0) \<and> bool_free_sumC (\<pi> \<bullet> body)) =
         ((\<forall>a\<in>set as. case a of (x, x0) \<Rightarrow> bool_free_sumC x0) \<and> bool_free_sumC body)" by simp
  qed
qed auto
nominal_termination (eqvt) by lexicographic_order

lemma bool_free_SmartLet[simp]:
  "bool_free (SmartLet \<Gamma> e) \<longleftrightarrow> (\<forall> (x, e) \<in> set \<Gamma>. bool_free e) \<and> bool_free e"
by (auto simp add: SmartLet_def)

 
lemma Ball_subst[simp]:
  "(\<forall>p\<in>set (\<Gamma>[y::h=x]). f p) \<longleftrightarrow> (\<forall>p\<in>set \<Gamma>. case p of (z,e) \<Rightarrow> f (z, e[y::=x]))"
  by (induction \<Gamma>) auto

lemma [simp]: "bool_free e[y::=x] \<longleftrightarrow> bool_free e"
  by (nominal_induct e avoiding: x y rule: exp_strong_induct_set) (auto  simp add: fresh_star_Pair)

inductive bool_free_stack :: "stack \<Rightarrow> bool" where
  "bool_free_stack []"
  | "bool_free_stack S \<Longrightarrow> bool_free_stack (Upd x # S)"
  | "bool_free_stack S \<Longrightarrow> bool_free_stack (Arg x # S)"
  | "bool_free_stack S \<Longrightarrow> bool_free_stack (Dummy x # S)"

inductive_simps bool_free_stack_simps: "bool_free_stack []"  "bool_free_stack (s # S)"

fun bool_free_conf :: "conf \<Rightarrow> bool" where
  "bool_free_conf (\<Gamma>, e, S) \<longleftrightarrow> (\<forall> (x, e) \<in> set \<Gamma>. bool_free e) \<and> bool_free e \<and> bool_free_stack S"

lemma step_bool_free:
  "c1 \<Rightarrow> c2 \<Longrightarrow> bool_free_conf c1 \<Longrightarrow> bool_free_conf c2"
  by (cases rule: step.cases) (auto simp add: bool_free_stack_simps dest!: set_mp[OF set_delete_subset] map_of_is_SomeD)
  
lemma step_star_bool_free:
  assumes  "c \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> c'"
  assumes "bool_free_conf c"
  shows "bool_free_conf c'"
using assms by (induction) (auto dest: step_bool_free)

lemma bal_star_bool_free:
  assumes  "c \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> c'"
  assumes "bool_free_conf c"
  shows "bool_free_conf c'"
using assms by (metis bal.simps step_star_bool_free)


lemma lemma_3:
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
  assumes "bool_free_conf (\<Gamma>, e, S)"
  assumes "isLam z"
  shows "\<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z"
using assms
proof(induction T arbitrary: \<Gamma> e S \<Delta> z rule: measure_induct_rule[where f = length])
  case (less T \<Gamma> e S \<Delta> z)
  from `(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)`
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)" and "\<forall> c'\<in>set T. S \<lesssim> stack c'" unfolding bal.simps by auto

  from this(1)
  show ?case
  proof(cases)
  case trace_nil
    from `isLam z` obtain y e' where "z = Lam [y]. e'" by (cases z rule:isLam.cases) auto
    with trace_nil show ?thesis by (auto intro: reds.intros)
  next
  case (trace_cons conf' T')
    from `T = conf' # T'` and `\<forall> c'\<in>set T. S \<lesssim> stack c'` have "S \<lesssim> stack conf'" by auto

    note step_bool_free[OF `(\<Gamma>, e, S) \<Rightarrow> conf'`  `bool_free_conf (\<Gamma>, _, S)`]

    from `(\<Gamma>, e, S) \<Rightarrow> conf'`
    show ?thesis
    proof(cases)
    case (app\<^sub>1 e x)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(\<Gamma>, e, Arg x # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: " c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  `bal _ T _`[unfolded app\<^sub>1 trace_cons]]) (simp, rule)

      from `T = _` `T' = _` have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto

      note bal_star_bool_free[OF prem1 `bool_free_conf conf'`[unfolded app\<^sub>1]]
      note step_bool_free[OF `c\<^sub>3 \<Rightarrow> c\<^sub>4` this]

      from prem1 have "stack c\<^sub>3 =  Arg x # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note `c\<^sub>3 \<Rightarrow> c\<^sub>4`
      ultimately
      obtain \<Delta>' y e' where "c\<^sub>3 = (\<Delta>', Lam [y]. e', Arg x # S)" and "c\<^sub>4 = (\<Delta>', e'[y ::= x], S)"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      
      from less(1)[OF `length T\<^sub>1 < length T` prem1[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`] `bool_free_conf conf'`[unfolded app\<^sub>1] isLam_Lam]
      have "\<Gamma> : e \<Down>\<^bsub>x # (flattn S)\<^esub> \<Delta>' : Lam [y]. e'" by simp
      moreover
      from less(1)[OF `length T\<^sub>2 < length T` prem2[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`]  `bool_free_conf c\<^sub>4`[unfolded `c\<^sub>4 = _`] `isLam z`]
      have "\<Delta>' : e'[y::=x] \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z" by simp
      ultimately
      show ?thesis unfolding app\<^sub>1
        by (rule reds_ApplicationI)
    next
    case (app\<^sub>2 y e x S')
      from `conf' =_` `S = _ # S'` `S \<lesssim> stack conf'`
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
    case (var\<^sub>1 x e)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(delete x \<Gamma>, e, Upd x # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: "c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  `bal _ T _`[unfolded var\<^sub>1 trace_cons]]) (simp, rule)
      
      from `T = _` `T' = _` have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto


      from prem1 have "stack c\<^sub>3 = Upd x # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note `c\<^sub>3 \<Rightarrow> c\<^sub>4`
      ultimately
      obtain \<Delta>' z' where "c\<^sub>3 = (\<Delta>', z', Upd x # S)" and "c\<^sub>4 = ((x,z')#\<Delta>', z', S)" and "isVal z'"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      from `isVal z'` and prem2[unfolded `c\<^sub>4 = _`]
      have "T\<^sub>2 = []" by (rule lambda_stop)
      with prem2 `c\<^sub>4 = _`
      have "z' = z" and "\<Delta> = (x,z)#\<Delta>'" by auto
          
      from less(1)[OF `length T\<^sub>1 < length T` prem1[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`  `z' = _`] `bool_free_conf conf'`[unfolded var\<^sub>1]  `isLam z`]
      have "delete x \<Gamma> : e \<Down>\<^bsub>x # flattn S\<^esub> \<Delta>' : z" by simp
      with `map_of _ _ = _`
      show ?thesis unfolding var\<^sub>1(1) `\<Delta> = _` by rule
    next
    case (var\<^sub>2 x S')
      from `conf' = _` `S = _ # S'` `S \<lesssim> stack conf'`
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
    case (let\<^sub>1 as e)
      from `T = conf' # T'` have "length T' < length T" by auto
      moreover
      have "(as @ \<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T'\<^esub> (\<Delta>, z, S)" 
        using trace_cons `conf' = _`  `\<forall> c'\<in>set T. S \<lesssim> stack c'` by fastforce
      moreover
      note `bool_free_conf conf'`[unfolded let\<^sub>1]
      moreover
      note `isLam z`
      ultimately
      have "as @ \<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z" by (rule less)
      moreover
      from `atom \` domA as \<sharp>* \<Gamma>`  `atom \` domA as \<sharp>* S`
      have "atom ` domA as \<sharp>* (\<Gamma>, flattn S)" by (auto simp add: fresh_star_Pair)
      ultimately
      show ?thesis unfolding let\<^sub>1  by (rule reds.Let[rotated])
    next
    case (if\<^sub>1)
      with `bool_free_conf (\<Gamma>, e, S)`
      have False by simp
      thus ?thesis..
   next
    case (if\<^sub>2)
      with `bool_free_conf (\<Gamma>, e, S)`
      have False by simp
      thus ?thesis..
    qed
  qed
qed

lemma dummy_stack_extended:
  "set S \<subseteq>  Dummy ` UNIV \<Longrightarrow> x \<notin> Dummy ` UNIV \<Longrightarrow> (S \<lesssim> x # S') \<longleftrightarrow>  S \<lesssim> S'"
  apply (auto simp add: extends_def)
  apply (case_tac S'')
  apply auto
  done

lemma[simp]: "Arg x \<notin> range Dummy"  "Upd x \<notin> range Dummy"   "Alts e\<^sub>1 e\<^sub>2 \<notin> range Dummy" by auto

lemma dummy_stack_balanced:
  assumes "set S \<subseteq> Dummy ` UNIV"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
  obtains T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
proof-
  from build_trace[OF assms(2)]
  obtain T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"..
  moreover
  hence "\<forall> c'\<in>set T. stack (\<Gamma>, e, S) \<lesssim> stack c'"
    by (rule conjunct1[OF traces_list_all])
       (auto elim: step.cases simp add: dummy_stack_extended[OF `set S \<subseteq> Dummy \` UNIV`])
  ultimately
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
    by (rule balI) simp
  thus ?thesis by (rule that)
qed

end
