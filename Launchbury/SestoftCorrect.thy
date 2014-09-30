theory SestoftCorrect
imports Sestoft Launchbury BalancedTraces
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

  from `map_of \<Gamma> x = Some e`
  have "(\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e, Upd x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, Upd x # S)" by (rule Variable) simp
  also have "\<dots> \<Rightarrow> ((x,z)#\<Delta>, z, S)" using `x \<notin> domA \<Delta>` `isLam z` by (rule var\<^sub>2)
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
  assumes "isLam e"
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
  
lemma lemma_3:
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
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
  
    from `(\<Gamma>, e, S) \<Rightarrow> conf'`
    show ?thesis
    proof(cases)
    case (app\<^sub>1 e x)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(\<Gamma>, e, Arg x # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: " c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  `bal _ T _`[unfolded app\<^sub>1 trace_cons]]) (simp, rule)

      from `T = _` `T' = _` have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto

      from prem1 have "stack c\<^sub>3 =  Arg x # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note `c\<^sub>3 \<Rightarrow> c\<^sub>4`
      ultimately
      obtain \<Delta>' y e' where "c\<^sub>3 = (\<Delta>', Lam [y]. e', Arg x # S)" and "c\<^sub>4 = (\<Delta>', e'[y ::= x], S)"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)
      
      from less(1)[OF `length T\<^sub>1 < length T` prem1[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`] isLam_Lam]
      have "\<Gamma> : e \<Down>\<^bsub>x # (flattn S)\<^esub> \<Delta>' : Lam [y]. e'" by simp
      moreover
      from less(1)[OF `length T\<^sub>2 < length T` prem2[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`] `isLam z`]
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
      obtain \<Delta>' z' where "c\<^sub>3 = (\<Delta>', z', Upd x # S)" and "c\<^sub>4 = ((x,z')#\<Delta>', z', S)" and "isLam z'"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      from `isLam z'` and prem2[unfolded `c\<^sub>4 = _`]
      have "T\<^sub>2 = []" by (rule lambda_stop)
      with prem2 `c\<^sub>4 = _`
      have "z' = z" and "\<Delta> = (x,z)#\<Delta>'" by auto
          
      from less(1)[OF `length T\<^sub>1 < length T` prem1[unfolded `c\<^sub>3 = _` `c\<^sub>4 = _`  `z' = _`] `isLam z`]
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
      note `isLam z`
      ultimately
      have "as @ \<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z" by (rule less)
      moreover
      from `atom \` domA as \<sharp>* \<Gamma>`  `atom \` domA as \<sharp>* S`
      have "atom ` domA as \<sharp>* (\<Gamma>, flattn S)" by (auto simp add: fresh_star_Pair)
      ultimately
      show ?thesis unfolding let\<^sub>1  by (rule reds.Let[rotated])
    qed
  qed
qed

lemma dummy_stack_extended:
  "set S \<subseteq>  Dummy ` UNIV \<Longrightarrow> x \<notin> Dummy ` UNIV \<Longrightarrow> (S \<lesssim> x # S') \<longleftrightarrow>  S \<lesssim> S'"
  apply (auto simp add: extends_def)
  apply (case_tac S'')
  apply auto
  done

lemma[simp]: "Arg x \<notin> range Dummy"  "Upd x \<notin> range Dummy" by auto

lemma dummy_stack_balanced:
  assumes "set S \<subseteq> Dummy ` UNIV"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
  obtains T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
proof-
  from build_trace[OF assms(2)]
  obtain T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"..
  moreover
  hence "\<forall> c'\<in>set T. stack (\<Gamma>, e, S) \<lesssim> stack c'"
    by(rule conjunct1[OF traces_list_all]) (auto elim: step.cases simp add: dummy_stack_extended[OF `set S \<subseteq> Dummy \` UNIV`])
  ultimately
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
    by (rule balI) simp
  thus ?thesis by (rule that)
qed

end
