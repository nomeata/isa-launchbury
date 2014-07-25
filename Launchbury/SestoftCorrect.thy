theory SestoftCorrect
imports Sestoft Launchbury BalancedTraces
begin


fun ap :: "stack \<Rightarrow> var set" where
  "ap [] = {}"
| "ap (Arg x # S) = insert x (ap S)"
| "ap (Upd x # S) = ap S"
fun upds :: "stack \<Rightarrow> var set" where
  "upds [] = {}"
| "upds (Upd x # S) = insert x (upds S)"
| "upds (Arg x # S) = upds S"
fun flattn :: "stack \<Rightarrow> var list" where
  "flattn [] = []"
| "flattn (Upd x # S) = x # flattn S"
| "flattn (Arg x # S) = x # flattn S"
  

lemma fresh_flattn[simp]: "a \<sharp> flattn S \<longleftrightarrow> a \<sharp> S"
  by (induction S rule:flattn.induct) (auto simp add: fresh_Nil fresh_Cons)
lemma fresh_star_flattn[simp]: "a \<sharp>* flattn S \<longleftrightarrow> a \<sharp>* S"
  by (auto simp add: fresh_star_def)

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

  note `L = flattn S`[simp]

  from `map_of \<Gamma> x = Some e`
  have "(\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e, Upd x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, Upd x # S)" by (rule Variable) simp
  also have "\<dots> \<Rightarrow> ((x,z)#\<Delta>, z, S)" using `isLam z` by (rule var\<^sub>2)
  finally show ?case.
next
case (Let as \<Gamma> L body \<Delta> z S)
  from Let(1) Let(4)
  have "atom ` domA as \<sharp>* (\<Gamma>, S)" by (simp add: fresh_star_Pair)
  hence "(\<Gamma>, Terms.Let as body, S) \<Rightarrow> (as@\<Gamma>, body, S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, S)" by (rule Let) fact
  finally show ?case.
qed

type_synonym trace = "conf list"

fun stack :: "conf \<Rightarrow> stack" where "stack (\<Gamma>, e, S) = S"

interpretation traces step.

interpretation balance_trace step  stack
  apply default
  apply (erule step.cases)
  apply auto
  done

lemma lambda_stop:
  assumes "isLam e"
  assumes "bal (\<Gamma>, e, S) T (\<Delta>, z, S)"
  shows "T=[]"
  using assms
  apply -
  apply (erule balE)
  apply (erule trace.cases)
  apply (auto elim: step.cases)
  done
  
lemma lemma_3:
  assumes "bal (\<Gamma>, e, S) T (\<Delta>, z, S)"
  assumes "isLam z"
  shows "\<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z"
using assms
proof(induction T arbitrary: \<Gamma> e S \<Delta> z rule: measure_induct_rule[where f = length])
  case (less T \<Gamma> e S \<Delta> z)
  from `bal (\<Gamma>, e, S) T (\<Delta>, z, S)`
  have "trace (\<Gamma>, e, S) T (\<Delta>, z, S)" and "list_all (\<lambda>c'. S \<lesssim> stack c') T" unfolding bal.simps by auto

  from this(1)
  show ?case
  proof(cases)
  case trace_nil
    from `isLam z` obtain y e' where "z = Lam [y]. e'" by (cases z rule:isLam.cases) auto
    with trace_nil show ?thesis by (auto intro: reds.intros)
  next
  case (trace_cons conf' T')
    from `T = conf' # T'` and `list_all _ _` have "S \<lesssim> stack conf'" by auto
  
    from `(\<Gamma>, e, S) \<Rightarrow> conf'`
    show ?thesis
    proof(cases)
    case (app\<^sub>1 e x)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "bal (\<Gamma>, e, Arg x # S) T\<^sub>1 c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: "bal c\<^sub>4 T\<^sub>2 (\<Delta>, z, S)"
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
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "bal (delete x \<Gamma>, e, Upd x # S) T\<^sub>1 c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: "bal c\<^sub>4 T\<^sub>2 (\<Delta>, z, S)"
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
      have "bal (as @ \<Gamma>, e, S) T' (\<Delta>, z, S)" 
        using trace_cons `conf' = _`  `list_all _ _` by auto
      moreover
      note `isLam z`
      ultimately
      have "as @ \<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z" by (rule less)
      moreover
      from `atom \` domA as \<sharp>* (\<Gamma>, S)`
      have "atom ` domA as \<sharp>* (\<Gamma>, flattn S)" by (auto simp add: fresh_star_Pair)
      ultimately
      show ?thesis unfolding let\<^sub>1  by (rule reds.Let[rotated])
    qed
  qed
qed

end
