theory SestoftCorrect
imports Sestoft Launchbury
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
  hence "(\<Gamma>, Let as body, S) \<Rightarrow> (as@\<Gamma>, body, S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, S)" by (rule Let) fact
  finally show ?case.
qed

type_synonym trace = "conf list"

(*
inductive trace :: "conf \<Rightarrow> trace \<Rightarrow> conf \<Rightarrow> bool"  where
  trace_nil[iff]: "trace conf [] conf"
| trace_cons[intro]: "trace conf' T end \<Longrightarrow> conf \<Rightarrow> conf' \<Longrightarrow> trace conf (conf'#T) end"

lemma build_trace:
  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow> \<exists> T. trace c T c'"
proof(induction rule: converse_rtranclp_induct)
  have "trace c' [] c'"..
  thus "\<exists>T. trace c' T c'"..
next
  fix y z
  assume "y \<Rightarrow> z"
  assume "\<exists>T. trace z T c'"
  then obtain T where "trace z T c'"..
  with `y \<Rightarrow> z`
  have "trace y (z#T) c'" by auto
  thus "\<exists>T. trace y T c'" by blast
qed

lemma destruct_trace:  "trace c T c' \<Longrightarrow> c \<Rightarrow>\<^sup>* c'"
  by (induction rule:trace.induct) auto

definition extends :: "stack \<Rightarrow> stack \<Rightarrow> bool" (infix "\<lesssim>" 50) where
  "S \<lesssim> S' = (\<exists> S''. S' = S'' @ S)"

fun stack :: "conf \<Rightarrow> stack" where "stack (\<Gamma>, e, S) = S"

fun bal :: "conf \<Rightarrow> trace \<Rightarrow> conf \<Rightarrow> bool" where
  "bal c T c' = (trace c T c' \<and> (list_all (\<lambda>c'. stack c \<lesssim> stack c') T \<and> stack c' = stack c))"
lemma bal_consE:
  assumes "bal c\<^sub>1 (c\<^sub>2 # T) c\<^sub>5"
  assumes "length (stack c\<^sub>2)
  obtains T\<^sub>1 

*)



(*
lemma bal_trace[case_names empty app var "let"]:
  assumes "bal (\<Gamma>, e, S) T (\<Delta>, z, S)"
  obtains
    "T = []" and "\<Delta> = \<Gamma>" and "z = e"
  | x f y e' T\<^sub>1 T\<^sub>2
   where "e = App f x"
    and "bal (\<Gamma>, e, Arg x # S) T\<^sub>1 (\<Delta>, Lam [y]. e', Arg x # S)"
    and "bal (\<Delta>, e'[y::=x], S) T\<^sub>2 c'"
    and "T = (\<Gamma>, e, Arg x # S) # T\<^sub>1 @  (\<Delta>, e'[y::=x], S) # T\<^sub>2"
  | \<Gamma> x S  \<Delta> y e' T\<^sub>1 T\<^sub>2
   where "c = (\<Gamma>, Var x, S)"
    and "map_of \<Gamma> x = Some e"
    and "bal (delete x \<Gamma>, e, Upd x # S) T\<^sub>1 (\<Delta>, z, Upd x # S)"
    and "bal ((x,z)#\<Delta>, z, S) T\<^sub>2 c'"
    and "T = (delete x \<Gamma>, e, Upd x # S) # T\<^sub>1 @ ((x,z)#\<Delta>, z, S) # T\<^sub>2"
  | \<Gamma> as e' S T\<^sub>1
   where "c = (\<Gamma>, Let as e', S)"
    and "atom ` domA as \<sharp>* \<Gamma>"
    and "atom ` domA as \<sharp>* S"
    and "bal (as @ \<Gamma>, e', S) T\<^sub>1 c'"
    and "T = (as @ \<Gamma>, e', S) # T\<^sub>1"
sorry


lemma lemma_3:
  assumes "bal (\<Gamma>, e, S) T (\<Delta>, z, S)"
  assumes "isLam z"
  shows "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
thm measure_induct_rule
using assms
proof(induction T arbitrary: \<Gamma> e S \<Delta> z rule: measure_induct_rule[where f = length])
  case (less T \<Gamma> e S \<Delta> z)
  from `bal (\<Gamma>, e, S) T (\<Delta>, z, S)`
  show ?case
  proof(induction rule: bal_trace)
  case empty
    from `isLam z` obtain y e' where "z = Lam [y]. e'" by (cases z rule:isLam.cases) auto
    with empty show ?case by (auto intro: reds.intros)
  next 
  case (app \<Gamma> x e S \<Delta> y e' T\<^sub>1 T\<^sub>2)
    from `T = (\<Gamma>, e, Arg x # S) # T\<^sub>1 @ (\<Delta>, e'[y::=x], S) # T\<^sub>2`
    have l1: "length T\<^sub>1 < length T" and l2: "length T\<^sub>2 < length T" by auto
    note IH1 = less(1)[OF l1 app(2) isLam_Lam]
    note IH2 = less(1)[OF _ app(3)]
*)  
    
      

lemma lemma_3:
  assumes "bal (\<Gamma>, e, S) T (\<Delta>, z, S)"
  assumes "isLam z"
  shows "\<Gamma> : e \<Down>\<^bsub>flattn S\<^esub> \<Delta> : z"
thm measure_induct_rule
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
      
      show ?thesis sorry
    next
      case (app\<^sub>2 y e x S')
      from `conf' =_` `S = _ # S'` `S \<lesssim> stack conf'`
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
      case (var\<^sub>1 x e)
      show ?thesis sorry
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
        using trace_cons `conf' = _`  `list_all _ _`  by simp
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
