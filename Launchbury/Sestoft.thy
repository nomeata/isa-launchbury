theory Sestoft 
imports Terms Substitution
begin

datatype stack_elem = Arg var | Upd var | Dummy var

instantiation stack_elem :: pt
begin
definition  "\<pi> \<bullet> x = (case x of (Arg v) \<Rightarrow> Arg (\<pi> \<bullet> v) | (Upd v) \<Rightarrow> Upd (\<pi> \<bullet> v) | (Dummy v) \<Rightarrow> Dummy (\<pi> \<bullet> v))"
instance
  by default (auto simp add: permute_stack_elem_def split:stack_elem.split)
end

lemma Arg_eqvt[eqvt]: "\<pi> \<bullet> (Arg v) = Arg (\<pi> \<bullet> v)"
  and Upd_eqvt[eqvt]: "\<pi> \<bullet> (Upd v) = Upd (\<pi> \<bullet> v)"
  and Dummy_eqvt[eqvt]: "\<pi> \<bullet> (Dummy v) = Dummy (\<pi> \<bullet> v)"
  by (auto simp add: permute_stack_elem_def split:stack_elem.split)

lemma supp_Arg[simp]: "supp (Arg v) = supp v"  unfolding supp_def by auto
lemma supp_Upd[simp]: "supp (Upd v) = supp v"  unfolding supp_def by auto
lemma supp_Dummy[simp]: "supp (Dummy v) = supp v"  unfolding supp_def by auto
lemma fresh_Arg[simp]: "a \<sharp> Arg v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Upd[simp]: "a \<sharp> Upd v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Dummy[simp]: "a \<sharp> Dummy v = a \<sharp> v" unfolding fresh_def by auto
lemma fv_Arg[simp]: "fv (Arg v) = fv v"  unfolding fv_def by auto
lemma fv_Upd[simp]: "fv (Upd v) = fv v"  unfolding fv_def by auto

instance stack_elem :: fs  by (default, case_tac x) (auto simp add: finite_supp)

type_synonym stack = "stack_elem list"

fun ap :: "stack \<Rightarrow> var set" where
  "ap [] = {}"
| "ap (Arg x # S) = insert x (ap S)"
| "ap (Upd x # S) = ap S"
| "ap (Dummy x # S) = ap S"
fun upds :: "stack \<Rightarrow> var set" where
  "upds [] = {}"
| "upds (Upd x # S) = insert x (upds S)"
| "upds (Arg x # S) = upds S"
| "upds (Dummy x # S) = upds S"
fun flattn :: "stack \<Rightarrow> var list" where
  "flattn [] = []"
| "flattn (Upd x # S) = x # flattn S"
| "flattn (Arg x # S) = x # flattn S"
| "flattn (Dummy x # S) = x # flattn S"

lemma ups_fv_subset: "upds S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto

lemma fresh_flattn[simp]: "a \<sharp> flattn S \<longleftrightarrow> a \<sharp> S"
  by (induction S rule:flattn.induct) (auto simp add: fresh_Nil fresh_Cons)
lemma fresh_star_flattn[simp]: "a \<sharp>* flattn S \<longleftrightarrow> a \<sharp>* S"
  by (auto simp add: fresh_star_def)

type_synonym conf = "(heap \<times> exp \<times> stack)"


inductive step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  app\<^sub>1:  "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e , Arg x # S)"
| app\<^sub>2:  "(\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> (\<Gamma>, e[y ::= x] , S)"
| var\<^sub>1:  "map_of \<Gamma> x = Some e \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e , Upd x # S)"
| var\<^sub>2:  "x \<notin> domA \<Gamma> \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<Rightarrow> ((x,e)# \<Gamma>, e , S)"
| let\<^sub>1:  "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> (\<Delta>@\<Gamma>, e , S)"

abbreviation steps (infix "\<Rightarrow>\<^sup>*" 50) where "steps \<equiv> step\<^sup>*\<^sup>*"

lemma SmartLet_stepI:
   "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, SmartLet \<Delta> e, S) \<Rightarrow>\<^sup>*  (\<Delta>@\<Gamma>, e , S)"
unfolding SmartLet_def by (auto intro: let\<^sub>1)

lemma lambda_var: "map_of \<Gamma> x = Some e \<Longrightarrow> isLam e  \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* ((x,e) # delete x \<Gamma>, e , S)"
  by (rule rtranclp_trans[OF r_into_rtranclp r_into_rtranclp])
     (auto intro: var\<^sub>1 var\<^sub>2)

text {* An induction rule that skips the annoying case of a lambda taken off the heap *}

inductive boring_step where
  "isLam e \<Longrightarrow> boring_step (\<Gamma>, e, Upd x # S)"
  

lemma step_induction[consumes 2, case_names app\<^sub>1 app\<^sub>2 thunk lamvar var\<^sub>2 let\<^sub>1 refl trans]:
  assumes "c \<Rightarrow>\<^sup>* c'"
  assumes "\<not> boring_step c'"
  assumes app\<^sub>1:  "\<And> \<Gamma> e x S . P (\<Gamma>, App e x, S)  (\<Gamma>, e , Arg x # S)"
  assumes app\<^sub>2:  "\<And> \<Gamma> y e x S . P (\<Gamma>, Lam [y]. e, Arg x # S) (\<Gamma>, e[y ::= x] , S)"
  assumes thunk:  "\<And> \<Gamma> x e S . map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> P (\<Gamma>, Var x, S) (delete x \<Gamma>, e , Upd x # S)"
  assumes lamvar:  "\<And> \<Gamma> x e S . map_of \<Gamma> x = Some e \<Longrightarrow> isLam e \<Longrightarrow> P (\<Gamma>, Var x, S) ((x,e) # delete x \<Gamma>, e , S)"
  assumes var\<^sub>2:  "\<And> \<Gamma> x e S . x \<notin> domA \<Gamma> \<Longrightarrow> isLam e \<Longrightarrow> P (\<Gamma>, e, Upd x # S) ((x,e)# \<Gamma>, e , S)"
  assumes let\<^sub>1:  "\<And> \<Delta> \<Gamma> e S . atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> P (\<Gamma>, Let \<Delta> e, S) (\<Delta>@\<Gamma>, e, S)"
  assumes refl: "\<And> c. P c c"
  assumes trans[trans]: "\<And> c c' c''. c \<Rightarrow>\<^sup>* c' \<Longrightarrow> c' \<Rightarrow>\<^sup>* c'' \<Longrightarrow> P c c' \<Longrightarrow> P c' c'' \<Longrightarrow> P c c''"
  shows "P c c'"
proof-
  from assms(1)
  have "P c c' \<or> (boring_step c' \<and> (\<forall> c''. c' \<Rightarrow> c'' \<longrightarrow> P c c''))"
  proof(induction)
  case base
    have "P c c" by (rule refl)
    thus ?case..
  next
  case (step y z)
    from step(3)
    show ?case
    proof
      assume "P c y"

      note t = trans[OF `c \<Rightarrow>\<^sup>* y` r_into_rtranclp[where r = step, OF `y \<Rightarrow> z`]]
      
      from `y \<Rightarrow> z`
      show ?thesis
      proof (cases)
        case app\<^sub>1 hence "P y z" using assms(3) by metis
        with `P c y` show ?thesis by (metis t)
      next
        case app\<^sub>2 hence "P y z" using assms(4) by metis
        with `P c y` show ?thesis by (metis t)
      next
        case (var\<^sub>1 \<Gamma> x e S)
        show ?thesis
        proof (cases "isLam e")
          case False with var\<^sub>1 have "P y z" using assms(5) by metis
          with `P c y` show ?thesis by (metis t)
        next
          case True
          have *: "y \<Rightarrow>\<^sup>* ((x,e) # delete x \<Gamma>, e , S)" using var\<^sub>1 True lambda_var by metis

          have "boring_step (delete x \<Gamma>, e, Upd x # S)" using True ..
          moreover
          have "P y ((x,e) # delete x \<Gamma>, e , S)" using var\<^sub>1 True assms(6) by metis
          with `P c y` have "P c ((x,e) # delete x \<Gamma>, e , S)" by (rule trans[OF `c \<Rightarrow>\<^sup>* y` *])
          ultimately
          show ?thesis using var\<^sub>1(2,3) True by (auto elim!: step.cases)
        qed
      next
        case var\<^sub>2 hence "P y z" using assms(7) by metis
        with `P c y` show ?thesis by (metis t)
      next
        case let\<^sub>1 hence "P y z" using assms(8) by metis
        with `P c y` show ?thesis by (metis t)
      qed
    next
      assume "boring_step y \<and> (\<forall>c''. y \<Rightarrow> c'' \<longrightarrow> P c c'')"
      with `y \<Rightarrow> z`
      have "P c z" by blast
      thus ?thesis..
    qed
  qed
  with assms(2)
  show ?thesis by auto
qed

end
