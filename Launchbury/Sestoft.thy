theory Sestoft 
imports SestoftConf
begin

inductive step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  app\<^sub>1:  "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e , Arg x # S)"
| app\<^sub>2:  "(\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> (\<Gamma>, e[y ::= x] , S)"
| var\<^sub>1:  "map_of \<Gamma> x = Some e \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e , Upd x # S)"
| var\<^sub>2:  "x \<notin> domA \<Gamma> \<Longrightarrow> isVal e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<Rightarrow> ((x,e)# \<Gamma>, e , S)"
| let\<^sub>1:  "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> (\<Delta>@\<Gamma>, e , S)"
| if\<^sub>1:  "(\<Gamma>, scrut ? e1 : e2, S) \<Rightarrow> (\<Gamma>, scrut, Alts e1 e2 # S)"
| if\<^sub>2:  "(\<Gamma>, Bool b, Alts e1 e2 # S) \<Rightarrow> (\<Gamma>, if b then e1 else e2, S)"

abbreviation steps (infix "\<Rightarrow>\<^sup>*" 50) where "steps \<equiv> step\<^sup>*\<^sup>*"

lemma SmartLet_stepI:
   "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, SmartLet \<Delta> e, S) \<Rightarrow>\<^sup>*  (\<Delta>@\<Gamma>, e , S)"
unfolding SmartLet_def by (auto intro: let\<^sub>1)

lemma lambda_var: "map_of \<Gamma> x = Some e \<Longrightarrow> isVal e  \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* ((x,e) # delete x \<Gamma>, e , S)"
  by (rule rtranclp_trans[OF r_into_rtranclp r_into_rtranclp])
     (auto intro: var\<^sub>1 var\<^sub>2)

text {* An induction rule that skips the annoying case of a lambda taken off the heap *}

thm step.induct[no_vars]

lemma step_induction[consumes 2, case_names app\<^sub>1 app\<^sub>2 thunk lamvar var\<^sub>2 let\<^sub>1 if\<^sub>1 if\<^sub>2 refl trans]:
  assumes "c \<Rightarrow>\<^sup>* c'"
  assumes "\<not> boring_step c'"
  assumes app\<^sub>1:  "\<And> \<Gamma> e x S . P (\<Gamma>, App e x, S)  (\<Gamma>, e , Arg x # S)"
  assumes app\<^sub>2:  "\<And> \<Gamma> y e x S . P (\<Gamma>, Lam [y]. e, Arg x # S) (\<Gamma>, e[y ::= x] , S)"
  assumes thunk:  "\<And> \<Gamma> x e S . map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isVal e \<Longrightarrow> P (\<Gamma>, Var x, S) (delete x \<Gamma>, e , Upd x # S)"
  assumes lamvar:  "\<And> \<Gamma> x e S . map_of \<Gamma> x = Some e \<Longrightarrow> isVal e \<Longrightarrow> P (\<Gamma>, Var x, S) ((x,e) # delete x \<Gamma>, e , S)"
  assumes var\<^sub>2:  "\<And> \<Gamma> x e S . x \<notin> domA \<Gamma> \<Longrightarrow> isVal e \<Longrightarrow> P (\<Gamma>, e, Upd x # S) ((x,e)# \<Gamma>, e , S)"
  assumes let\<^sub>1:  "\<And> \<Delta> \<Gamma> e S . atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> P (\<Gamma>, Let \<Delta> e, S) (\<Delta>@\<Gamma>, e, S)"
  assumes if\<^sub>1:   "\<And>\<Gamma> scrut e1 e2 S. P (\<Gamma>, scrut ? e1 : e2, S) (\<Gamma>, scrut, Alts e1 e2 # S)"
  assumes if\<^sub>2:   "\<And>\<Gamma> b e1 e2 S. P (\<Gamma>, Bool b, Alts e1 e2 # S) (\<Gamma>, if b then e1 else e2, S)"
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
        proof (cases "isVal e")
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
      next
        case if\<^sub>1 hence "P y z" using assms(9) by metis
        with `P c y` show ?thesis by (metis t)
      next
        case if\<^sub>2 hence "P y z" using assms(10) by metis
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
