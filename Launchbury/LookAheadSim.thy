theory LookAheadSim imports Main
begin

inductive look_ahead :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  for rel :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<triangleright>" 50) and step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Rightarrow>" 50)
  where
    nowI : "x \<triangleright> y \<Longrightarrow> look_ahead rel step x y"
  | laterI : "x \<Rightarrow> x' \<Longrightarrow> (\<And> x'. x \<Rightarrow> x' \<Longrightarrow> look_ahead rel step x' y) \<Longrightarrow> look_ahead rel step x y"

lemma later_svI:
  fixes step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Rightarrow>" 50)
  shows  "single_valuedP (op \<Rightarrow>) \<Longrightarrow> x \<Rightarrow> x' \<Longrightarrow> look_ahead rel step x' y \<Longrightarrow> look_ahead rel step x y"
  by (rule laterI) (auto dest: single_valuedD)

context
  fixes rel :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<triangleright>" 50)
  fixes step1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>1" 50)
  fixes step2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>2" 50)
  assumes single_step: "\<And> x x' y . x \<Rightarrow>\<^sub>1 x' \<Longrightarrow> x \<triangleright> y \<Longrightarrow> \<exists> y'. op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y' \<and> look_ahead rel step1 x' y'"
begin


lemma simulate_with_later:
  assumes "x \<Rightarrow>\<^sub>1 x'"
  assumes "look_ahead rel step1 x y"
  shows "\<exists> y'. op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y' \<and> look_ahead rel step1 x' y'"
using assms(2)
proof(cases)
  case nowI
  thus ?thesis by (rule single_step[OF `x \<Rightarrow>\<^sub>1 x'`])
next
  case laterI
  from laterI(2)[OF assms(1)]
  show ?thesis by blast
qed

lemma simulate_with_later_to_end:
  assumes "op \<Rightarrow>\<^sub>1\<^sup>*\<^sup>* x x'"
  assumes "\<not> Domainp step1 x'"
  assumes "x \<triangleright> y"
  shows "\<exists> y'. op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y' \<and> x' \<triangleright> y'"
proof-
  from `x \<triangleright> y`
  have "look_ahead rel step1 x y"..
  
  from `op \<Rightarrow>\<^sub>1\<^sup>*\<^sup>* x x'` and this
  have "\<exists> y'. op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y' \<and> look_ahead rel step1 x' y'"
  proof(induction)
    case base thus ?case by blast
  next
    case (step x' x'')
    then obtain y' where "op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y'" and "look_ahead op \<triangleright> op \<Rightarrow>\<^sub>1 x' y'" by auto
    
    from `x' \<Rightarrow>\<^sub>1 x''` and `look_ahead op \<triangleright> op \<Rightarrow>\<^sub>1 x' y'`
    have "\<exists>y''. op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y' y'' \<and> look_ahead op \<triangleright> op \<Rightarrow>\<^sub>1 x'' y''" by (rule simulate_with_later)
    with `op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y'`
    show ?case by (metis rtranclpD tranclp_into_rtranclp tranclp_rtranclp_tranclp)
  qed
  then obtain y' where "op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y'" and "look_ahead rel step1 x' y'" by auto
  from `look_ahead rel step1 x' y'` and `\<not> Domainp step1 x'`
  have "x' \<triangleright> y'" by cases auto
  with `op \<Rightarrow>\<^sub>2\<^sup>*\<^sup>* y y'`
  show ?thesis by auto
qed

end

subsection {* Example *}

context
begin

inductive rel :: "nat \<Rightarrow> nat \<Rightarrow> bool" (infix "\<triangleright>" 50)
  where relI: "rel (3 * n) (2 * n)" 
inductive step (infix "\<Rightarrow>" 50)
  where stepI: "n \<le> 299 \<Longrightarrow> step n (Suc n)"

lemma sv_step: "single_valuedP step"
  by (auto intro!: single_valuedI elim: step.cases)

lemma "\<exists> y'. op \<Rightarrow>\<^sup>*\<^sup>* 0 y' \<and> 300 \<triangleright> y'"
proof-
  { fix n
    have "n \<le> 300 \<Longrightarrow> op \<Rightarrow>\<^sup>*\<^sup>* 0 n"
      apply (induction n rule: nat_induct)
      apply (auto)
      by (metis rtranclp.rtrancl_into_rtrancl step.intros)
  }
  hence "op \<Rightarrow>\<^sup>*\<^sup>* 0 300" by auto
  moreover
  have "\<not> Domainp op \<Rightarrow> 300" by (auto elim!: step.cases)
  moreover
  have "0 \<triangleright> 0" using relI[of 0] by auto
  ultimately
  show ?thesis
  proof (rule simulate_with_later_to_end[rotated])
    fix x x' y
    assume "x \<Rightarrow> x'"
    hence "x \<le> 299" and "x' = Suc x" by (auto elim: step.cases)

    assume "x \<triangleright> y"
    then obtain n where "x = 3*n" and "y = 2*n" by (auto elim: rel.cases)

    from `x \<le> 299` and `x = 3*n` have "x < 298" by arith
    
    from `x' = Suc x` and `x < 298` have "x' \<le> 299" and "Suc x' \<le> 299" by auto
    hence "x' \<Rightarrow> Suc x'" and "Suc x' \<Rightarrow> Suc (Suc x')" by (auto intro: stepI)

    have "Suc (Suc x') \<triangleright> Suc (Suc y)"
      unfolding `x' = Suc x` `x = 3*n` `y = 2*n`
      using relI[of "Suc n"] by (metis Suc3_eq_add_3 add_2_eq_Suc mult_Suc_right)
    hence "look_ahead op \<triangleright> op \<Rightarrow> (Suc (Suc x')) (Suc (Suc y))"..
    with `Suc x' \<Rightarrow> Suc (Suc x')`
    have  "look_ahead op \<triangleright> op \<Rightarrow> (Suc x') (Suc (Suc y))" by(rule later_svI[OF sv_step])
    with `x' \<Rightarrow> Suc x'`
    have  "look_ahead op \<triangleright> op \<Rightarrow> x' (Suc (Suc y))" by (rule later_svI[OF sv_step])
    moreover
    from `x \<le> 299` and `x = 3*n` and `y = 2*n` have "y < 298" by arith

    hence "y \<le> 299" and "Suc y \<le> 299" by auto
    hence "y \<Rightarrow> Suc y" and "Suc y \<Rightarrow> Suc (Suc y)" by (auto intro: stepI)
    hence "op \<Rightarrow>\<^sup>*\<^sup>* y (Suc (Suc y))" by auto
    ultimately
    show "\<exists>y'. op \<Rightarrow>\<^sup>*\<^sup>* y y' \<and> look_ahead op \<triangleright> op \<Rightarrow> x' y'" by auto
  qed
qed
end

end
