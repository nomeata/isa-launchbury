theory "Env-HOLCF"
  imports Env "HOLCF-Utils"
begin

subsubsection {* Continuity and finite maps *}

lemma  fmap_add_belowI:
  assumes "\<And> a. a \<in> S \<Longrightarrow> y a \<sqsubseteq> z a"
  and "\<And> a. a \<notin> S \<Longrightarrow> x a \<sqsubseteq> z a"
  shows  "x f++\<^bsub>S\<^esub> y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fun_belowI)
  apply (case_tac "xa \<in> S")
  apply auto
  done

lemma fmap_add_cont1: "cont (\<lambda> x. x f++\<^bsub>S\<^esub> m)"
  by (rule cont2cont_lambda) (auto simp add: fmap_add_def)

lemma fmap_add_cont2: "cont (\<lambda> x. m f++\<^bsub>S\<^esub> x)"
  by (rule cont2cont_lambda) (auto simp add: fmap_add_def)

lemma fmap_add_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. f x f++\<^bsub>S\<^esub> g x)"
by (rule cont_apply[OF assms(1) fmap_add_cont1 cont_compose[OF fmap_add_cont2 assms(2)]])

lemma fmap_add_mono:
  assumes "x1 \<sqsubseteq> (x2 :: 'a\<Colon>type \<Rightarrow> 'b\<Colon>cpo)"
  assumes "y1 \<sqsubseteq> y2"
  shows "x1 f++\<^bsub>S\<^esub> y1 \<sqsubseteq> x2 f++\<^bsub>S\<^esub> y2"
by (rule below_trans[OF cont2monofunE[OF fmap_add_cont1 assms(1)] cont2monofunE[OF fmap_add_cont2 assms(2)]])

lemma fun_upd_belowI:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> z \<sqsubseteq> \<rho>' z" 
  assumes "y \<sqsubseteq> \<rho>' x"
  shows  "\<rho>(x := y) \<sqsubseteq> \<rho>'"
  apply (rule fun_belowI)
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fun_upd_below_fmap_deleteI:
  assumes "fmap_delete x \<rho> \<sqsubseteq> fmap_delete x \<rho>'" 
  assumes "y \<sqsubseteq> \<rho>' x"
  shows  "\<rho>(x := y) \<sqsubseteq> \<rho>'"
  using assms
  apply (auto intro!: fun_upd_belowI   simp add: fmap_delete_def)
  by (metis fun_belowD fun_upd_other)

lemma fun_upd_belowI2:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> z \<sqsubseteq> \<rho>' z" 
  assumes "\<rho> x \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x := y)"
  apply (rule fun_belowI)
  using assms by auto

lemma fmap_restr_belowI:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> (m1 f|` S) x \<sqsubseteq> (m2 f|` S) x"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
  apply (rule fun_belowI)
  by (metis assms below_bottom_iff lookup_fmap_restr_not_there)

lemma fmap_restr_below_itself:
  shows "m f|` S \<sqsubseteq> m"
  apply (rule fun_belowI)
  apply (case_tac "x \<in> S")
  apply auto
  done  

lemma fmap_restr_cont:  "cont (fmap_restr S)"
  apply (rule cont2cont_lambda)
  apply (case_tac "y \<in> S")
  apply (auto simp add: assms)
  done


lemma fmap_restr_belowD:
  assumes "m1 f|` S \<sqsubseteq> m2 f|` S"
  assumes "x \<in> S"
  shows "m1 x \<sqsubseteq> m2 x"
  using fun_belowD[OF assms(1), where x = x] assms(2) by simp

lemma fmap_restr_eqD:
  assumes "m1 f|` S = m2 f|` S"
  assumes "x \<in> S"
  shows "m1 x = m2  x"
  by (metis assms(1) assms(2) lookup_fmap_restr)

lemma fmap_restr_below_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' \<sqsubseteq> m2 f|` S'"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
using assms
by (auto intro!: fmap_restr_belowI dest: fmap_restr_belowD)

lemma fmap_restr_eq_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' = m2 f|` S'"
  shows "m1 f|` S = m2 f|` S"
using assms
by (metis fmap_restr_fmap_restr le_iff_inf)

lemma  fmap_add_below_restrI:
  assumes " x f|` (-S) \<sqsubseteq> z f|` (-S)"
  and "y f|` S \<sqsubseteq> z f|` S"
  shows  "x f++\<^bsub>S\<^esub> y \<sqsubseteq> z"
using assms
by (auto intro: fmap_add_belowI dest:fmap_restr_belowD)

lemma  fmap_below_add_restrI:
  assumes "x f|` (-S) \<sqsubseteq> y f|` (-S)"
  and     "x f|` S \<sqsubseteq> z f|` S"
  shows  "x \<sqsubseteq> y f++\<^bsub>S\<^esub> z"
using assms
by (auto intro!: fun_belowI dest:fmap_restr_belowD simp add: lookup_fmap_add_eq)

lemmas fmap_restr_cont2cont[simp,cont2cont] = cont_compose[OF fmap_restr_cont]

lemma fmap_delete_cont:  "cont (fmap_delete x)"
  apply (rule cont2cont_lambda)
  apply (case_tac "y = x")
  apply (auto simp add: assms)
  done
lemmas fmap_delete_cont2cont[simp,cont2cont] = cont_compose[OF fmap_delete_cont]


subsubsection {* A setup for defining a fixed point of finite maps iteratively *}


locale iterative =
  fixes \<rho> :: "'a::type f\<rightharpoonup> 'b::pcpo"
   and e1 :: "'a f\<rightharpoonup> 'b \<rightarrow> 'a f\<rightharpoonup> 'b"
   and e2 :: "'a f\<rightharpoonup> 'b \<rightarrow> 'b"
   and S :: "'a set" and x :: 'a
  assumes ne:"x \<notin> S"
begin
  abbreviation "L == (\<Lambda> \<rho>'. (\<rho> f++\<^bsub>S\<^esub> e1 \<cdot> \<rho>')(x := e2 \<cdot> \<rho>'))"
  abbreviation "H == (\<lambda> \<rho>'. \<Lambda> \<rho>''. \<rho>' f++\<^bsub>S\<^esub> e1 \<cdot> \<rho>'')"
  abbreviation "R == (\<Lambda> \<rho>'. (\<rho> f++\<^bsub>S\<^esub> (fix \<cdot> (H \<rho>')))(x := e2 \<cdot> \<rho>'))"
  abbreviation "R' == (\<Lambda> \<rho>'. (\<rho> f++\<^bsub>S\<^esub> (fix \<cdot> (H \<rho>')))(x := e2 \<cdot> (fix \<cdot> (H \<rho>'))))"

  lemma split_x:
    fixes y
    obtains "y = x" and "y \<notin> S" | "y \<in> S" and "y \<noteq> x" | "y \<notin> S" and "y \<noteq> x" using ne by blast
  lemmas below = fun_belowI[OF split_x, where y1 = "\<lambda>x. x"]
  lemmas eq = ext[OF split_x, where y1 = "\<lambda>x. x"]

  lemma lookup_fix[simp]:
    fixes y and F :: "'a f\<rightharpoonup> 'b \<rightarrow> 'a f\<rightharpoonup> 'b"
    shows "(fix \<cdot> F) y = (F \<cdot> (fix \<cdot> F)) y"
    by (subst fix_eq, rule)

  lemma R_S: "\<And> y. y \<in> S \<Longrightarrow> (fix \<cdot> R) y = (e1 \<cdot> (fix \<cdot> (H (fix \<cdot> R)))) y"
    by (case_tac y rule: split_x) simp_all

  lemma R'_S: "\<And> y. y \<in> S \<Longrightarrow> (fix \<cdot> R') y = (e1 \<cdot> (fix \<cdot> (H (fix \<cdot> R')))) y"
    by (case_tac y rule: split_x) simp_all

  lemma HR_is_R[simp]: "fix\<cdot>(H (fix \<cdot> R)) = fix \<cdot> R"
    by (rule eq) simp_all

  lemma HR'_is_R'[simp]: "fix \<cdot> (H (fix \<cdot> R')) = fix \<cdot> R'"
    by (rule eq) simp_all

  lemma H_noop:
    fixes \<rho>' \<rho>''
    assumes "\<And> y. y \<in> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> (e1 \<cdot> \<rho>'') y \<sqsubseteq> \<rho>' y"
    shows "H \<rho>' \<cdot> \<rho>'' \<sqsubseteq> \<rho>'"
      using assms
      by -(rule below, simp_all)

  lemma HL_is_L[simp]: "fix \<cdot> (H (fix \<cdot> L)) = fix \<cdot> L"
  proof (rule below_antisym)
    show "fix \<cdot> (H (fix \<cdot> L)) \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF H_noop]) simp
    hence *: "e2 \<cdot> (fix \<cdot> (H (fix \<cdot> L))) \<sqsubseteq> e2 \<cdot> (fix \<cdot> L)" by (rule monofun_cfun_arg)

    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> (H (fix \<cdot> L))"
      by (rule fix_least_below[OF below]) (simp_all add: ne *)
  qed
  
  lemma iterative_fmap_add:
    shows "fix \<cdot> L = fix \<cdot> R"
  proof(rule below_antisym)
    show "fix \<cdot> R \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF below]) simp_all

    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> R"
      apply (rule fix_least_below[OF below])
      apply simp
      apply (simp del: lookup_fix add: R_S)
      apply simp
      done
  qed

  lemma iterative_fmap_add':
    shows "fix \<cdot> L = fix \<cdot>  R'"
  proof(rule below_antisym)
    show "fix \<cdot> R' \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF below]) simp_all
  
    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> R'"
      apply (rule fix_least_below[OF below])
      apply simp
      apply (simp del: lookup_fix add: R'_S)
      apply simp
      done
  qed
end

end
