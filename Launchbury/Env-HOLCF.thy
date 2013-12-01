theory "Env-HOLCF"
  imports Env "HOLCF-Utils"
begin

subsubsection {* A partial order on finite maps *}


subsubsection {* Continuity and finite maps *}

(*
ch2ch_fun
lemma lookup_chain:
  assumes "chain (Y :: nat \<Rightarrow> 'a f\<rightharpoonup> 'b::pcpo)"
  shows "chain (\<lambda> i . (Y i) x)"
unfolding lookup_def
using assms  by (rule ch2ch_fun)
*)

(*
cont2cont_fun
lemma cont2cont_lookup[simp,cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::type f\<rightharpoonup> 'c::pcpo"
  assumes "cont f"
  shows "cont (\<lambda>p. (f p) x)"
using assms unfolding lookup_def by (rule cont2cont_fun)
*)

(*
cont2cont_lambda
lemma fmap_cont_via_lookupI:
  assumes "\<And> x. cont (\<lambda> \<rho> . f \<rho>  x)"
  shows "cont f"
using assms unfolding lookup_def
by (rule cont2cont_lambda)
*)

lemma fun_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x := v1) \<sqsubseteq> \<rho>2(x := v2)"
  apply (rule fun_belowI)
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fun_belowD)
  done

lemma fun_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. (f x)(v := h x) :: 'a f\<rightharpoonup> 'b::pcpo)"
  by (rule cont2cont_lambda)(auto simp add: assms)


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


lemma pointwise_adm:
  fixes P :: "'a::pcpo \<Rightarrow> 'b::pcpo \<Rightarrow> bool"
  assumes "adm (\<lambda> x. P (fst x) (snd x))"
  shows "adm (\<lambda> m. pointwise P (fst m) (snd m))"
proof (rule admI)
  case (goal1 Y)
    show ?case
    apply (rule pointwiseI)
    apply (rule admD[OF adm_subst[where t = "\<lambda>p . (fst p x, snd p x)", standard, OF _ assms, simplified] `chain Y`])
    using goal1(2) unfolding pointwise_def by auto
qed 

(*
subsubsection {* Expanding the domain of finite maps *}

lift_definition fmap_expand :: "'a f\<rightharpoonup> 'b::pcpo \<Rightarrow> 'a set  \<Rightarrow> 'a f\<rightharpoonup> 'b" ("_\<^bsub>[_]\<^esub>" [90, 60] 90)
  is "\<lambda> m1 S x. if x \<in> S then Some (case m1 x of (Some x) => x | None => \<bottom>) else None"
  ..

lemma fmap_restr_fmap_expand:
  "fmap_restr d1 (m\<^bsub>[d2]\<^esub>) = fmap_restr d1 (m\<^bsub>[d1 \<inter> d2]\<^esub>)"
  by transfer (auto simp add: restrict_map_def)

lemma fmap_restr_fmap_expand2:
  "d1 \<subseteq> d2 \<Longrightarrow> fmap_restr d1 (m\<^bsub>[d2]\<^esub>) = m\<^bsub>[d1]\<^esub>"
  apply transfer
  apply (auto simp add: restrict_map_def split:option.split)
  apply (metis set_mp)
  done

lemma fdom_fmap_expand[simp]:
  "fdom (m\<^bsub>[S]\<^esub>) = S"
  by (transfer, auto split:if_splits) 

lemma fmap_expand_noop[simp]:
  "S = fdom \<rho> \<Longrightarrow> \<rho>\<^bsub>[S]\<^esub> = \<rho>"
  by (transfer, auto split: option.split)

lemma fmap_expand_idem:
  "fdom \<rho> \<subseteq> S1 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> (\<rho>\<^bsub>[S1]\<^esub>)\<^bsub>[S2]\<^esub> = \<rho>\<^bsub>[S2]\<^esub>"
  apply (transfer)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  apply (rule ext)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  done

lemma lookup_fmap_expand1[simp]:
  "x \<in> S \<Longrightarrow> x \<in> fdom m \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = lookup m x"
  by (transfer, auto)

lemma lookup_fmap_expand2[simp]:
  "x \<in> S \<Longrightarrow> x \<notin> fdom m \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = Some \<bottom>"
  by (transfer, auto split:option.split)

lemma lookup_fmap_expand3[simp]:
  "x \<notin> S \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = None"
 by (transfer, auto split:option.split)

lemma lookup_fmap_expand_eq:
  "lookup (m\<^bsub>[S]\<^esub>) x = (if x \<in> S then Some (m f!\<^sub>\<bottom> x) else None)"
 by (transfer, auto split:option.split)

lemma fmap_lookup_bot_fmap_expand_eq:
  "m\<^bsub>[S]\<^esub> f!\<^sub>\<bottom> x = (if x \<in> S then m f!\<^sub>\<bottom> x else  \<bottom>)"
 by (transfer, auto)

lemma fmap_lookup_bot_fmap_expand1[simp]:
  "x \<notin> fdom m \<Longrightarrow>  m\<^bsub>[S]\<^esub> f!\<^sub>\<bottom> x = \<bottom>"
 by (transfer, auto)

lemma fmap_lookup_bot_fmap_expand2[simp]:
  "x \<in> S \<Longrightarrow>  m\<^bsub>[S]\<^esub> f!\<^sub>\<bottom> x = m f!\<^sub>\<bottom> x"
 by (transfer, auto)

lemma fmap_lookup_bot_fmap_expand3[simp]:
  "fdom m \<subseteq> S \<Longrightarrow>  m\<^bsub>[S]\<^esub> f!\<^sub>\<bottom> x = m f!\<^sub>\<bottom> x"
 by (cases "x \<in> fdom m", auto)

lemma fmap_expand_fdom[simp]: "\<rho>\<^bsub>[fdom \<rho>]\<^esub> = \<rho>"
  by (transfer, auto split:option.split)

lemma lookup_bot_fmap_expand_subset:
  "fdom \<rho> \<subseteq> S \<Longrightarrow> op f!\<^sub>\<bottom> (\<rho>\<^bsub>[S]\<^esub>) = op f!\<^sub>\<bottom> \<rho>"
  by rule auto

lemma fmap_expand_belowI:
  assumes "fdom \<rho>' = S"
  assumes "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<in> S \<Longrightarrow> \<rho> f! x \<sqsubseteq> \<rho>' f! x"
  shows "\<rho>\<^bsub>[S]\<^esub> \<sqsubseteq> \<rho>'"
  apply (rule fun_belowI)
  apply (metis assms(1) fdom_fmap_expand)
  apply (case_tac "x \<in> fdom \<rho>")
  apply (metis assms(1) assms(2) lookup_fmap_expand1)
  apply (metis assms(1) lookup_fmap_expand2 minimal the.simps)
  done

lemma fmap_expand_fmap_restr_below:
  assumes [simp]:"fdom x = S2"
  shows "(fmap_restr S1 x)\<^bsub>[S2]\<^esub> \<sqsubseteq> x"
  by (rule fmap_expand_belowI[OF assms(1)])
     (auto simp add: lookup_fmap_restr_eq)

lemma fmap_expand_cont:
  "cont (\<lambda> m. m\<^bsub>[S]\<^esub>)"
  apply (rule fmap_cont_via_lookupI)
  apply (drule fmap_below_dom, simp)
  apply (subst lookup_fmap_expand_eq)
  apply (rule cont_if_fdom[OF _ _ cont_id])
  apply simp_all
  done

lemmas cont2cont_fmap_expand[simp, cont2cont] = cont_compose[OF fmap_expand_cont]

lemma fun_upd_expand:
  "x \<in> S \<Longrightarrow>
   \<rho>(x := y)\<^bsub>[S]\<^esub> = (\<rho>\<^bsub>[S - {x}]\<^esub>)(x := y)"
   apply (rule ext, auto)
   apply (case_tac "xa \<in> fdom (\<rho>(x := y))", auto)
   apply (case_tac "xa = x", auto)
   done

lemma less_fmap_expand:
  "fdom \<rho> \<subseteq> S \<Longrightarrow> \<rho> \<le> \<rho>\<^bsub>[S]\<^esub>"
  unfolding less_eq_fmap_def by auto

lemma fmap_expand_less:
  "S \<subseteq> fdom \<rho> \<Longrightarrow> \<rho>\<^bsub>[S]\<^esub> \<le> \<rho>"
  unfolding less_eq_fmap_def by auto

subsubsection {* Bottoms *}
*)

(*
lemma fmap_bottom_inj[iff]: "f\<emptyset>\<^bsub>[x]\<^esub> = f\<emptyset>\<^bsub>[y]\<^esub> \<longleftrightarrow> x = y"
  by (metis below.r_refl fmap_bottom_below_iff)

lemma fmap_expand_fmap_bottom[simp]: "f\<emptyset>\<^bsub>[S']\<^esub>\<^bsub>[S]\<^esub> = f\<emptyset>\<^bsub>[S]\<^esub>"
  by (transfer, auto)

lemma fmap_restr_fmap_bottom[simp]:
  "fmap_restr S (f\<emptyset>\<^bsub>[S2]\<^esub>) = f\<emptyset>\<^bsub>[S \<inter> S2]\<^esub>"
  by auto

lemma fmap_bottom_insert:
  "f\<emptyset>\<^bsub>[insert x S]\<^esub> = (f\<emptyset>\<^bsub>[S]\<^esub>)(x := \<bottom>)"
  apply (rule ext)
  apply auto[1]
  apply (case_tac "xa = x", auto)
  done

lemma fmap_bottom_less[simp]:
  "S1 \<subseteq> S2 \<Longrightarrow> f\<emptyset>\<^bsub>[S1]\<^esub> \<le> f\<emptyset>\<^bsub>[S2]\<^esub>"
  by (rule fmap_less_eqI) simp_all
*)


subsubsection {* A setup for defining a fixed point of finite maps iteratively *}

(*
lemma fdom_fix_on:
  assumes "fix_on_cond S b F"
  shows  "fdom (fix_on' b F) = fdom b"
proof-
  have "fix_on' b F \<in> S"
    by (rule fix_on_there[OF assms])
  hence "b \<sqsubseteq> fix_on' b F"
    by (metis assms bottom_of_subpcpo_bot_minimal fix_on_cond.simps subpcpo_is_subpcpo_bot)
  thus ?thesis
    by (metis fmap_below_dom)
qed
*)

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


subsection {* Mapping *}

lemma fmap_map_lookup_not_there[simp]: "v \<notin> fdom \<rho> \<Longrightarrow> (fmap_map f \<rho>) v = f \<bottom>"
  by (simp add: lookup_not_fdom)

lemma fmap_map_lookup_eq: "fmap_map f \<rho> v = (if v \<in> fdom \<rho> then f (\<rho> v) else f \<bottom>)"
  by (auto simp add: lookup_not_fdom)

lemma cont2cont_fmap_map [simp, cont2cont]:
  assumes "cont f"
  assumes "\<And> x. cont (f x)"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_map (f x) (g x))"
  apply (rule cont2cont_lambda)
  apply (simp)
  apply (intro cont2cont  `cont g` `cont f` cont_compose2[OF assms(1,2)] cont2cont_fun)
  done

definition fmap_cmap :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> 'c::type f\<rightharpoonup> 'a \<rightarrow> 'c::type f\<rightharpoonup> 'b" 
  where  "fmap_cmap = (\<Lambda> f \<rho>. fmap_map (\<lambda> x. f\<cdot>x) \<rho>)"

lemma [simp]: "fmap_cmap\<cdot>f\<cdot>(\<rho>(x := v)) = (fmap_cmap\<cdot>f\<cdot>\<rho>)(x := f\<cdot>v)"
  unfolding fmap_cmap_def by simp

lemma fmap_cmap_app[simp]: "(fmap_cmap\<cdot>f\<cdot>\<rho>) x = f\<cdot>(\<rho> x)"
  unfolding fmap_cmap_def by auto
end
