theory "Env-HOLCF"
  imports Env  "HOLCF-Set"
begin

default_sort type

lemma cont_compose2:
  assumes "cont c"
  assumes "\<And> x. cont (c x)"
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda>x. c (f x) (g x))"
proof-
  have "monofun (\<lambda>x. c (f x) (g x))"
    apply (rule monofunI)
    apply (rule below_trans[OF cont2monofunE[OF assms(2) cont2monofunE[OF `cont g`]]], assumption)
    apply (rule fun_belowD[OF cont2monofunE[OF `cont c` cont2monofunE[OF `cont f`]]], assumption)
    done
  thus ?thesis
    apply (rule contI2)
    apply (subst cont2contlubE[OF `cont f`], assumption)
    apply (subst cont2contlubE[OF `cont g`], assumption)
    apply (subst cont2contlubE[OF `cont c` ch2ch_cont[OF `cont f`]], assumption)
    apply (subst lub_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (subst cont2contlubE[OF assms(2)ch2ch_cont[OF `cont g`]], assumption)
    apply (subst diag_lub)
    apply (rule ch2ch_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (rule ch2ch_cont[OF assms(2) ch2ch_cont[OF `cont g`]], assumption)
    apply (rule below_refl)
    done
qed

subsubsection {* A partial order on finite maps *}

instantiation fmap :: (type, pcpo) po
begin
  lift_definition below_fmap :: "('a f\<rightharpoonup> 'b) \<Rightarrow> ('a f\<rightharpoonup> 'b) \<Rightarrow> bool" is "op \<sqsubseteq>"..
 

instance
proof default
  fix x :: "'a f\<rightharpoonup> 'b"
  show "x \<sqsubseteq> x" by (auto simp add:below_fmap_def)
next
  fix x y z :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z"
  thus "x \<sqsubseteq> z"
  apply (auto simp add: below_fmap_def)
  by (metis rev_below_trans)
next
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x"
  thus "x = y"
  by (metis Rep_fmap_inject below_fmap.rep_eq po_eq_conv)
qed
end

lemma fmap_belowI:
  assumes "\<And> x. a f! x \<sqsubseteq> b f! x"
  shows "a \<sqsubseteq> b"
  using assms
  by (transfer, metis fun_belowI)

lemma fmap_belowE:
  assumes "m1 \<sqsubseteq> m2"
  shows "m1 f! x \<sqsubseteq> m2 f! x"
  using assms
  by (transfer, metis fun_belowD )

subsubsection {* The order is chain-complete *}

instance fmap :: (type, pcpo) cpo
  apply default
  sorry

subsubsection {* Continuity and finite maps *}

(*
lemma cont_if_fdom:
  assumes "cont (\<lambda>x. k (f x))"
  assumes "cont (\<lambda>x. k (g x))"
  assumes "cont h"
  shows "cont (\<lambda>x. k (if j (fdom (h x))  then f x else g x))"
proof-
  have "monofun (\<lambda>x. k (if j (fdom (h x)) then f x else g x))"
    apply (rule monofunI)
    apply (frule fmap_below_dom[OF cont2monofunE[OF `cont h`]])
    apply (auto intro: cont2monofunE[OF assms(1)] cont2monofunE[OF assms(2)])
    done
  thus ?thesis
    unfolding if_distrib
    apply (rule contI2)
    apply (subst cont2contlubE[OF `cont h`], assumption)
    apply (subst chain_fdom(1)[OF ch2ch_cont[OF `cont h`]], assumption)
    apply (subst chain_fdom(2)[OF ch2ch_cont[OF `cont h`]], assumption)
    apply (subst cont2contlubE[OF cont_if[OF assms(1) assms(2)]], assumption)
    apply (rule below_refl)
    done
qed
*)

lemma lookup_chain:
  assumes "chain (Y :: nat \<Rightarrow> 'a f\<rightharpoonup> 'b::pcpo)"
  shows "chain (\<lambda> i . (Y i) f! x)"
sorry


lemma lookup_cont:
  assumes "chain (Y :: nat \<Rightarrow> 'a f\<rightharpoonup> 'b::pcpo)"
  shows "(\<Squnion> i. Y i) f! x = (\<Squnion> i. (Y i) f! x)"
sorry

lemma cont2cont_lookup[simp,cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::type f\<rightharpoonup> 'c::pcpo"
  assumes "cont f"
  shows "cont (\<lambda>p. (f p) f! x)"
sorry

lemma fmap_cont_via_lookupI:
  assumes "\<And> x. cont (\<lambda> \<rho> . f \<rho> f! x)"
  shows "cont f"
proof-
  have "monofun f"
    apply (rule monofunI)
    apply (rule fmap_belowI)
    apply (erule cont2monofunE[OF assms(1)])
    done
  thus ?thesis
    apply (rule contI2)
    apply (rule fmap_belowI)
    apply (subst cont2contlubE[OF assms(1)], assumption)
    apply (subst lookup_cont, assumption)
    apply (rule below_refl)
    done
qed

lemma fmap_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x f\<mapsto> v1) \<sqsubseteq> \<rho>2(x f\<mapsto> v2)"
  apply (rule fmap_belowI)
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fmap_belowE)
  done

lemma fmap_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. fmap_upd (f x) v (h x) :: 'a f\<rightharpoonup> 'b::pcpo)"
  apply (rule fmap_cont_via_lookupI)
  apply (case_tac "x = v")
  apply (auto simp add: assms)
  done

(*
lemma fdom_adm[intro]: "adm (\<lambda> a. P (fdom a))" 
  apply (rule admI)
  apply auto
*)

(*
lemma fdom_adm_eq[simp]:
   "adm (\<lambda>\<rho>. fdom \<rho> = z)"
   by (rule fdom_adm)
*)


lemma  fmap_add_belowI:
  assumes "\<And> a. a \<in> S \<Longrightarrow> y f! a \<sqsubseteq> z f! a"
  and "\<And> a. a \<notin> S \<Longrightarrow> x f! a \<sqsubseteq> z f! a"
  shows  "x f++\<^bsub>S\<^esub> y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI)
  apply (case_tac "xa \<in> S")
  apply auto
  done

lemma fmap_add_cont1: "cont (\<lambda> x. x f++\<^bsub>S\<^esub> m)"
  apply (rule fmap_cont_via_lookupI)
  apply (case_tac "x \<in> S")
  apply (auto simp add: assms)
  done

lemma fmap_add_cont2: "cont (\<lambda> x. m f++\<^bsub>S\<^esub> x)"
  apply (rule fmap_cont_via_lookupI)
  apply (subst lookup_fmap_add_eq)
  apply simp_all
  done

lemma fmap_add_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. f x f++\<^bsub>S\<^esub> g x)"
by (rule cont_apply[OF assms(1) fmap_add_cont1 cont_compose[OF fmap_add_cont2 assms(2)]])

lemma fmap_add_mono:
  assumes "x1 \<sqsubseteq> x2"
  assumes "y1 \<sqsubseteq> y2"
  shows "x1 f++\<^bsub>S\<^esub> y1 \<sqsubseteq> x2 f++\<^bsub>S\<^esub> y2"
by (rule below_trans[OF cont2monofunE[OF fmap_add_cont1 assms(1)] cont2monofunE[OF fmap_add_cont2 assms(2)]])

lemma fmap_upd_belowI:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> f! z \<sqsubseteq> \<rho>' f! z" 
  assumes "y \<sqsubseteq> \<rho>' f! x"
  shows  "\<rho>(x f\<mapsto> y) \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI)
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_upd_below_fmap_deleteI:
  assumes "\<rho> \<sqsubseteq> fmap_delete x \<rho>'" 
  assumes "y \<sqsubseteq> \<rho>' f! x"
  shows  "\<rho>(x f\<mapsto> y) \<sqsubseteq> \<rho>'"
  by (rule fmap_upd_belowI[OF below_trans[OF fmap_belowE[OF assms(1)] eq_imp_below] assms(2)], simp)

lemma fmap_upd_belowI2:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> f! z \<sqsubseteq> \<rho>' f! z" 
  assumes "\<rho> f! x \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x f\<mapsto> y)"
  apply (rule fmap_belowI)
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_restr_belowI:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> (fmap_restr S m1) f! x \<sqsubseteq> (fmap_restr S m2) f! x"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
  apply (rule fmap_belowI)
  by (metis assms below_bottom_iff lookup_fmap_restr_not_there)

lemma fmap_restr_below_itself:
  shows "m f|` S \<sqsubseteq> m"
  apply (rule fmap_belowI)
  apply (case_tac "x \<in> S")
  apply auto
  done  

lemma fmap_restr_cont:  "cont (fmap_restr S)"
  apply (rule fmap_cont_via_lookupI)
  apply (case_tac "x \<in> S")
  apply (auto simp add: assms)
  done

(*
lemma fmap_restr_fdom_cont'[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_restr (S (fdom (f x))) (g x))"
  apply (rule fmap_cont_via_lookupI)
  apply (subst lookup_fmap_restr_eq)
  apply simp
  apply (rule cont_if_fdom)
  apply (simp_all add: assms)
  done
*)

lemmas fmap_restr_cont2cont[simp,cont2cont] = cont_compose[OF fmap_restr_cont]

lemma fmap_delete_cont:  "cont (fmap_delete x)"
  apply (rule fmap_cont_via_lookupI)
  apply (case_tac "xa = x")
  apply (auto simp add: assms)
  done
lemmas fmap_delete_cont2cont[simp,cont2cont] = cont_compose[OF fmap_delete_cont]


(*
lemma adm_less_fmap [simp]:
  "[|cont (\<lambda>x. u x); cont (\<lambda>x. v x)|] ==> adm (\<lambda>x. u x \<le> ((v x)::'a::type f\<rightharpoonup> 'b::pcpo))"
  apply (subst fmap_less_restrict)
  apply (intro adm_lemmas, assumption+)
  apply (rule contI)
  apply (subst chain_fdom(1)[OF ch2ch_cont[of u]], assumption+)
  apply (subst cont2contlubE[of u], assumption+)
  apply (subst chain_fdom(2)[OF ch2ch_cont[of u]], assumption+)
  apply (rule contE)
  apply auto
  done
*)

lemma fmap_lift_rel_adm:
  assumes "adm (\<lambda> x. P (fst x) (snd x))"
  shows "adm (\<lambda> m. fmap_lift_rel P (fst m) (snd m))"
proof (rule admI)
  case (goal1 Y)
    show ?case
    apply (rule fmap_lift_relI)
    apply (rule admD[OF adm_subst[where t = "\<lambda>p . (fst p f! x, snd p f! x)", standard, OF _ assms, simplified] `chain Y`])
    apply (rule fmap_lift_rel.cases[OF spec[OF goal1(2)]])
    by (metis  fmap_lift_rel.cases  goal1(2) )
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

lemma the_lookup_bot_fmap_expand_subset:
  "fdom \<rho> \<subseteq> S \<Longrightarrow> op f!\<^sub>\<bottom> (\<rho>\<^bsub>[S]\<^esub>) = op f!\<^sub>\<bottom> \<rho>"
  by rule auto

lemma fmap_expand_belowI:
  assumes "fdom \<rho>' = S"
  assumes "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<in> S \<Longrightarrow> \<rho> f! x \<sqsubseteq> \<rho>' f! x"
  shows "\<rho>\<^bsub>[S]\<^esub> \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI)
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

lemma fmap_upd_expand:
  "x \<in> S \<Longrightarrow>
   \<rho>(x f\<mapsto> y)\<^bsub>[S]\<^esub> = (\<rho>\<^bsub>[S - {x}]\<^esub>)(x f\<mapsto> y)"
   apply (rule fmap_eqI, auto)
   apply (case_tac "xa \<in> fdom (\<rho>(x f\<mapsto> y))", auto)
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

lemma fmap_bottom_below[simp]:
  "f\<emptyset> \<sqsubseteq> \<rho>"
 by(rule fmap_belowI, auto)

(*
lemma fmap_bottom_inj[iff]: "f\<emptyset>\<^bsub>[x]\<^esub> = f\<emptyset>\<^bsub>[y]\<^esub> \<longleftrightarrow> x = y"
  by (metis below.r_refl fmap_bottom_below_iff)

lemma fmap_expand_fmap_bottom[simp]: "f\<emptyset>\<^bsub>[S']\<^esub>\<^bsub>[S]\<^esub> = f\<emptyset>\<^bsub>[S]\<^esub>"
  by (transfer, auto)

lemma fmap_restr_fmap_bottom[simp]:
  "fmap_restr S (f\<emptyset>\<^bsub>[S2]\<^esub>) = f\<emptyset>\<^bsub>[S \<inter> S2]\<^esub>"
  by auto

lemma fmap_bottom_insert:
  "f\<emptyset>\<^bsub>[insert x S]\<^esub> = (f\<emptyset>\<^bsub>[S]\<^esub>)(x f\<mapsto> \<bottom>)"
  apply (rule fmap_eqI)
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

(*
locale iterative =
  fixes \<rho> :: "'a::type f\<rightharpoonup> 'b::pcpo"
   and e1 :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
   and e2 :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'b"
   and S :: "'a set" and x :: 'a
   and D
  defines "D \<equiv> insert x (fdom \<rho> \<union> S)"
  assumes cont_e1 [simp]:"cont e1"
  assumes cont_e2 [simp]:"cont e2"
  assumes dom[simp]: "\<And> \<rho>. fdom (e1 \<rho>) = S"
  assumes ne:"x \<notin> S"
begin
  sublocale subpcpo "UNIV :: 'b set" by (rule subpcpo_UNIV)

  abbreviation "cpo \<equiv> UNIV :: 'b set"

  abbreviation "L == (\<lambda> \<rho>'. (\<rho> f++ e1 \<rho>')(x f\<mapsto> e2 \<rho>'))"
  abbreviation "H == (\<lambda> \<rho>' \<rho>''. \<rho>' f++ e1 \<rho>'')"
  abbreviation "R == (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' b (H \<rho>')))(x f\<mapsto> e2 \<rho>'))"
  abbreviation "R' == (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' b (H \<rho>')))(x f\<mapsto> e2 (fix_on' b (H \<rho>'))))"

  lemma condL: "fix_on_cond cpo b L"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (simp add: D_def)
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condL]

  lemma condH: "\<And> \<rho>'. \<rho>' \<in> cpo \<Longrightarrow> fix_on_cond cpo b (H \<rho>')"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (auto simp add: D_def)[1]
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condH]
  
  lemma condR: "fix_on_cond cpo b R"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      using fdom_fix_on[OF condH]  apply (auto simp add: D_def)[1]
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_upd_cont[OF cont_id cont_const]]
                fmap_upd_cont[OF cont_const cont_id]
                _
                cont_is_cont_on[OF cont_e2]])
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_add_cont1]
                fmap_add_cont2
                cont_is_cont_on[OF cont_const]
                ])
    apply (rule cont_comp_cont_on[OF fmap_restr_cont])
    apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (1) fix_on_mono[OF condH condH])
      apply (erule cont2monofunE[OF fmap_add_cont1])

    apply (rule eq_imp_below)
    apply (rule fix_on_cont[OF chain_on_is_chain condH[OF chain_on_is_on]])
      apply assumption
      apply assumption
    apply (rule cont2cont_lambda[OF fmap_add_cont1])
    done
  lemmas [simp] = fdom_fix_on[OF condR]

  lemma cont_on_fix_H: "cont_on (\<lambda> \<rho>'. fix_on' b (H \<rho>'))"
    apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (1) fix_on_mono[OF condH condH])
      apply (erule cont2monofunE[OF fmap_add_cont1])

    apply (rule eq_imp_below)
    apply (rule fix_on_cont[OF chain_on_is_chain condH[OF chain_on_is_on]])
      apply assumption
      apply assumption
    apply (rule cont2cont_lambda[OF fmap_add_cont1])
    done

  lemma condR': "fix_on_cond cpo b R'"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      using fdom_fix_on[OF condH]  apply (auto simp add: D_def)[1]
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_upd_cont[OF cont_id cont_const]]
                fmap_upd_cont[OF cont_const cont_id]
                _
                cont_comp_cont_on[OF cont_e2 cont_on_fix_H]])
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_add_cont1]
                fmap_add_cont2
                cont_is_cont_on[OF cont_const]
                ])
    apply (rule cont_comp_cont_on[OF fmap_restr_cont cont_on_fix_H])
    done
  lemmas [simp] = fdom_fix_on[OF condR']

  lemmas fix_eq_R = fix_on_eq[OF condR]
  lemmas fix_eq_R' = fix_on_eq[OF condR']
  lemmas fix_eq_L = fix_on_eq[OF condL]
  lemmas fix_eq_HL = fix_on_eq[OF condH[OF fix_on_there[OF condL]]]
  lemmas fix_eq_HR = fix_on_eq[OF condH[OF fix_on_there[OF condR]]]
  lemmas fix_eq_HR' = fix_on_eq[OF condH[OF fix_on_there[OF condR']]]

  lemma [simp]: "D \<inter> S = S" 
      by (auto simp add: D_def)

  lemma HR_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) x = lookup (fix_on' b R) x"
      apply (subst fix_eq_HR) by simp
  
  lemma HR_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HR)
    apply simp
    using ne by metis

  lemma L_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b L) y = lookup (e1 (fix_on' b L)) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst (1) fix_eq_L)
    apply simp
    using ne by metis

  lemma L_x2[simp]: "(fix_on' b L) f! x = e2 (fix_on' b L)"
    by (subst (1) fix_eq_L, simp)

  lemma L_not_S_x2[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b L) y = lookup \<rho> y"
    by (subst (1) fix_eq_L, simp)

  lemma R_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b R) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_R)
    apply simp
    using ne by metis

  lemma R_x2[simp]: "(fix_on' b R) f! x = e2 (fix_on' b R)"
    by (subst fix_eq_R, simp)

  lemma R_not_S[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b R) y = lookup \<rho> y"
    by (subst fix_eq_R, simp)

  lemma HR_is_R[simp]: "fix_on' b (H (fix_on' b R)) = fix_on' b R"
    apply (rule fmap_eqI)
    apply simp
    apply (case_tac "xa \<in> S")
    apply simp_all
    done

  lemma HL_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b L))) x = lookup (fix_on' b L) x"
    apply (subst fix_eq_HL) by simp

  lemma HR'_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R'))) x = lookup (fix_on' b R') x"
    apply (subst fix_eq_HR') by simp

  lemma HR'_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R'))) y = lookup (e1 (fix_on' b (H (fix_on' b R')))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HR')
    apply simp
    using ne by metis

  lemma HL_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b L))) y = lookup (e1 (fix_on' b (H (fix_on' b L)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HL)
    apply simp
    using ne by metis

  lemma R'_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b R') y = lookup (e1 (fix_on' b (H (fix_on' b R')))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_R')
    apply simp
    using ne by metis

  lemma R'_x2[simp]: "(fix_on' b R') f! x = e2 (fix_on' b (H (fix_on' b R')))"
    by (subst fix_eq_R', simp)

  lemma R'_not_S[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b R') y = lookup \<rho> y"
    by (subst fix_eq_R', simp)

  lemma HR'_is_R'[simp]: "fix_on' b (H (fix_on' b R')) = fix_on' b R'"
    apply (rule fmap_eqI)
    apply simp
    apply (case_tac "xa \<in> S")
    apply simp_all
    done
  
  lemma H_noop:
    fixes \<rho>' \<rho>''
    assumes there: "(\<rho>' :: 'a f\<rightharpoonup> 'b) \<in> cpo"
    assumes "\<And> x. x \<in> S \<Longrightarrow> (e1 \<rho>'') f! x \<sqsubseteq> \<rho>' f! x"
    shows "H \<rho>' \<rho>'' \<sqsubseteq> \<rho>'"
      using assms
      apply -
      apply (rule fmap_belowI)
      using there apply (auto simp add: D_def)[1]
      apply (case_tac "x \<in> fdom (e1 \<rho>')")
      apply simp
      apply simp
      done

  lemma HL_is_L[simp]: "fix_on' b (H (fix_on' b L)) = fix_on' b L"
  proof (rule below_antisym)
    show "fix_on' b (H (fix_on' b L)) \<sqsubseteq> fix_on' b L"
      apply (rule fix_on_least_below[OF condH[OF fix_on_there[OF condL]] fix_on_there[OF condL]])
      apply (rule H_noop[OF fix_on_there[OF condL]])
      apply simp
    done

    show "fix_on' b L \<sqsubseteq> fix_on' b (H (fix_on' b L))"
    apply (rule fix_on_least_below[OF condL fix_on_there[OF condH[OF fix_on_there[OF condL]]]])
    apply (rule fmap_upd_belowI)
    apply simp apply (auto simp add: D_def)[1]
    apply (case_tac "z \<in> S")
    apply simp
    apply simp
    apply (simp add: ne)
    apply (rule cont2monofunE[OF cont_e2])
    apply fact
    done
  qed
  
  lemma iterative_fmap_add:
    shows "fix_on' b L = fix_on' b R"
  proof(rule below_antisym)
    show "fix_on' b R \<sqsubseteq> fix_on' b L"
    proof (rule fix_on_least_below[OF condR])
      show "fix_on' b L \<in> cpo"
        by simp
      show "R (fix_on' b L) \<sqsubseteq> fix_on' b L"
      proof(rule fmap_upd_belowI)
        case goal1 show ?case by (simp, auto simp add: D_def)
        show "e2 (fix_on' b L) \<sqsubseteq> (fix_on' b L) f! x"
          by simp
        case (goal2 y)
        thus "\<rho> f++ fmap_restr S (fix_on' b (H (fix_on' b L))) f! y \<sqsubseteq> (fix_on' b L) f! y"
          by(cases "y \<in> S", simp_all)
      qed
    qed
  
    show "fix_on' b L \<sqsubseteq> fix_on' b R"
    proof (rule fix_on_least_below[OF condL])
      show "fix_on' b R \<in> cpo"
        by simp
      show "L (fix_on' b R) \<sqsubseteq> fix_on' b R"
        apply (rule  fmap_upd_belowI)
        apply simp apply (auto simp add: D_def)[1]
        apply (case_tac "z \<notin> S")
        apply simp_all
      done
    qed
  qed

  lemma iterative_fmap_add':
    shows "fix_on' b L = fix_on' b R'"
  proof(rule below_antisym)
    show "fix_on' b R' \<sqsubseteq> fix_on' b L"
    proof (rule fix_on_least_below[OF condR'])
      show "fix_on' b L \<in> cpo"
        by simp
      show "R' (fix_on' b L) \<sqsubseteq> fix_on' b L"
      proof(rule fmap_upd_belowI)
        case goal1 show ?case by (simp, auto simp add: D_def)
        show "e2 (fix_on' b (H (fix_on' b L))) \<sqsubseteq> (fix_on' b L) f! x"
          by simp
        case (goal2 y)
          thus "\<rho> f++ fmap_restr S (fix_on' b (H (fix_on' b L))) f! y \<sqsubseteq> fix_on' b L f! y"
            by (cases "y \<in> S", simp_all)
      qed
    qed
  
    show "fix_on' b L \<sqsubseteq> fix_on' b R'"
    proof (rule fix_on_least_below[OF condL])
      show "fix_on' b R' \<in> cpo"
        by simp
      show "L (fix_on' b R') \<sqsubseteq> fix_on' b R'"
        apply (rule  fmap_upd_belowI)
        apply simp apply (auto simp add: D_def)[1]
        apply (case_tac "z \<notin> S")
        apply simp_all
      done
    qed
  qed
end
*)

subsubsection {* Finite maps can be partitioned in pcpo's *} 

instance fmap :: (type, pcpo) pcpo
apply default
apply (rule exI[where x = "f\<emptyset>"])
apply auto
done

lemma bot_is_fmap_empty [simp]: "\<bottom> = f\<emptyset>"
  by (metis below_bottom_iff fmap_bottom_below)

instantiation fmap :: (type, pcpo) subpcpo_partition
begin
  definition "to_bot x = f\<emptyset>"

  lemma to_bot_vimage_cone:"to_bot -` {to_bot (x :: 'a f\<rightharpoonup> 'b)} = UNIV"
    by (auto simp add:to_bot_fmap_def)

  instance  
  apply default
  apply (subst to_bot_vimage_cone)
  apply (rule subpcpo_UNIV)
  apply (simp add: to_bot_fmap_def )
  apply (simp add: to_bot_fmap_def)
  done
end

subsection {* Mapping *}

lemma fmap_map_lookup_not_there[simp]: "v \<notin> fdom \<rho> \<Longrightarrow> lookup (fmap_map f \<rho>) v = f \<bottom>"
  by (simp add: lookup_not_fdom)

lemma fmap_map_lookup_eq: "fmap_map f \<rho> f! v = (if v \<in> fdom \<rho> then f (\<rho> f! v) else f \<bottom>)"
  by (auto simp add: lookup_not_fdom)

lemma cont2cont_fmap_map [simp, cont2cont]:
  assumes "cont f"
  assumes "\<And> x. cont (f x)"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_map (f x) (g x))"
  apply (rule fmap_cont_via_lookupI)
  apply simp
  apply (intro cont2cont  `cont g` `cont f` cont_compose2[OF assms(1,2)])
  done

definition fmap_cmap :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> 'c::type f\<rightharpoonup> 'a \<rightarrow> 'c::type f\<rightharpoonup> 'b" 
  where  "fmap_cmap = (\<Lambda> f \<rho>. fmap_map (\<lambda> x. f\<cdot>x) \<rho>)"


lemma [simp]: "fmap_cmap\<cdot>f\<cdot>(\<rho>(x f\<mapsto> v)) = fmap_cmap\<cdot>f\<cdot>\<rho>(x f\<mapsto> f\<cdot>v)"
  unfolding fmap_cmap_def by simp

lemma [simp]: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> fmap_cmap\<cdot>f\<cdot>\<rho> f! x = f\<cdot>(\<rho> f! x )"
  unfolding fmap_cmap_def by auto

end
