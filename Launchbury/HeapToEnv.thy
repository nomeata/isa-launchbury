theory "HeapToEnv"
  imports "DistinctVars" "Nominal-Utils" "Env-Nominal-HOLCF"
begin

default_sort type

subsubsection {* Conversion from heaps to environments *} 

function heapToEnv :: "('var \<times> 'exp) list \<Rightarrow> ('exp \<Rightarrow> 'value::pcpo) \<Rightarrow> 'var f\<rightharpoonup> 'value"
where
  "heapToEnv [] _ = f\<emptyset>"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma cont2cont_heapToEnv[simp, cont2cont]:
  "(\<And> e . e \<in> snd ` set h \<Longrightarrow> cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct, auto simp add: fmap_upd_eqvt)

lemma fdom_heapToEnv_subset:"fdom (heapToEnv h eval) \<subseteq> heapVars h"
  by (induct h eval rule:heapToEnv.induct) (auto dest:set_mp[OF fdom_fmap_upd_subset])

lemma heapToEnv_cong[fundef_cong]:
  "\<lbrakk> heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap1 eval1 = heapToEnv heap2 eval2"
 by (induct heap2 eval2 arbitrary:heap1 rule:heapToEnv.induct, auto)

lemma lookupHeapToEnv:
  assumes "v \<in> heapVars h"
  shows "(heapToEnv h f) f! v = f (the (map_of h v))"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done

lemma lookupHeapToEnv_other[simp]:
  assumes "v \<notin> heapVars h"
  shows "(heapToEnv h f) f! v = \<bottom>"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done


lemma fmap_restr_heapToEnv_noop:
  "heapVars h \<subseteq> S \<Longrightarrow> fmap_restr S (heapToEnv h eval) = heapToEnv h eval"
  apply rule
  apply (case_tac "x \<in> S")
  apply (auto simp add: lookupHeapToEnv intro: lookupHeapToEnv_other)
  done

lemma heapToEnv_cong':
  "\<lbrakk> (\<And> x. x \<in> heapVars heap \<Longrightarrow> eval1 (the (map_of heap x)) = eval2 (the (map_of heap x))) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap eval1 = heapToEnv heap eval2"
 apply rule
 apply (case_tac "x \<in> heapVars heap")
 apply (auto simp add: lookupHeapToEnv)
 done

lemma lookupHeapToEnvNotAppend[simp]:
  assumes "x \<notin> heapVars \<Gamma>"
  shows "heapToEnv (\<Gamma>@h) f f! x = heapToEnv h f f! x"
  using assms by (induct \<Gamma>, auto)

(*
lemma heapToEnv_remove_Cons_fmap_expand:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> heapToEnv ((x, e) # \<Gamma>) eval\<^bsub>[S]\<^esub> = heapToEnv \<Gamma> eval\<^bsub>[S]\<^esub>"
  apply (rule fmap_eqI)
  apply simp
  apply (subgoal_tac "xa \<noteq> x")
  apply (case_tac "xa \<in> heapVars \<Gamma>")
  apply simp
  apply simp
  apply auto
  done
*)

lemma heapToEnv_delete[simp]: "heapToEnv (delete x \<Gamma>) eval = fmap_delete x (heapToEnv \<Gamma> eval)"
  by (induct \<Gamma>) auto

lemma heapToEnv_mono:
  "x \<notin> heapVars \<Gamma> \<Longrightarrow>
  heapToEnv \<Gamma> eval \<sqsubseteq> heapToEnv ((x, e) # \<Gamma>) eval"
   apply simp
   apply (rule fmap_belowI)
   apply (case_tac "xa \<in> heapVars \<Gamma>")
   apply (case_tac "xa = x")
   apply auto
   done

subsubsection {* Reordering lemmas *}

lemma heapToEnv_reorder:
  assumes "map_of \<Gamma> = map_of \<Delta>"
  shows "heapToEnv \<Gamma> h = heapToEnv \<Delta> h"
proof (rule fmap_eqI)
  from assms
  have *: "heapVars \<Gamma> = heapVars \<Delta>" by (metis dom_map_of_conv_heapVars)

  fix x
  show "heapToEnv \<Gamma> h f! x = heapToEnv \<Delta> h f! x" 
    using assms(1) *
    apply (cases "x \<in> heapVars \<Gamma>")
    apply (auto simp add: lookupHeapToEnv)
    done
qed

lemma heapToEnv_reorder_head:
  assumes "x \<noteq> y"
  shows "heapToEnv ((x,e1)#(y,e2)#\<Gamma>) eval = heapToEnv ((y,e2)#(x,e1)#\<Gamma>) eval"
  by (rule heapToEnv_reorder) (simp add: fun_upd_twist[OF assms])

lemma heapToEnv_reorder_head_append:
  assumes "x \<notin> heapVars \<Gamma>"
  shows "heapToEnv ((x,e)#\<Gamma>@\<Delta>) eval = heapToEnv (\<Gamma> @ ((x,e)#\<Delta>)) eval"
  by (rule heapToEnv_reorder) (simp, metis assms dom_map_of_conv_heapVars map_add_upd_left)

lemma heapToEnv_delete_insert:
  assumes "distinctVars \<Gamma>"
  assumes "(x,e) \<in> set \<Gamma>"
  shows "heapToEnv \<Gamma> eval = heapToEnv ((x,e) # delete x \<Gamma>) eval"
proof(rule heapToEnv_reorder)
  show "map_of \<Gamma> = map_of ((x,e) # delete x \<Gamma>)"
  proof
    fix x'
    show "map_of \<Gamma> x' = (map_of ((x,e) # delete x \<Gamma>)) x'"
    by (cases "x' = x")(simp_all, metis assms distinctVarsE map_of_is_SomeD weak_map_of_SomeI)
  qed
qed

lemma heapToEnv_subst_exp:
  assumes "eval e = eval e'"
  shows "heapToEnv ((x,e)#\<Gamma>) eval = heapToEnv ((x,e')#\<Gamma>) eval"
  by (simp add: assms)
end
