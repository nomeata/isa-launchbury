theory "HeapToEnv"
  imports "AList-Utils"  "Env-Nominal" "Env-HOLCF"
begin

default_sort type

subsubsection {* Conversion from heaps to environments *} 

fun heapToEnv :: "('var \<times> 'exp) list \<Rightarrow> ('exp \<Rightarrow> 'value::{pure,pcpo}) \<Rightarrow> 'var \<Rightarrow> 'value"
where
  "heapToEnv [] _ = \<bottom>"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x := eval e)"

lemma cont2cont_heapToEnv[simp, cont2cont]:
  "(\<And> e . e \<in> snd ` set h \<Longrightarrow> cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct) (auto simp add:fun_upd_eqvt  simp del: fun_upd_apply)

lemma fdom_heapToEnv_subset:"fdom (heapToEnv h eval) \<subseteq> domA h"
  by (induct h eval rule:heapToEnv.induct) (auto dest:set_mp[OF fdom_fun_upd_subset] simp del: fun_upd_apply)

lemma heapToEnv_cong[fundef_cong]:
  "\<lbrakk> heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap1 eval1 = heapToEnv heap2 eval2"
 by (induct heap2 eval2 arbitrary:heap1 rule:heapToEnv.induct, auto)

lemma lookupHeapToEnv:
  assumes "v \<in> domA h"
  shows "(heapToEnv h f) v = f (the (map_of h v))"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done

lemma lookupHeapToEnv_other[simp]:
  assumes "v \<notin> domA h"
  shows "(heapToEnv h f) v = \<bottom>"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done


lemma fmap_restr_heapToEnv_noop:
  "domA h \<subseteq> S \<Longrightarrow> fmap_restr S (heapToEnv h eval) = heapToEnv h eval"
  apply (rule ext)
  apply (case_tac "x \<in> S")
  apply (auto simp add: lookupHeapToEnv intro: lookupHeapToEnv_other)
  done

lemma heapToEnv_cong':
  "\<lbrakk> (\<And> x. x \<in> domA heap \<Longrightarrow> eval1 (the (map_of heap x)) = eval2 (the (map_of heap x))) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap eval1 = heapToEnv heap eval2"
 apply (rule ext)
 apply (case_tac "x \<in> domA heap")
 apply (auto simp add: lookupHeapToEnv)
 done

lemma lookupHeapToEnvNotAppend[simp]:
  assumes "x \<notin> domA \<Gamma>"
  shows "(heapToEnv (\<Gamma>@h) f) x = heapToEnv h f x"
  using assms by (induct \<Gamma>, auto)

lemma heapToEnv_delete[simp]: "heapToEnv (delete x \<Gamma>) eval = fmap_delete x (heapToEnv \<Gamma> eval)"
  by (induct \<Gamma>) auto

lemma heapToEnv_mono:
  "x \<notin> domA \<Gamma> \<Longrightarrow>
  heapToEnv \<Gamma> eval \<sqsubseteq> heapToEnv ((x, e) # \<Gamma>) eval"
   apply simp
   apply (rule fun_belowI)
   apply (case_tac "xa \<in> domA \<Gamma>")
   apply (case_tac "xa = x")
   apply auto
   done

subsubsection {* Reordering lemmas *}

lemma heapToEnv_reorder:
  assumes "map_of \<Gamma> = map_of \<Delta>"
  shows "heapToEnv \<Gamma> h = heapToEnv \<Delta> h"
proof (rule ext)
  from assms
  have *: "domA \<Gamma> = domA \<Delta>" by (metis dom_map_of_conv_domA)

  fix x
  show "heapToEnv \<Gamma> h x = heapToEnv \<Delta> h x" 
    using assms(1) *
    apply (cases "x \<in> domA \<Gamma>")
    apply (auto simp add: lookupHeapToEnv)
    done
qed

lemma heapToEnv_reorder_head:
  assumes "x \<noteq> y"
  shows "heapToEnv ((x,e1)#(y,e2)#\<Gamma>) eval = heapToEnv ((y,e2)#(x,e1)#\<Gamma>) eval"
  by (rule heapToEnv_reorder) (simp add: fun_upd_twist[OF assms])

lemma heapToEnv_reorder_head_append:
  assumes "x \<notin> domA \<Gamma>"
  shows "heapToEnv ((x,e)#\<Gamma>@\<Delta>) eval = heapToEnv (\<Gamma> @ ((x,e)#\<Delta>)) eval"
  by (rule heapToEnv_reorder) (simp, metis assms dom_map_of_conv_domA map_add_upd_left)

lemma heapToEnv_subst_exp:
  assumes "eval e = eval e'"
  shows "heapToEnv ((x,e)#\<Gamma>) eval = heapToEnv ((x,e')#\<Gamma>) eval"
  by (simp add: assms)
end
