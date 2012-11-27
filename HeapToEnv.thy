theory "HeapToEnv"
  imports "Nominal-Utils" "FMap-Nominal-HOLCF" "~~/src/HOL/HOLCF/Library/Option_Cpo" "~~/src/HOL/HOLCF/HOLCF"
begin

default_sort type


function heapToEnv :: "('var \<times> 'exp) list \<Rightarrow> ('exp \<Rightarrow> 'value) \<Rightarrow> ('var, 'value) fmap"
where
  "heapToEnv [] _ = fempty"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma cont2cont_heapToEnv[simp, cont2cont]:
  "(\<And> e . e \<in> snd ` set h \<Longrightarrow> cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct, auto simp add: fmap_upd_eqvt  permute_fun_def)

lemma heapToEnv_fdom[simp]:"fdom (heapToEnv h eval) = fst ` set h"
  by (induct h eval rule:heapToEnv.induct, auto)

lemma heapToEnv_cong[fundef_cong]:
  "\<lbrakk> heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
    \<Longrightarrow>  heapToEnv heap1 eval1 = heapToEnv heap2 eval2"
 by (induct heap2 eval2 arbitrary:heap1 rule:heapToEnv.induct, auto)

lemma perm_still_cont[simp]: "cont (\<pi> \<bullet> f) = cont (f :: ('a :: cont_pt) \<Rightarrow> ('b :: cont_pt))"
proof
  have imp:"\<And> (f :: 'a \<Rightarrow> 'b) \<pi>. cont f \<Longrightarrow> cont (\<pi> \<bullet> f)"
    unfolding permute_fun_def
    by (metis cont_compose perm_cont)
  show "cont f \<Longrightarrow> cont (\<pi> \<bullet> f)" using imp[of "f" "\<pi>"].
  show "cont (\<pi> \<bullet> f) \<Longrightarrow> cont (f)" using imp[of "\<pi> \<bullet> f" "-\<pi>"] by simp
qed

lemma perm_still_cont3[simp]: "(\<forall>e. cont ((\<pi> \<bullet> f) e)) = (\<forall> e. cont ((f :: ('a::cont_pt \<Rightarrow> 'b::cont_pt \<Rightarrow> 'b::cont_pt)) e))"
proof
  have imp:"\<And> (f :: ('a::cont_pt \<Rightarrow> 'b::cont_pt \<Rightarrow> 'c::cont_pt)) \<pi>. (\<forall>e. cont (f e)) \<Longrightarrow> (\<forall> e. cont ((\<pi> \<bullet> f) e))"
    unfolding permute_fun_def
    apply rule
    apply (erule_tac x = "-\<pi> \<bullet> e" in allE)
    by (metis cont_compose perm_cont) 
  show "(\<forall> e. cont (f e)) \<Longrightarrow> (\<forall> e. cont ((\<pi> \<bullet> f) e))" using imp[of "f" "\<pi>"].
  show "(\<forall> e. cont ((\<pi> \<bullet> f) e)) \<Longrightarrow> (\<forall> e. cont (f e))" using imp[of "\<pi> \<bullet> f" "-\<pi>"] by simp
qed

lemma perm_still_cont4[simp]: "(\<forall>e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> f) e)) = (\<forall> e \<in> snd `set h. cont ((f :: ('a::cont_pt \<Rightarrow> 'b::cont_pt \<Rightarrow> 'b::cont_pt)) e))"  
  (is "?lhs = ?rhs")
proof
  have imp:"\<And> h (f :: ('a::cont_pt \<Rightarrow> 'b::cont_pt \<Rightarrow> 'b::cont_pt)) \<pi>. (\<forall>e \<in> snd ` set h. cont (f e)) \<Longrightarrow> (\<forall> e \<in> snd `set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> f) e))"
    unfolding permute_fun_def
    apply rule
    apply (erule_tac x = "-\<pi> \<bullet> e" in ballE)
    apply (rule cont_compose[OF perm_cont])
    apply (erule cont_compose)
    apply (rule cont_compose[OF perm_cont])
    apply auto[1]
    apply (erule notE)
    apply (subst image_iff)
    apply (erule imageE)
    apply (rule_tac x = "-\<pi> \<bullet> x" in bexI)
    apply auto[1]
    apply (subst (asm) set_eqvt[symmetric])
    by (metis (full_types) mem_permute_iff permute_minus_cancel(1))    
  show "?rhs \<Longrightarrow> ?lhs" using imp[of "h" "f" "\<pi>"].
  show "?lhs \<Longrightarrow> ?rhs" using imp[of "\<pi> \<bullet> h" "\<pi> \<bullet> f" "-\<pi>"] by simp
qed

lemma lookupHeapToEnv:
  assumes "v \<in> fst ` set h"
  shows "the (lookup (heapToEnv h f) v) = f (the (map_of h v))"
  using assms
  apply (induct h)
  apply simp
  apply (case_tac a)
  apply auto
  done

lemma lookupHeapToEnvE:
  assumes "v \<in> fst ` set h"
  obtains e where "(v, e) \<in> set h" and "\<And> f. the (lookup (heapToEnv h f) v) = f e"
proof(rule that)
  show "(v, (the (map_of h v))) \<in> set h"
    by (metis assms domD dom_map_of_conv_image_fst map_of_is_SomeD the.simps)
  fix f
  show "the (lookup (heapToEnv h f) v) = f (the (map_of h v))"
    by (rule lookupHeapToEnv[OF assms])
qed

lemma lookupHeapToEnvE2:
  assumes "v \<in> fst ` set h"
  obtains e where "(v, e) \<in> set h" and "\<And> f. the (lookup (heapToEnv h f) v) = f e" and "\<And> f. the (lookup (heapToEnv (h@h') f) v) = f e"
proof(rule that)
  show "(v, (the (map_of h v))) \<in> set h"
    by (metis assms domD dom_map_of_conv_image_fst map_of_is_SomeD the.simps)
  fix f
  show "the (lookup (heapToEnv h f) v) = f (the (map_of h v))"
    by (rule lookupHeapToEnv[OF assms])
  show "the (lookup (heapToEnv (h @ h') f) v) = f (the (map_of h v))"
    apply (subst lookupHeapToEnv)
    using assms apply (auto simp add: map_add_dom_app_simps dom_map_of_conv_image_fst)
    done
qed

lemma lookupHeapToEnvNotCons[simp]:
  assumes "x \<noteq> y"
  shows "the (lookup (heapToEnv ((y,e)#h) f) x) = the (lookup (heapToEnv h f) x)"
  using assms by simp

lemma lookupHeapToEnvNotAppend[simp]:
  assumes "x \<notin> fst ` set \<Gamma>"
  shows "the (lookup (heapToEnv (\<Gamma>@h) f) x) = the (lookup (heapToEnv h f) x)"
  using assms by (induct \<Gamma>, auto)

end
