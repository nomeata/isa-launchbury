theory "Denotational-Common"
  imports Terms Heap "Nominal-Utils" "FMap-Nominal-HOLCF" "~~/src/HOL/HOLCF/Library/Option_Cpo" "~~/src/HOL/HOLCF/HOLCF"
begin

default_sort cpo


instantiation var :: discrete_cpo
begin
  definition  [simp]: "(x::var) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instance var :: cont_pt  by default auto


definition cfun_upd :: "('a \<rightarrow> 'b) => 'a => 'b => ('a \<rightarrow> 'b)" where
  "cfun_upd f a b == \<Lambda> x. if x=a then b else f\<cdot>x"

nonterminal cupdbinds and cupdbind

syntax
  "_cupdbind" :: "['a, 'a] => cupdbind"               ("(2_ :\<cdot>=/ _)")
  ""         :: "cupdbind => cupdbinds"               ("_")
  "_cupdbinds":: "[cupdbind, cupdbinds] => cupdbinds" ("_,/ _")
  "_cUpdate"  :: "['a, cupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_cUpdate f (_cupdbinds b bs)" == "_cUpdate (_cUpdate f b) bs"
  "f(x:\<cdot>=y)" == "CONST cfun_upd f x y"


lemma cfun_upd_eqvt[eqvt]: "p \<bullet> (cfun_upd f (x::'a::{cont_pt,discrete_cpo}) y) = cfun_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
  by (auto simp add:permute_cfun_def cfun_eq_iff cfun_upd_def)


domain Value = Fn (lazy "Value \<rightarrow> Value")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value" (* (infix "\<down>Fn" 70) *)
 where "Fn_project\<cdot>(Fn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"

lemma "Fn\<cdot>(\<Lambda> x . \<bottom>) \<noteq> \<bottom>" by simp

type_synonym Env = "(var, Value) fmap"

instantiation Value :: pure_cpo
begin
  definition "p \<bullet> (v::Value) = v"
instance
  apply default
  apply (auto simp add: permute_Value_def)
  done
end

lemma sharp_Env: "atom (x::var) \<sharp> (\<rho> :: Env) \<longleftrightarrow> x \<notin> fdom \<rho>"
  apply (subst fresh_def)
  apply (simp  add: supp_fmap)
  apply (subst (1 2) fresh_def[symmetric])
  apply (simp add: fresh_finite_set_at_base[OF finite_fdom] pure_fresh)
  done

lemma sharp_star_Env: "set (bn as) \<sharp>* (\<rho> :: Env) \<longleftrightarrow> (\<forall> x \<in> fst`set (asToHeap as) . x \<notin> fdom \<rho>)"
  by(induct rule:asToHeap.induct, auto simp add: fresh_star_def exp_assn.bn_defs sharp_Env)

function heapToEnv :: "heap \<Rightarrow> (exp \<Rightarrow> Value) \<Rightarrow> Env"
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

lemma perm_still_cont3[simp]: "(\<forall>e. cont ((\<pi> \<bullet> f) e)) = (\<forall> e. cont ((f :: (exp \<Rightarrow> Env \<Rightarrow> Value)) e))"
proof
  have imp:"\<And> (f :: (exp \<Rightarrow> Env \<Rightarrow> Value)) \<pi>. (\<forall>e. cont (f e)) \<Longrightarrow> (\<forall> e. cont ((\<pi> \<bullet> f) e))"
    unfolding permute_fun_def
    apply rule
    apply (erule_tac x = "-\<pi> \<bullet> e" in allE)
    by (metis cont_compose perm_cont) 
  show "(\<forall> e. cont (f e)) \<Longrightarrow> (\<forall> e. cont ((\<pi> \<bullet> f) e))" using imp[of "f" "\<pi>"].
  show "(\<forall> e. cont ((\<pi> \<bullet> f) e)) \<Longrightarrow> (\<forall> e. cont (f e))" using imp[of "\<pi> \<bullet> f" "-\<pi>"] by simp
qed

lemma perm_still_cont4[simp]: "(\<forall>e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> f) e)) = (\<forall> e \<in> snd `set h. cont ((f :: (exp \<Rightarrow> Env \<Rightarrow> Value)) e))"  
  (is "?lhs = ?rhs")
proof
  have imp:"\<And> h (f :: (exp \<Rightarrow> Env \<Rightarrow> Value)) \<pi>. (\<forall>e \<in> snd ` set h. cont (f e)) \<Longrightarrow> (\<forall> e \<in> snd `set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> f) e))"
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

definition heapExtendMeet :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtendMeet \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>) )
    then fmap_meet \<rho> (fixR (fmap_bottom (fst ` set h)) (\<lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_meet \<rho> \<rho>'))))
    else fempty)"

lemma heapExtendMeet_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtendMeet \<rho> h eval = heapExtendMeet (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "(\<forall> e \<in> snd ` set h. cont (eval e)) \<and> compatible_fmap \<rho> (heapToEnv h (\<lambda> e. eval e \<rho>))")
  case True
  moreover hence "(\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)) \<and> compatible_fmap (\<pi> \<bullet> \<rho>) (heapToEnv (\<pi> \<bullet> h) (\<lambda> e. (\<pi> \<bullet> eval) e (\<pi> \<bullet> \<rho>))) " sorry
  ultimately show ?thesis
   unfolding heapExtendMeet_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_meet_eqvt)
   apply (subst fixR_eqvt)
   apply (auto simp add: fmap_bottom_eqvt)[1]
   apply perm_simp
   apply rule
   done
next
case False thus ?thesis
   unfolding heapExtendMeet_def
   apply (subst if_not_P, assumption)
   apply (subst if_not_P)
   apply  (rule notI)
   apply  (erule notE)
   apply  rule
   apply  (metis perm_still_cont4)
   apply  (erule conjE)
   apply  (drule compatible_fmap_eqvt[of _ _ "- \<pi>"])
   apply  (simp add: permute_fun_def heapToEnv_eqvt)
   apply (rule fempty_eqvt)
   done
qed

lemma heapExtendMeet_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtendMeet env1 heap1 eval1 = heapExtendMeet env2 heap2 eval2"
  unfolding heapExtendMeet_def
  by (auto cong:heapToEnv_cong)

definition heapExtend :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend \<rho> h eval =
    (if (\<forall>e \<in> snd ` set h. cont (eval e))
    then fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h)) (\<Lambda> \<rho>' . heapToEnv h (\<lambda> e. eval e (fmap_update \<rho> \<rho>'))))
    else fempty)"


lemma heapExtend_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtend \<rho> h eval = heapExtend (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
proof (cases "\<forall> e \<in> snd ` set h. cont (eval e)")
  case True
  moreover hence "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> eval) e)" by (simp only: perm_still_cont4 simp_thms(35))
  ultimately show ?thesis
   unfolding heapExtend_def
   apply -
   apply (subst if_P, assumption)+
   apply (subst fmap_update_eqvt)
   apply (subst fix1_eqvt)
   apply (subst Lam_eqvt)
     apply (rule cont2cont)
     apply (rule cont_compose) back
     apply auto[1]
     apply auto[1]
    apply (auto simp add: fmap_bottom_eqvt)[1]
    apply perm_simp
    apply rule
    done
next
case False thus ?thesis
   unfolding heapExtend_def
   apply (simp_all only: if_not_P perm_still_cont4)
   apply auto
  done 
qed

lemma heapExtend_cong[fundef_cong]:
  "\<lbrakk> env1 = env2 ; heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
      \<Longrightarrow> heapExtend env1 heap1 eval1 = heapExtend env2 heap2 eval2"
  unfolding heapExtend_def
  by (auto cong:heapToEnv_cong)

lemma heapExtend_cont[simp,cont2cont]: "cont (\<lambda>\<rho>. heapExtend \<rho> h eval)"
  unfolding heapExtend_def
  apply (cases "\<forall> e \<in> snd ` set h.  cont (eval e)")
  apply (simp_all only: if_P if_not_P perm_still_cont4 simp_thms(35) if_False)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply (subst beta_cfun)
  apply (intro cont2cont)
  apply (rule cont_compose[where c = "eval e", standard, where eval = eval]) 
  apply auto[1]
  apply simp
  apply simp
  apply simp
  done
end
