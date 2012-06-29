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

function heapToEnv :: "heap \<Rightarrow> (exp \<Rightarrow> Value) \<Rightarrow> Env"
where
  "heapToEnv [] _ = fempty"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma cont2cont_heapToEnv[simp, cont2cont]:
  "(\<And> e. cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct, auto simp add: fmap_upd_eqvt  permute_fun_def)

lemma heapToEnv_fdom[simp]:"fdom (heapToEnv h eval) = fst ` set h"
  by (induct h eval rule:heapToEnv.induct, auto)

definition heapExtend :: "Env \<Rightarrow> heap \<Rightarrow> (exp \<Rightarrow> Env \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend \<rho> h eval = fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h))  (\<Lambda> \<rho>'. heapToEnv h (\<lambda> e. eval e \<rho>')))"

lemma heapExtend_eqvt:
  "(\<And>e. cont (eval e)) \<Longrightarrow> \<pi> \<bullet> heapExtend \<rho> h eval = heapExtend (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
unfolding heapExtend_def
  apply (subst fmap_update_eqvt)
  apply (subst fix1_eqvt)
  apply (auto intro: fmap_belowI')[1]
  apply (auto simp add: fmap_bottom_eqvt  Lam_eqvt)
  apply perm_simp
  apply rule
  done

end
