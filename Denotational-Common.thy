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

lemma sharp_star_Env: "set (bn as) \<sharp>* (\<rho> :: Env) \<longleftrightarrow> (\<forall> x \<in> fst`set (asToHeap as) . x \<notin> fdom \<rho>)"
  by(induct rule:asToHeap.induct, auto simp add: fresh_star_def exp_assn.bn_defs sharp_Env)

lemma sharp_star_Env': "atom ` fst ` set \<Gamma> \<sharp>* (\<rho> :: Env) \<longleftrightarrow> fst ` set \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct rule:asToHeap.induct, auto simp add: fresh_star_def exp_assn.bn_defs sharp_Env)

lemma perm_still_cont: "cont (\<pi> \<bullet> f) = cont (f :: ('a :: cont_pt) \<Rightarrow> ('b :: cont_pt))"
proof
  have imp:"\<And> (f :: 'a \<Rightarrow> 'b) \<pi>. cont f \<Longrightarrow> cont (\<pi> \<bullet> f)"
    unfolding permute_fun_def
    by (metis cont_compose perm_cont)
  show "cont f \<Longrightarrow> cont (\<pi> \<bullet> f)" using imp[of "f" "\<pi>"].
  show "cont (\<pi> \<bullet> f) \<Longrightarrow> cont (f)" using imp[of "\<pi> \<bullet> f" "-\<pi>"] by simp
qed


end
