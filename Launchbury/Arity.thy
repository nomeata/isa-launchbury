theory Arity
imports "HOLCF-Join-Classes" Lifting
begin

typedef Arity = "UNIV :: nat set" by auto


setup_lifting type_definition_Arity

(*
instantiation Arity :: order
begin
lift_definition less_eq_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . x \<le> y".
lift_definition less_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . x < y".
instance
  apply default
  apply (transfer, fastforce)+
  done
end
*)


lift_definition inc_Arity :: "Arity \<Rightarrow> Arity" is Suc.
lift_definition pred_Arity :: "Arity \<Rightarrow> Arity" is "(\<lambda> x . x - 1)".

instantiation Arity :: po
begin

lift_definition below_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . y \<le> x".

instance
apply default
apply ((transfer, auto)+)
done
end

instance Arity :: cpo
apply default
proof-
  fix S  :: "nat \<Rightarrow> Arity"
  assume "chain S"

  have "LeastM Rep_Arity (\<lambda>x. x \<in> range S) \<in> range S"
    by (rule LeastM_natI) auto
  then obtain n where n: "S n = LeastM Rep_Arity (\<lambda>x. x \<in> range S)" by auto
  have "max_in_chain n S"
  proof(rule max_in_chainI)
    fix j
    assume "n \<le> j" hence "S n \<sqsubseteq> S j" using `chain S` by (metis chain_mono)
    also
    have "Rep_Arity (S n) \<le> Rep_Arity (S j)"
      unfolding n image_def
      by (metis (lifting, full_types) LeastM_nat_lemma UNIV_I mem_Collect_eq)
    hence "S j \<sqsubseteq> S n" by transfer
    finally  
    show "S n = S j".
  qed
  thus "\<exists>x. range S <<| x" using `chain S`  by (metis lub_finch1)
qed

definition
  inc  :: "Arity -> Arity" where
  "inc = (\<Lambda> x. inc_Arity x)"

definition
  pred  :: "Arity -> Arity" where
  "pred = (\<Lambda> x. pred_Arity x)"



instance Arity :: Finite_Join_cpo
proof default
  fix x y :: Arity
  have "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by transfer auto
  thus "compatible x y" by (metis below_refl compatibleI)
qed

instantiation Arity :: zero
begin
lift_definition zero_Arity :: Arity is 0.
instance ..
end

lemma Arity_zero_top[simp]: "(x :: Arity) \<sqsubseteq> 0"
  by transfer simp

lemma Arity_zero_join[simp]: "(x :: Arity) \<squnion> 0 = 0"
  by transfer simp
lemma Arity_zero_join2[simp]: "0 \<squnion> (x :: Arity) = 0"
  by transfer simp

lemma Arity_up_zero_join[simp]: "(x :: Arity\<^sub>\<bottom>) \<squnion> up\<cdot>0 = up\<cdot>0"
  by (cases x) auto
lemma Arity_up_zero_join2[simp]: "up\<cdot>0 \<squnion> (x :: Arity\<^sub>\<bottom>) = up\<cdot>0"
  by (cases x) auto


end
