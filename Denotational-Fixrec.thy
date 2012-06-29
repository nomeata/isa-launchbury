theory "Denotational-Fixrec"
  imports "Denotational-Common"
begin


instantiation exp :: discrete_cpo
begin
  definition  [simp]: "(x::exp) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instantiation exp_raw :: discr_pt
begin
  definition  [simp]: "(x::exp_raw) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instantiation assn_raw :: discrete_cpo
begin
  definition  [simp]: "(x::assn_raw) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end


(*
find_theorems (100) name:exp name:"split"

definition
  match_Lam :: "exp \<rightarrow> (var \<rightarrow> exp \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Lam = (\<Lambda> e k. case e of (Lam [x]. e) \<Rightarrow> k x e | _ \<Rightarrow>  Fixrec.fail)"

lemma match_Lam_simps [simp]:
  "match_Lam\<cdot>(Lam [x]. e)\<cdot>k = k\<cdot>x\<cdot>e"
  "match_Lam\<cdot>(Var x)\<cdot>k = Fixrec.fail"
unfolding match_Lam_def by simp_all

setup {*
  Fixrec.add_matchers
    [ (@{const_name Lam}, @{const_name match_Lam})) ]
*}
*)

definition
  match_Lam_raw :: "exp_raw \<rightarrow> (var \<rightarrow> exp_raw \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Lam_raw = (\<Lambda> e k. case e of (Lam_raw x e) \<Rightarrow> k \<cdot> x \<cdot> e | _ \<Rightarrow>  Fixrec.fail)"

definition
  match_App_raw :: "exp_raw \<rightarrow> (exp_raw \<rightarrow> var \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_App_raw = (\<Lambda> e k. case e of (App_raw e v) \<Rightarrow> k \<cdot> e \<cdot> v | _ \<Rightarrow>  Fixrec.fail)"

definition
  match_Var_raw :: "exp_raw \<rightarrow> ( var \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Var_raw = (\<Lambda> e k. case e of (Var_raw v) \<Rightarrow> k \<cdot> v | _ \<Rightarrow>  Fixrec.fail)"

definition
  match_Let_raw :: "exp_raw \<rightarrow> (assn_raw \<rightarrow> exp_raw \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Let_raw = (\<Lambda> e k. case e of (Let_raw as e) \<Rightarrow> k \<cdot> as \<cdot> e | _ \<Rightarrow>  Fixrec.fail)"

setup {*
  Fixrec.add_matchers
    [ (@{const_name Lam_raw}, @{const_name match_Lam_raw})
    , (@{const_name App_raw}, @{const_name match_App_raw})
    , (@{const_name Var_raw}, @{const_name match_Var_raw})
    , (@{const_name Let_raw}, @{const_name match_Let_raw})
    ]
*}

lemma match_Lam_raw_simps [simp]:
  "match_Lam_raw\<cdot>(Lam_raw x e)\<cdot>k = k\<cdot>x\<cdot>e"
  "match_Lam_raw\<cdot>(App_raw e x)\<cdot>k = Fixrec.fail"
  "match_Lam_raw\<cdot>(Var_raw x)\<cdot>k = Fixrec.fail"
  "match_Lam_raw\<cdot>(Let_raw as e)\<cdot>k = Fixrec.fail"
unfolding match_Lam_raw_def by simp_all

lemma match_App_raw_simps [simp]:
  "match_App_raw\<cdot>(Lam_raw x e)\<cdot>k = Fixrec.fail"
  "match_App_raw\<cdot>(App_raw e x)\<cdot>k = k\<cdot>e\<cdot>x"
  "match_App_raw\<cdot>(Var_raw x)\<cdot>k = Fixrec.fail"
  "match_App_raw\<cdot>(Let_raw as e)\<cdot>k = Fixrec.fail"
unfolding match_App_raw_def by simp_all

lemma match_Var_raw_simps [simp]:
  "match_Var_raw\<cdot>(Lam_raw x e)\<cdot>k = Fixrec.fail"
  "match_Var_raw\<cdot>(App_raw e x)\<cdot>k = Fixrec.fail"
  "match_Var_raw\<cdot>(Var_raw x)\<cdot>k = k\<cdot>x"
  "match_Var_raw\<cdot>(Let_raw as e)\<cdot>k = Fixrec.fail"
unfolding match_Var_raw_def by simp_all

lemma match_Let_raw_simps [simp]:
  "match_Let_raw\<cdot>(Lam_raw x e)\<cdot>k = Fixrec.fail"
  "match_Let_raw\<cdot>(App_raw e x)\<cdot>k = Fixrec.fail"
  "match_Let_raw\<cdot>(Var_raw x)\<cdot>k = Fixrec.fail"
  "match_Let_raw\<cdot>(Let_raw as e)\<cdot>k = k\<cdot>as\<cdot>e"
unfolding match_Let_raw_def by simp_all

lemma cont2cont_lookup[simp,cont2cont]:
  "cont f \<Longrightarrow> cont (\<lambda>p. the (lookup (f p) x))" sorry

function heapToEnv_raw :: "(var \<times> exp_raw) list \<Rightarrow> (exp_raw \<Rightarrow> Value) \<Rightarrow> Env"
where
  "heapToEnv_raw [] _ = fempty"
| "heapToEnv_raw ((x,e)#h) eval = (heapToEnv_raw h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma cont2cont_heapToEnv_raw[simp, cont2cont]:
  "(\<And> e. cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. heapToEnv_raw h (eval \<rho>))"
  by(induct h, auto)

lemma heapToEnv_raw_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv_raw h eval = heapToEnv_raw (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv_raw.induct, auto simp add: fmap_upd_eqvt  permute_fun_def)

lemma heapToEnv_raw_fdom[simp]:"fdom (heapToEnv_raw h eval) = fst ` set h"
  by (induct h eval rule:heapToEnv_raw.induct, auto)


definition heapExtend_raw :: "Env \<Rightarrow> (var \<times> exp_raw) list \<Rightarrow> (exp_raw \<rightarrow> Env \<rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend_raw \<rho> h eval = fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h))  (\<Lambda> \<rho>'. heapToEnv_raw h (\<lambda> e. eval\<cdot>e\<cdot>\<rho>')))"

lemma heapExtend_raw_eqvt:
  "\<pi> \<bullet> heapExtend_raw \<rho> h eval = heapExtend_raw (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
unfolding heapExtend_raw_def
  apply (subst fmap_update_eqvt)
  apply (subst fix1_eqvt)
  apply (auto intro: fmap_belowI' simp add: fmap_bottom_eqvt  Lam_eqvt)
  apply perm_simp
  apply rule
  done

lemma cont2cont_heapExtend_raw[simp,cont2cont]:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> cont(\<lambda> x. heapExtend_raw (f x) h (g x))" sorry

lemma cont2cont_heapExtend[simp,cont2cont]:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> cont(\<lambda> x. heapExtend (f x) h (g x))" sorry

lemma cont2cont_rep_exp[simp,cont2cont]:
  "cont f \<Longrightarrow> cont(\<lambda> x. rep_exp (f x))" sorry


fixrec
  ESem2 :: "exp_raw \<rightarrow> (Env \<rightarrow> Value)" 
where
  "atom x \<sharp> \<rho> \<Longrightarrow> ESem2\<cdot>(Lam_raw x e) \<cdot> \<rho> = Fn \<cdot> (\<Lambda> v. (ESem2 \<cdot> e \<cdot> (\<rho>(x f\<mapsto> v))))"
| "ESem2\<cdot>(App_raw e x) \<cdot> \<rho> = (ESem2 \<cdot> e \<cdot> \<rho>) \<down>Fn (ESem2 \<cdot> (Var_raw x) \<cdot> \<rho>) "
| "ESem2\<cdot>(Var_raw x) \<cdot> \<rho> = the (lookup \<rho> x)"
| "ESem2\<cdot>(Let_raw as body) \<cdot> \<rho> =  ESem2 \<cdot> body \<cdot> (heapExtend_raw \<rho> (asToHeap_raw as) ESem2)"

definition map_cfun :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<rightarrow> 'b) \<Rightarrow> ('c \<rightarrow> 'd)" where
  "map_cfun f g h = (\<Lambda> x. g (h \<cdot> (f x)))"

definition
  cfun_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<rightarrow> 'b) \<Rightarrow> ('c \<rightarrow> 'd) \<Rightarrow> bool" (infixr "\<cdot>===>" 55)
where
  "cfun_rel A B = (\<lambda>f g. \<forall>x y. A x y \<longrightarrow> B (f\<cdot>x) (g\<cdot>y))"

lemma cfun_quotient3:
  assumes q1: "Quotient3 R1 abs1 rep1"
  and     q2: "Quotient3 R2 abs2 rep2"
  shows "Quotient3 (R1 \<cdot>===> R2) (map_cfun rep1 abs2) (map_cfun abs1 rep2)"
  sorry

declare [[mapQ3 "cfun" = (cfun_rel, cfun_quotient3)]]

definition map_fmap :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('c, 'd) fmap" where
  "map_fmap f g h = undefined"

definition
  fmap_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('c, 'd) fmap \<Rightarrow> bool" (infixr "f===>" 55)
where
  "fmap_rel A B = (\<lambda>f g. undefined)"

lemma fmap_quotient3:
  assumes q1: "Quotient3 R1 abs1 rep1"
  and     q2: "Quotient3 R2 abs2 rep2"
  shows "Quotient3 (R1 f===> R2) (map_fmap rep1 abs2) (map_fmap abs1 rep2)"
  sorry

declare [[mapQ3 "fmap" = (fmap_rel, fmap_quotient3)]]


definition 
  match_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a match \<Rightarrow> 'b match \<Rightarrow> bool"
where
  "match_rel R a b = undefined"

lemma [simp]: "match_rel (op =) = op =" sorry

definition
  map_match :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a match \<Rightarrow> 'b match"
where
  "map_match = undefined"

lemma match_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (match_rel R) (map_match Abs) (map_match Rep)"
  sorry
declare [[mapQ3 "match" = (match_rel, match_quotient)]]

(*
Cannot allow the Nominal constructors in HOLCF as a match_Lam would not
be equivariant (as the continuation might not be)

quotient_definition
  "match_Lam :: exp \<rightarrow> (var \<rightarrow> exp \<rightarrow> 'b match) \<rightarrow> 'b match"
  is "match_Lam_raw"
unfolding cfun_rel_def
apply auto
thm alpha_exp_raw.cases
apply (erule alpha_exp_raw.cases)
unfolding match_Lam_raw_def
apply auto
*)

quotient_definition  "ESem3 :: exp \<rightarrow> Env \<rightarrow> Value" is ESem2
unfolding cfun_rel_def
find_theorems alpha_exp_raw
apply rule
apply rule
apply rule
apply (rule cfun_eqI)

apply (induct rule:ESem2.induct)
apply auto

apply (erule alpha_exp_raw.cases)
apply auto

defer
apply (rule cfun_eqI, simp)



oops

(*
find_theorems ESem2
apply (induct rule:ESem2.induct)
find_theorems name:alpha_exp_raw
apply auto
apply (erule alpha_exp_raw_alpha_assn_raw_alpha_bn_raw.inducts)
apply auto
*)


end
