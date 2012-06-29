theory Denotational
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
  apply (auto intro: fmap_belowI' simp add: fmap_bottom_eqvt  Lam_eqvt)
  apply perm_simp
  apply rule
  done

nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
and
  HSem :: "heap => Env => Env" ("\<lbrace> _ \<rbrace>_"  [60,60] 60) 
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk> Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Let as body\<rbrakk>\<^bsub>\<lbrace> asToHeap as \<rbrace>\<rho>\<^esub>"
| "\<lbrace> h \<rbrace>\<rho> = heapExtend \<rho> h ESem"
proof-
have eqvt_at_ESem: "\<And> a b . eqvt_at ESem_HSem_sumC (Inl (a, b)) \<Longrightarrow> eqvt_at (\<lambda>(a, b). ESem a b) (a, b)" sorry
have eqvt_at_HSem: "\<And> a b . eqvt_at ESem_HSem_sumC (Inr (a, b)) \<Longrightarrow> eqvt_at (\<lambda>(a, b). HSem a b) (a, b)" sorry
thm exp_assn.strong_exhaust(1)
{

case goal1 thus ?case
  unfolding eqvt_def ESem_HSem_graph_def
  apply rule
  apply perm_simp
  sorry (* :-( *)

(* Exhaustiveness *)
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Inl a)
    show ?thesis
    proof(cases a)
    case (Pair e \<rho>)
      show ?thesis 
        using Pair Inl goal3
        apply (rule_tac y=e in exp_assn.exhaust(1))
        apply auto[1]
        apply blast
        prefer 2
        apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
        apply (rule_tac y=e and c = \<rho> in exp_assn.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
        done
    qed
  next
  case (Inr a) thus ?thesis using goal3
    apply(case_tac a)
    apply metis
    done
  qed
next
case (goal4 x \<rho> e x' \<rho>' e')
  have eqvt1: "(\<And>xa. eqvt_at (\<lambda>(a, b). ESem a b) (e, \<rho>(x f\<mapsto> xa)))" using goal4 by -(rule eqvt_at_ESem)
  have eqvt2: "(\<And>xa. eqvt_at (\<lambda>(a, b). ESem a b) (e', \<rho>'(x' f\<mapsto> xa)))"  using goal4 by -(rule eqvt_at_ESem)

  have tmp2: "[[atom x]]lst. e = [[atom x']]lst. e'" and rho_eq:"\<rho> = \<rho>'"  using goal4(7) by auto  

  have all_fresh: "(atom x' \<rightleftharpoons> atom x) \<bullet> \<rho>' = \<rho>'" 
    using goal4 `\<rho> = \<rho>'`
    by (auto simp add: swap_fresh_fresh)

  have tmp: "\<And> xa. ESem e (\<rho>(x f\<mapsto> xa)) = ESem e' (\<rho>'(x' f\<mapsto> xa))"
    using eqvt1 eqvt2 tmp2 rho_eq goal4(5) goal4(6)
    apply (simp add: Abs1_eq_iff')
    apply auto

    apply (erule_tac x = xa in meta_allE)
    apply (erule_tac x = xa in meta_allE)
    apply (simp only: eqvt_at_def)
    apply auto

    apply (erule_tac x = "(atom x' \<rightleftharpoons> atom x)" in allE)
    apply (auto simp add: fmap_upd_eqvt permute_Value_def all_fresh)
    done

   show ?case
    apply (simp only: meta_eq_to_obj_eq[OF ESem_def, symmetric, unfolded fun_eq_iff]
      meta_eq_to_obj_eq[OF HSem_def, symmetric, unfolded fun_eq_iff])
    (* No _sum any more at this point! *)
    by (subst tmp, rule)
next
case (goal16 as \<rho> body as' \<rho>' body')
  thus ?case
    apply -
    apply (drule eqvt_at_ESem)
    apply (drule eqvt_at_ESem)
    apply (drule eqvt_at_HSem)
    apply (drule eqvt_at_HSem)
    apply (simp only: meta_eq_to_obj_eq[OF ESem_def, symmetric, unfolded fun_eq_iff]
      meta_eq_to_obj_eq[OF HSem_def, symmetric, unfolded fun_eq_iff])
    (* No _sum any more at this point! *)
    proof- 
      assume eqvt1: "eqvt_at (\<lambda>(a, b). ESem a b) (Terms.Let as body, HSem (asToHeap as) \<rho>)"
      assume eqvt2: "eqvt_at (\<lambda>(a, b). ESem a b) (Terms.Let as' body', HSem (asToHeap as') \<rho>')"
      assume eqvt3: "eqvt_at (\<lambda>(a, b). HSem a b) (asToHeap as, \<rho>)"
      assume eqvt4: "eqvt_at (\<lambda>(a, b). HSem a b) (asToHeap as', \<rho>')"
      assume fresh1: "set (bn as) \<sharp>* \<rho>" and fresh2: "set (bn as') \<sharp>* \<rho>'"
      assume "Inl (Terms.Let as body, \<rho>) = Inl (Terms.Let as' body', \<rho>')"
      hence tmp: "[bn as]lst. (body, as) = [bn as']lst. (body', as')" and rho:"\<rho>' = \<rho>" by auto

      thm Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem (Let as' body) (HSem (asToHeap as) \<rho>))" , OF tmp, simplified]
      thm Abs_lst_fcb2[of "(bn as)" _ "(bn as')"]
      have "ESem (Terms.Let as body) (HSem (asToHeap as) \<rho>) =
            ESem (Terms.Let as' body') (HSem (asToHeap as') \<rho>)"
        apply (rule Abs_lst_fcb[of bn _ _ _ _ "(\<lambda> as (body, as'). ESem (Let as' body) (HSem (asToHeap as) \<rho>))" , OF tmp, simplified])
        apply (rule pure_fresh)+
        using fresh2[unfolded rho]
        apply (clarify)
        proof-
          fix \<pi>
          assume "set (bn (\<pi> \<bullet> as)) \<sharp>* \<rho>" with fresh1
          have "(set (bn as) \<union> set (bn (\<pi> \<bullet> as))) \<sharp>* \<rho>" by (metis fresh_star_Un)
          moreover
          assume "supp \<pi> \<subseteq> set (bn as) \<union> set (bn (\<pi> \<bullet> as))"
          ultimately
          have "\<pi> \<bullet> \<rho> = \<rho>"
            apply -
            apply (rule perm_supp_eq)
            apply (auto intro: perm_supp_eq simp add: fresh_star_def)
            done            
          thus "\<pi> \<bullet> ESem (Terms.Let as body) (HSem (asToHeap as) \<rho>) = ESem (Terms.Let (\<pi> \<bullet> as) (\<pi> \<bullet> body)) (HSem (asToHeap (\<pi> \<bullet> as)) \<rho>)"
             by (simp only: eqvt1[unfolded eqvt_at_def, simplified, rule_format]
                            eqvt3[unfolded eqvt_at_def, simplified, rule_format]
                            asToHeap.eqvt)
        qed
        thus "Inl (ESem (Terms.Let as body) (HSem (asToHeap as) \<rho>)) =
              Inl (ESem (Terms.Let as' body') (HSem (asToHeap as') \<rho>'))" using `\<rho>' = \<rho>`
        by simp
    qed
}
qed auto

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
