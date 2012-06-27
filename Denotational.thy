theory Denotational
  imports Terms Heap "FMap-HOLCF" "FMap-Nominal" "~~/src/HOL/HOLCF/Library/Option_Cpo" "~~/src/HOL/HOLCF/HOLCF"  
begin

default_sort cpo

instantiation var :: discrete_cpo
begin
  definition  [simp]: "(x::var) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

class cont_pt = 
  cpo + 
  pt +
  assumes perm_cont: "\<And>p. cont ((permute p) :: 'a::{cpo,pt} \<Rightarrow> 'a)"

lemma (in cont_pt) perm_cont_simp[simp]: "\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> y \<longleftrightarrow> x \<sqsubseteq> y"
  apply rule
  apply (drule cont2monofunE[OF perm_cont, of _ _ "-\<pi>"], simp)[1]
  apply (erule cont2monofunE[OF perm_cont, of _ _ "\<pi>"])
  done

lemmas perm_cont2cont[simp,cont2cont] = cont_compose[OF perm_cont]

lemma perm_bottom[simp,eqvt]: "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})"
using [[show_sorts]] [[show_types]]
  proof-
  have "\<bottom> \<sqsubseteq> -\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  thm cont2monofunE[OF perm_cont]
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> \<pi> \<bullet> (-\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo}))" by(rule cont2monofunE[OF perm_cont])
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  thus "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})" by simp
qed

instance var :: cont_pt  by default auto

(*
lemma cont_transfer[transfer_rule]: "((cr_fmap ===> cr_fmap) ===> op =) (cont :: (('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)) \<Rightarrow> bool)  (cont :: (('a, 'b::cpo) fmap \<Rightarrow> ('a, 'b) fmap) \<Rightarrow> bool) "
  apply (rule fun_relI)+
  apply (erule fun_relE)
  find_theorems name:fun_rel
  
  thm fun_relI
  unfolding cr_fmap_def
  apply auto
  unfolding cont_def
*)

lemma image_eqvt[eqvt]: "\<pi> \<bullet> (f ` S) = (\<pi> \<bullet> f) ` (\<pi> \<bullet> S)"
  unfolding permute_set_def permute_fun_def
  by (auto simp add: image_def)

lemma range_eqvt: "\<pi> \<bullet> range Y = range (\<pi> \<bullet> Y)"
  unfolding image_eqvt UNIV_eqvt ..


instance "fmap" :: (cont_pt, cont_pt) cont_pt
apply default
proof(rule contI2, rule monofunI)
  fix \<pi> m1 m2
  assume "m1 \<sqsubseteq> (m2 :: ('a, 'b) fmap)"
  hence "fdom m1 = fdom m2"
    by (rule fmap_below_dom)
  show "\<pi> \<bullet> m1 \<sqsubseteq> \<pi> \<bullet> m2"
  proof (rule fmap_belowI')
    show "fdom (\<pi> \<bullet> m1) = fdom (\<pi> \<bullet> m2)"
      using `fdom m1 = fdom m2`
      by (simp add: fdom_perm del: fdom_perm_rev)
  next
    fix x
    assume "x \<in> fdom (\<pi> \<bullet> m1)" and "x \<in> fdom (\<pi> \<bullet> m2)"
    moreover
    obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
    ultimately
    have "x2 \<in> fdom m1" "x2 \<in> fdom m2"
      using `x \<in> fdom (\<pi> \<bullet> m1)` `x \<in> fdom (\<pi> \<bullet> m2)`
      by (simp add: fdom_perm mem_permute_iff del: fdom_perm_rev)+

    have "the (lookup (\<pi> \<bullet> m1) x) = \<pi> \<bullet> the (lookup m1 x2)"
      by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m1`]  `x = _`)
    also have "... \<sqsubseteq> \<pi> \<bullet> the (lookup m2 x2)"
      by -(subst perm_cont_simp, rule fmap_belowE[OF `m1 \<sqsubseteq> m2`])
    also have "... \<sqsubseteq> the (lookup (\<pi> \<bullet> m2) x)"
      using `x = _`
      by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m2`]  )
    finally show "the (lookup (\<pi> \<bullet> m1) x) \<sqsubseteq> the (lookup (\<pi> \<bullet> m2) x)".
  qed
next
  fix \<pi> Y
  assume "chain (Y\<Colon>nat \<Rightarrow> ('a, 'b) fmap)"
  assume "chain (\<lambda>i. \<pi> \<bullet> Y i)"
  
  show "\<pi> \<bullet> (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. \<pi> \<bullet> Y i) "
  proof(rule fmap_belowI')
    show "fdom (\<pi> \<bullet> (\<Squnion> i. Y i)) = fdom (\<Squnion> i. \<pi> \<bullet> Y i)"
      by (simp add: chain_fdom(2)[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`] chain_fdom(2)[OF `chain Y`] fdom_perm del: fdom_perm_rev)
  next
    fix x
    assume "x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))"
    moreover
    obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
    ultimately
    have "x2 \<in> fdom (\<Squnion> i. Y i)"
      using `x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))` 
      by (simp add: fdom_perm mem_permute_iff del: fdom_perm_rev)+
    hence "x2 \<in> fdom (Y 0)"
      by (simp add: chain_fdom(2)[OF `chain Y`])
      
    assume  "x \<in> fdom (\<Squnion> i. \<pi> \<bullet> Y i) "
    hence "x \<in> fdom (\<pi> \<bullet> Y 0)"
      by (simp add: chain_fdom(2)[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`])

    have "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) = \<pi> \<bullet> (the (lookup (\<Squnion> i. Y i) x2))"
      by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom (\<Squnion> i. Y i)`]  `x = _`)
    also have "... = \<pi> \<bullet> (\<Squnion>i. (the (lookup (Y i) x2)))"
      by (subst lookup_cont[OF `chain Y` `x2 \<in> fdom (Y 0)`], rule refl)
    also have "... = (\<Squnion>i. \<pi> \<bullet> (the (lookup (Y i) x2)))"
      by (rule cont2contlubE[OF perm_cont, OF lookup_chain[OF `chain Y` `x2 \<in> fdom (Y 0)`]])
    also have "... = (\<Squnion>i. the (lookup (\<pi> \<bullet> (Y i)) x))"
      using `x2 \<in> fdom (Y 0)` chain_fdom(1)[OF `chain Y`] `x = _`
      apply (subst the_lookup_eqvt)
      apply auto
      done
    also have "... = the (lookup (\<Squnion>i. \<pi> \<bullet> (Y i)) x)"
      by (subst lookup_cont[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)` `x \<in> fdom (\<pi> \<bullet> Y 0)`], rule refl)
    finally
    have "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) = the (lookup (\<Squnion> i. \<pi> \<bullet> Y i) x)" .
    thus "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) \<sqsubseteq> the (lookup (\<Squnion> i. \<pi> \<bullet> Y i) x)" by auto
  qed
qed


instantiation "cfun" :: (cont_pt, cont_pt) pt
begin
  definition "p \<bullet> (f :: 'a  \<rightarrow> 'b) = (\<Lambda> x. p \<bullet> (f \<cdot> (- p \<bullet> x)))"

  instance
  apply(default)
  apply (simp add: permute_cfun_def eta_cfun)
  apply (simp add: permute_cfun_def cfun_eqI minus_add)
  done
end


lemma Lam_eqvt:
  "cont f \<Longrightarrow> \<pi> \<bullet> Abs_cfun f = Abs_cfun (\<pi> \<bullet> f)"
  unfolding permute_fun_def permute_cfun_def
  by auto

lemma Cfun_app_eqvt[eqvt]:
  "\<pi> \<bullet> (f \<cdot> x) = (\<pi> \<bullet> f) \<cdot> (\<pi> \<bullet> x)"
  unfolding permute_cfun_def
  by auto
(*
lemma Rep_cfun_eqvt[eqvt]:
  "\<pi> \<bullet> (Rep_cfun f) = Rep_cfun (\<pi> \<bullet> f)"
  unfolding permute_cfun_def permute_fun_def
  by auto
*)

lemma fix1_eqvt:
  "x \<sqsubseteq> f\<cdot>x \<Longrightarrow> \<pi> \<bullet> fix1 x f = fix1 (\<pi> \<bullet> x) (\<pi> \<bullet> f)"
  by (rule parallel_fix1_ind)(auto dest:cont2monofunE[OF perm_cont] simp add: Cfun_app_eqvt)

lemma option_case_eqvt[eqvt]:
  "\<pi> \<bullet> option_case d f x = option_case (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  by(cases x, auto simp add: permute_fun_def)

(*
lemma lub_eqvt[eqvt]:
  "chain S \<Longrightarrow> \<pi> \<bullet> lub (S:: ('a :: cont_pt) set) = lub (\<pi> \<bullet> S)"
apply(rule lub_eqI[symmetric])
apply(rule is_lubI)
apply(rule is_ubI)
unfolding permute_set_def
apply (auto)
apply (erule is_ubD[rotated])


apply (erule is_ubE)
thm cont2monofunE[OF perm_cont, OF is_ubD[rotated]]
apply (drule cont2monofunE[OF perm_cont, OF is_ubD[rotated]])

  proof (rule is_lubI)
*)

lemma finite_transfer[transfer_rule]: "(op = ===> op =) finite finite" 
  unfolding fun_rel_eq by (rule refl)

lemma fdom_fmap_bottom: "finite S \<Longrightarrow> fdom (fmap_bottom S) = S"
  by (transfer, auto simp add: dom_def)

lemma fmap_bottom_eqvt:
  "finite S \<Longrightarrow> \<pi> \<bullet> (fmap_bottom S :: ('a::pt, 'b::{cont_pt,pcpo}) fmap) = fmap_bottom (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

lemma fmap_update_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_update m1 (m2 :: ('a::{cont_pt,cpo}, 'b::{cont_pt,cpo}) fmap) = fmap_update (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  by (transfer, perm_simp, rule refl)


class pure_cpo = Nominal2_Base.pure + cpo

instance pure_cpo \<subseteq> cont_pt
  apply default
  proof-
    fix p :: perm
    have "permute p = ((\<lambda>x. x) :: 'a \<Rightarrow> 'a)" by(rule)(rule permute_pure)
    thus "cont (permute p :: 'a \<Rightarrow> 'a)" by (auto)
  qed

instance "cfun" :: (pure_cpo, pure_cpo) pure_cpo
  apply default
  apply (auto  simp add: permute_cfun_def permute_pure Cfun.cfun.Rep_cfun_inverse)
  done

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

lemma fresh_star_singleton: "{ x } \<sharp>* e \<longleftrightarrow> x \<sharp> e"
  by (simp add: fresh_star_def)

function heapToEnv :: "heap \<Rightarrow> (exp \<Rightarrow> Value) \<Rightarrow> Env"
where
  "heapToEnv [] _ = fempty"
| "heapToEnv ((x,e)#h) eval = (heapToEnv h eval) (x f\<mapsto> eval e)"
by (pat_completeness, auto)
termination by lexicographic_order

lemma heapToEnv_eqvt[eqvt]:
  "\<pi> \<bullet> heapToEnv h eval = heapToEnv (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h eval rule:heapToEnv.induct, auto simp add: fmap_upd_eqvt  permute_fun_def)

lemma heapToEnv_fdom[simp]:"fdom (heapToEnv h eval) = fst ` set h"
  by (induct h eval rule:heapToEnv.induct, auto)

lemma fmap_bottom_lookup[simp]: "\<lbrakk> x \<in> S ; finite S \<rbrakk> \<Longrightarrow> lookup (fmap_bottom S) x = Some \<bottom>"
  by (transfer, auto)

definition heapExtend :: "Env \<Rightarrow> heap \<Rightarrow> (Env \<Rightarrow> exp \<Rightarrow> Value)  \<Rightarrow> (var, Value) fmap"
  where
  "heapExtend \<rho> h eval = fmap_update \<rho> (fix1 (fmap_bottom (fst ` set h))  (\<Lambda> \<rho>'. heapToEnv h (eval \<rho>')))"

lemma heapExtend_eqvt[eqvt]:
  "\<pi> \<bullet> heapExtend \<rho> h eval = heapExtend (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
unfolding heapExtend_def
apply (subst fmap_update_eqvt)
apply (subst fix1_eqvt)
apply (subst beta_cfun)
defer
apply (rule fmap_belowI')
apply simp
apply simp
apply (subst fmap_bottom_eqvt)
apply simp
apply (subst Lam_eqvt)
defer
apply perm_simp
apply rule
(* Goal here: cont (\<lambda>\<rho>'. heapToEnv h (eval \<rho>'))  *)

sorry


nominal_primrec
  ESem :: "exp \<Rightarrow> Env \<Rightarrow> Value" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
and
  HSem :: "heap => Env => Env" ("\<lbrace> _ \<rbrace>_"  [60,60] 60) 
where
  "atom x \<sharp> \<rho> ==> \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = Fn \<cdot> (\<Lambda> v. (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
| "\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> "
| "\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub> = the (lookup \<rho> x)"
| "set (bn as) \<sharp>* \<rho> \<Longrightarrow>\<lbrakk> Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Let as body\<rbrakk>\<^bsub>\<lbrace> asToHeap as \<rbrace>\<rho>\<^esub>"
| "\<lbrace> h \<rbrace>\<rho> = heapExtend \<rho> h (\<lambda> \<rho>' e . \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
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

end
