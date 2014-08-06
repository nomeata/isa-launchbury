theory Sestoft 
imports Terms Substitution
begin

datatype stack_elem = Arg var | Upd var | Dummy var

instantiation stack_elem :: pt
begin
definition  "\<pi> \<bullet> x = (case x of (Arg v) \<Rightarrow> Arg (\<pi> \<bullet> v) | (Upd v) \<Rightarrow> Upd (\<pi> \<bullet> v) | (Dummy v) \<Rightarrow> Dummy (\<pi> \<bullet> v))"
instance
  by default (auto simp add: permute_stack_elem_def split:stack_elem.split)
end

lemma Arg_eqvt[eqvt]: "\<pi> \<bullet> (Arg v) = Arg (\<pi> \<bullet> v)"
  and Upd_eqvt[eqvt]: "\<pi> \<bullet> (Upd v) = Upd (\<pi> \<bullet> v)"
  and Dummy_eqvt[eqvt]: "\<pi> \<bullet> (Dummy v) = Dummy (\<pi> \<bullet> v)"
  by (auto simp add: permute_stack_elem_def split:stack_elem.split)

lemma supp_Arg[simp]: "supp (Arg v) = supp v"  unfolding supp_def by auto
lemma supp_Upd[simp]: "supp (Upd v) = supp v"  unfolding supp_def by auto
lemma supp_Dummy[simp]: "supp (Dummy v) = supp v"  unfolding supp_def by auto
lemma fresh_Arg[simp]: "a \<sharp> Arg v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Upd[simp]: "a \<sharp> Upd v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Dummy[simp]: "a \<sharp> Dummy v = a \<sharp> v" unfolding fresh_def by auto
lemma fv_Arg[simp]: "fv (Arg v) = fv v"  unfolding fv_def by auto
lemma fv_Upd[simp]: "fv (Upd v) = fv v"  unfolding fv_def by auto

instance stack_elem :: fs  by (default, case_tac x) (auto simp add: finite_supp)

type_synonym stack = "stack_elem list"

fun ap :: "stack \<Rightarrow> var set" where
  "ap [] = {}"
| "ap (Arg x # S) = insert x (ap S)"
| "ap (Upd x # S) = ap S"
| "ap (Dummy x # S) = ap S"
fun upds :: "stack \<Rightarrow> var set" where
  "upds [] = {}"
| "upds (Upd x # S) = insert x (upds S)"
| "upds (Arg x # S) = upds S"
| "upds (Dummy x # S) = upds S"
fun flattn :: "stack \<Rightarrow> var list" where
  "flattn [] = []"
| "flattn (Upd x # S) = x # flattn S"
| "flattn (Arg x # S) = x # flattn S"
| "flattn (Dummy x # S) = x # flattn S"

lemma ups_fv_subset: "upds S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto

lemma fresh_flattn[simp]: "a \<sharp> flattn S \<longleftrightarrow> a \<sharp> S"
  by (induction S rule:flattn.induct) (auto simp add: fresh_Nil fresh_Cons)
lemma fresh_star_flattn[simp]: "a \<sharp>* flattn S \<longleftrightarrow> a \<sharp>* S"
  by (auto simp add: fresh_star_def)

type_synonym conf = "(heap \<times> exp \<times> stack)"


inductive step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  app\<^sub>1:  "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e , Arg x # S)"
| app\<^sub>2:  "(\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> (\<Gamma>, e[y ::= x] , S)"
| var\<^sub>1:  "map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e , Upd x # S)"
| var\<^sub>2:  "map_of \<Gamma> x = Some e \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow> ((x,e) # delete x \<Gamma>, e , S)"
| var\<^sub>3:  "x \<notin> domA \<Gamma> \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<Rightarrow> ((x,e)# \<Gamma>, e , S)"
| let\<^sub>1:  "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> (\<Delta>@\<Gamma>, e , S)"

abbreviation steps (infix "\<Rightarrow>\<^sup>*" 50) where "steps \<equiv> step\<^sup>*\<^sup>*"

lemma SmartLet_stepI:
   "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, SmartLet \<Delta> e, S) \<Rightarrow>\<^sup>*  (\<Delta>@\<Gamma>, e , S)"
unfolding SmartLet_def by (auto intro: let\<^sub>1)

end
