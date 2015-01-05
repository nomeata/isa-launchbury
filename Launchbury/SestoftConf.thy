theory SestoftConf
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
fun upds_list :: "stack \<Rightarrow> var list" where
  "upds_list [] = []"
| "upds_list (Upd x # S) = x # upds_list S"
| "upds_list (Arg x # S) = upds_list S"
| "upds_list (Dummy x # S) = upds_list S"

lemma set_upds_list[simp]:
  "set (upds_list S) = upds S"
  by (induction S rule: upds_list.induct) auto

lemma ups_fv_subset: "upds S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto
lemma ap_fv_subset: "ap S \<subseteq> fv S"
  by (induction S rule: upds.induct) auto

lemma fresh_flattn[simp]: "a \<sharp> flattn S \<longleftrightarrow> a \<sharp> S"
  by (induction S rule:flattn.induct) (auto simp add: fresh_Nil fresh_Cons)
lemma fresh_star_flattn[simp]: "a \<sharp>* flattn S \<longleftrightarrow> a \<sharp>* S"
  by (auto simp add: fresh_star_def)

type_synonym conf = "(heap \<times> exp \<times> stack)"

inductive boring_step where
  "isLam e \<Longrightarrow> boring_step (\<Gamma>, e, Upd x # S)"


fun heap_upds_ok where "heap_upds_ok (\<Gamma>,S) \<longleftrightarrow> domA \<Gamma> \<inter> upds S = {} \<and> distinct (upds_list S)"

lemma heap_upds_okE: "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> upds S"
  by auto

lemma heap_upds_ok_Nil[simp]: "heap_upds_ok (\<Gamma>, [])" by auto
lemma heap_upds_ok_app1: "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (\<Gamma>,Arg x # S)" by auto
lemma heap_upds_ok_app2: "heap_upds_ok (\<Gamma>, Arg x # S) \<Longrightarrow> heap_upds_ok (\<Gamma>, S)" by auto

lemma heap_upds_ok_append:
  assumes "domA \<Delta> \<inter> domA \<Gamma> = {}"
  assumes "domA \<Delta> \<inter> upds S = {}"
  assumes "heap_upds_ok (\<Gamma>,S)"
  shows "heap_upds_ok (\<Delta>@\<Gamma>, S)"
  using assms
  unfolding heap_upds_ok.simps
  by auto

lemma heap_upds_ok_to_stack:
  "x \<in> domA \<Gamma> \<Longrightarrow> heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok (delete x \<Gamma>, Upd x #S)"
  by (auto)

lemma heap_upds_ok_to_heap:
  "heap_upds_ok (\<Gamma>, Upd x # S) \<Longrightarrow> heap_upds_ok ((x,e) # \<Gamma>, S)"
  by (auto)

lemma heap_upds_ok_reorder:
  "x \<in> domA \<Gamma> \<Longrightarrow> heap_upds_ok (\<Gamma>, S) \<Longrightarrow> heap_upds_ok ((x,e) # delete x \<Gamma>, S)"
  by (intro heap_upds_ok_to_heap heap_upds_ok_to_stack)

lemmas heap_upds_ok_intros[intro] = heap_upds_ok_to_heap heap_upds_ok_to_stack heap_upds_ok_reorder heap_upds_ok_app1 heap_upds_ok_app2
lemmas heap_upds_ok.simps[simp del]

fun restr_stack :: "var set \<Rightarrow> stack \<Rightarrow> stack"
  where "restr_stack V [] = []"
      | "restr_stack V (Arg x # S) = Arg x # restr_stack V S"
      | "restr_stack V (Upd x # S) = (if x \<in> V then Upd x # restr_stack V S else restr_stack V S)"
      | "restr_stack V (Dummy x # S) = Dummy x # restr_stack V S"

lemma restr_stack_cong:
  "(\<And> x. x \<in> upds S \<Longrightarrow> x \<in> V \<longleftrightarrow> x \<in> V') \<Longrightarrow> restr_stack V S = restr_stack V' S"
  by (induction V S rule: restr_stack.induct) auto

lemma upds_restr_stack[simp]: "upds (restr_stack V S) = upds S \<inter> V"
  by (induction V S rule: restr_stack.induct) auto

lemma fresh_star_restict_stack[intro]:
  "a \<sharp>* S \<Longrightarrow> a \<sharp>* restr_stack V S"
  by (induction V S rule: restr_stack.induct) (auto simp add: fresh_star_Cons)


end
