theory Sestoft 
imports Terms Substitution
begin

datatype stack_elem = Arg var | Upd var

instantiation stack_elem :: pt
begin
definition  "\<pi> \<bullet> x = (case x of (Arg v) \<Rightarrow> Arg (\<pi> \<bullet> v) | (Upd v) \<Rightarrow> Upd (\<pi> \<bullet> v))"
instance
  by default (auto simp add: permute_stack_elem_def split:stack_elem.split)
end

lemma Arg_eqvt[eqvt]: "\<pi> \<bullet> (Arg v) = Arg (\<pi> \<bullet> v)"
  and Upd_eqvt[eqvt]: "\<pi> \<bullet> (Upd v) = Upd (\<pi> \<bullet> v)"
  by (auto simp add: permute_stack_elem_def split:stack_elem.split)

lemma supp_Arg[simp]: "supp (Arg v) = supp v"  unfolding supp_def by auto
lemma supp_Upd[simp]: "supp (Upd v) = supp v"  unfolding supp_def by auto
lemma fresh_Arg[simp]: "a \<sharp> Arg v = a \<sharp> v" unfolding fresh_def by auto
lemma fresh_Upd[simp]: "a \<sharp> Upd v = a \<sharp> v" unfolding fresh_def by auto

instance stack_elem :: fs  by (default, case_tac x) (auto simp add: finite_supp)

type_synonym stack = "stack_elem list"
type_synonym conf = "(heap \<times> exp \<times> stack)"

nominal_function isLam :: "exp \<Rightarrow> bool" where
  "isLam (Var x) = False" |
  "isLam (Lam [x]. e) = True" |
  "isLam (App e x) = False" |
  "isLam (Let as e) = False"
  unfolding isLam_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_strong_exhaust)
  apply auto
  done
nominal_termination (eqvt) by lexicographic_order

lemma isLam_Lam: "isLam (Lam [x]. e)" by simp

inductive step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  app\<^sub>1:  "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e , Arg x # S)"
| app\<^sub>2:  "(\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> (\<Gamma>, e[y ::= x] , S)"
| var\<^sub>1:  "map_of \<Gamma> x = Some e \<Longrightarrow> (\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e , Upd x # S)"
| var\<^sub>2:  "isLam e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<Rightarrow> ((x,e)# \<Gamma>, e , S)"
| let\<^sub>1:  "atom ` domA \<Delta> \<sharp>* (\<Gamma>, S) \<Longrightarrow> (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> (\<Delta>@\<Gamma>, e , S)"

abbreviation steps (infix "\<Rightarrow>\<^sup>*" 50) where "steps \<equiv> step\<^sup>*\<^sup>*"

end
