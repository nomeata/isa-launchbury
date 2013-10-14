theory "LaunchburyCombined-Unstack"
imports LaunchburyCombined LaunchburyCombinedTaggedMap
begin

subsubsection {* Stacked evaluation implies original evaluation. *}

nominal_primrec convert_stack_elem  :: "exp \<Rightarrow> var list" where
  "convert_stack_elem (Var x) = [x]" |
  "convert_stack_elem (App e x) = [x]" |
  "convert_stack_elem (Lam [x]. e) = []" |
  "convert_stack_elem (Let as e) = []"
  unfolding convert_stack_elem_graph_def convert_stack_elem_graph_aux_def eqvt_def
  apply (rule, simp)
  apply rule
  apply (metis exp_assn.exhaust(1))
  apply auto
  done
termination (eqvt) by lexicographic_order

fun convert_stack :: "'a f\<rightharpoonup> exp \<Rightarrow> 'a list \<Rightarrow> var list" where
  "convert_stack \<Gamma> [] = []" |
  "convert_stack \<Gamma> (x#xs) = (if x \<in> fdom \<Gamma> then convert_stack_elem (\<Gamma> f! x) else []) @ convert_stack \<Gamma> xs"

lemma fresh_convert_stack_subset:
  fixes S :: "('a::fs) list"
  shows "a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> convert_stack \<Gamma> S"
  by (induction S)
     (auto simp add: fresh_Nil fresh_append fresh_lookup_fdom eqvt_fresh_cong1[OF convert_stack_elem.eqvt])

lemma convert_stack_upd_not_there[simp]:
  assumes "x \<notin> set S"
  shows "convert_stack (\<Gamma>(x f\<mapsto> e)) S = convert_stack \<Gamma> S"
using assms by (induction S) auto

lemma convert_stack_delete_not_there[simp]:
  assumes "x \<notin> set S"
  shows "convert_stack (fmap_delete x \<Gamma>) S = convert_stack \<Gamma> S"
using assms by (induction S) auto

lemma convert_stack_fmap_add_not_there[simp]:
  assumes "fdom m \<inter> set S = {}"
  shows "convert_stack (\<Gamma> f++ m) S = convert_stack \<Gamma> S"
using assms by (induction S) auto

(* Not really semantically correct, but might be a nice trick. *)
lemma convert_stack_app_to_var[simp]:
  "convert_stack (\<Gamma>(x f\<mapsto> App e y)) S =  convert_stack (\<Gamma>(x f\<mapsto> Var y)) S"
by (induction S, case_tac [2] "a = x") auto

lemma convert_stack_subset:
  assumes "\<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<surd>\<^bsub>x#S\<^esub> \<Delta>"
  assumes "x \<notin> set S"
  assumes "set S \<subseteq> fdom \<Gamma>"
  shows "convert_stack \<Delta> S = convert_stack \<Gamma> S"
  using stack_unchanged[OF assms(1), simplified] reds_doesnt_forget[OF assms(1)] assms(2)
  by (induction S) (auto simp add: fdomIff)

lemma forget_stack:
  assumes "\<Gamma> \<Down>\<^sup>\<times>\<^sup>u\<^sup>\<surd>\<^bsub>S\<^esub> \<Delta>"
  assumes "distinct S"
  assumes "set S \<subseteq> fdom \<Gamma>"
  shows "\<Gamma> f|` (-set S) : \<Gamma> f! hd S \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>convert_stack \<Gamma> (tl S)\<^esub> \<Delta> f|` (-set S) : \<Delta> f! hd S"
using assms
proof (nominal_induct \<Gamma> \<times> u \<surd> S \<Delta>  rule: LaunchburyCombinedTaggedMap.reds.strong_induct)
case Lambda
  show ?case by (auto intro: LambdaI)
next
case (Application n \<Gamma> x e y S z \<Delta> \<Theta> e' u)

  note `lookup \<Delta> n = Some (Lam [z]. e')`[simp]

  from `atom n \<sharp> \<Gamma>` have "n \<notin> fdom \<Gamma>" by (metis fresh_fdom)
  hence [simp]: "\<Gamma> f|` (- insert n (insert x  (set S))) = \<Gamma> f|` (- insert x  (set S))" by auto
  from `atom n \<sharp> x` have [simp]: "x \<noteq> n" by (metis not_self_fresh)

  have [simp]: "z \<noteq> n" by (metis (mono_tags) Application.hyps(11) Application.hyps(15) fresh_fdom hd.simps stack_bound)

  have [simp]: "fmap_delete n \<Delta> f|` (- insert x (set S)) = \<Delta> f|` (- insert n (insert x (set S)))" by auto

  have [simp]: "n \<notin> set S" by (metis Application.hyps(5) fresh_at_base_list)

  have [simp]: "\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e) f|` insert x (set S) = \<Gamma>(x f\<mapsto> App (Var n) y) f|` insert x (set S)" 
    apply (rule fmap_eqI)
    apply auto
    apply (case_tac "xa = x \<or> xa = n")
    apply auto
    done
    
  from `distinct (x # S)` have [simp]: "x \<notin> set S" "distinct S" by simp_all
 
  let ?S' = "convert_stack \<Gamma> S"
  
  have "distinct (n # x # S)" using `x \<noteq> n` by (simp del: `x \<noteq> n`)
  from Application.hyps(16)[OF this] Application.prems(2)
  have hyp1: "\<Gamma> f|` (- insert x (set S)) : e \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>y#?S'\<^esub> \<Delta> f|` (- insert n (insert x (set S))) : Lam [z]. e'"
    by auto

  from reds_doesnt_forget[OF Application.hyps(15)]
  have [simp]: "x \<in> fdom \<Delta>" by simp
  
  from stack_unchanged[OF Application.hyps(15), where x = x]
  have [simp]: "\<Delta> f! x = App (Var n) y" by simp

  have "n \<notin> set (x # S)" using `x \<noteq> n` by (simp del: `x \<noteq> n`)
  
  from Application.prems(2)
  have prem2: "set (x # S) \<subseteq> fdom (\<Gamma>(x f\<mapsto> App (Var n) y)(n f\<mapsto> e))" by auto
  from  convert_stack_subset[OF Application.hyps(15) `n \<notin> set (x #S)` this]
  have [simp]: "convert_stack \<Delta> S = convert_stack \<Gamma> S" by simp

  from Application.prems(2) reds_doesnt_forget[OF Application.hyps(15)]
  have "set (x # S) \<subseteq> fdom (fmap_delete n \<Delta>(x f\<mapsto> e'[z::=y]))" by auto

  from Application.hyps(18)[OF Application.prems(1) this]
  have hyp2': "\<Delta> f|` (- insert n (insert x (set S))) : e'[z::=y] \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>?S'\<^esub> \<Theta> f|` (- insert x (set S)) : \<Theta> f! x"
    by simp

  have "x \<in> fdom \<Theta>" by (metis LaunchburyCombinedTaggedMap.reds_doesnt_forget[OF Application.hyps(17)] fmap_upd_fdom insert_subset)

  have "\<Gamma> f|` (- insert x (set S)) : App e y \<Down>\<^sup>\<times>\<^sup>\<surd>\<^bsub>?S'\<^esub> \<Theta> f|` (- insert x (set S)) : \<Theta> f! x"
    apply (rule LaunchburyCombined.reds.Application[OF _ hyp1 hyp2'])
    using Application(1,2,6-12) `x \<in> fdom \<Theta>`
    by (auto simp add: fresh_Pair fresh_fmap_restr_subset fresh_convert_stack_subset fresh_fmap_upd_eq fresh_fmap_delete_subset fresh_lookup_fdom)
  thus ?case by simp
next
case (Variable y x S \<Gamma> \<Delta>)
  from `y \<notin> set (x # S)`
  have [simp]: "y \<noteq> x" and [simp]: "y \<notin> set S" by simp_all

  from stack_head_there[OF Variable.hyps(3)]
  have [simp]: "y \<in> fdom \<Gamma>" by simp
  from stack_bound[OF Variable.hyps(3)]
  have "y \<in> fdom \<Delta>" by simp

  have [simp]: "(\<Delta> f|` (- insert y (insert x (set S))))(y f\<mapsto> \<Delta> f! y) = \<Delta> f|` (- insert x (set S))"
    apply (rule fmap_eqI)
    apply simp
    apply (rule subset_antisym)
    apply rule
    apply (case_tac "xa = x") (* auto does something wrong here *)
    using `y \<in> fdom \<Delta>` Variable(1)
    apply auto
    done
  
  have [simp]: "\<Gamma> f|` (- insert y (insert x (set S))) = fmap_delete y (\<Gamma> f|` (- insert x (set S)))"
    by auto

  from `distinct (x # S)` have [simp]: "x \<notin> set S" "distinct S" by simp_all

  thm Variable.hyps(4)
  let ?S' = "convert_stack \<Gamma> S"

  have "distinct (y # x # S)" by simp
  from Variable.hyps(4)[OF this] Variable.prems(2)
  have hyp: "fmap_delete y (\<Gamma> f|` (- insert x (set S))) : \<Gamma> f! y \<Down>\<^bsub>y#?S'\<^esub> \<Delta> f|` (- insert y (insert x (set S))) : \<Delta> f! y"
    by auto
   
  have "\<Gamma> f|` (- insert x (set S)) : Var y \<Down>\<^bsub>?S'\<^esub> \<Delta> f|` (- insert x (set S)) : \<Delta> f! y"
    apply (rule LaunchburyCombined.reds.Variable[OF _ hyp, simplified])
    using Variable(1) `y \<in> fdom \<Gamma>`
    apply auto
    by (metis `y \<in> fdom \<Gamma>` fdomIff option.exhaust the.simps)
  thus ?case by simp
next
case (Let as \<Gamma> x S body u \<Delta>)
  note `x \<notin> fdom \<Gamma>`[simp]

  from `distinct (x # S)` have [simp]: "x \<notin> set S" "distinct S" by simp_all


  from Let(2)
  have [simp]: "x \<notin> fdom (fmap_of (asToHeap as))" 
    unfolding fdom_fmap_of_conv_heapVars set_bn_to_atom_heapVars fresh_star_def
    by auto

  have disj[simp]: "fdom (fmap_of (asToHeap as)) \<inter> set S = {}"
    by (metis fresh_star_list_distinct set_bn_to_atom_fdom Let.hyps(3) inf_commute)

  have [simp]: "(\<Gamma>(x f\<mapsto> body) f++ fmap_of (asToHeap as)) f|` (- insert x (set S))
   = (\<Gamma>(x f\<mapsto> body) f|` (- insert x (set S)))  f++ fmap_of (asToHeap as)"
   apply (auto simp add: fmap_restr_add intro: )
   apply (rule arg_cong[OF fmap_restr_useless])
   by (metis (full_types) Int_commute Int_insert_left LaunchburyCombinedTaggedMap.fdom_fmap_of_conv_heapVars `x \<notin> fdom (fmap_of (asToHeap as))` disj disjoint_eq_subset_Compl)

  let ?S' = "convert_stack \<Gamma> S"

  from  Let.hyps(6)[OF Let.prems(1)] Let.prems(2)
  have hyp: "(\<Gamma> f|` (- insert x (set S)))  f++ fmap_of (asToHeap as) : body \<Down>\<^bsub>?S'\<^esub> \<Delta> f|` (- insert x (set S)) : \<Delta> f! x"
    by auto

  have "\<Gamma> f|` (- insert x (set S)) : Terms.Let as body \<Down>\<^bsub>?S'\<^esub> \<Delta> f|` (- insert x (set S)) : \<Delta> f! x"
    apply (rule LaunchburyCombined.reds.Let[OF _  hyp])
    using Let(1)
    apply (auto simp add: fresh_star_Pair)
    apply (auto simp add: fresh_star_def fresh_fmap_restr_subset) [1]
    using Let(1,2,3) 
    apply (auto simp add: fresh_star_def fresh_convert_stack_subset)
    done
  thus ?case by simp
qed

lemma forget_stack_nice:
  assumes "\<Gamma> : (x, e) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Delta>'"
  and "supp L \<subseteq> supp \<Gamma>'"
  shows "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
using forget_stack[OF assms(1)] assms(2) by auto

subsubsection {* Original evaluation implies stacked evaluation. *}

lemma add_stack:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "x \<in> set L"
  assumes "supp \<Gamma>' \<subseteq> supp L"
  shows "\<Gamma> : (x,e) # \<Gamma>' \<Down> \<Delta> : (x,z) # \<Gamma>'"
using assms
proof (nominal_induct avoiding: \<Gamma>' x rule: reds_with_n_strong_induct)
case (Lambda \<Gamma> xa e L \<Gamma>')
  show ?case
    by (auto intro: LaunchburyStacked.reds.intros)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z n e' \<Gamma>' x)
  have fresh_n: "atom n \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Gamma>', x, e, xa, \<Theta>, (x, z) # \<Gamma>', y)"
    using Application
    by (simp add: fresh_Pair fresh_Cons fresh_at_base)

  have fresh_y: "atom y \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Gamma>', x, e, xa, \<Theta>, (x, z) # \<Gamma>')"
    using Application
    by (simp add: fresh_Pair fresh_Cons)

  have "supp ((x, App (Var n) xa) # \<Gamma>') \<subseteq> supp (n # xa # L)"
     using set_mp[OF supp_set_mem[OF `x \<in> set L`]] set_mp[OF `supp \<Gamma>' \<subseteq> supp L`]
     by (auto simp add: supp_Pair supp_Cons exp_assn.supp)
  hence hyp1: "\<Gamma> : (n, e) # (x, App (Var n) xa) # \<Gamma>' \<Down> \<Delta> : (n, Lam [y]. e') # (x, App (Var n) xa) # \<Gamma>'"
    apply (rule Application(21)[rotated])
    apply simp
    done
 
  have hyp2: "\<Delta> : (x, e'[y::=xa]) # \<Gamma>' \<Down> \<Theta> : (x, z) # \<Gamma>'"
    apply (rule Application(23)[OF Application.prems])
    done

  show ?case
    by (rule LaunchburyStacked.reds.Application[OF fresh_n fresh_y hyp1 hyp2])
next
case (Variable x e \<Gamma> L \<Delta> z \<Gamma>' xa)
  have "supp ((xa, Var x) # \<Gamma>') \<subseteq> supp (x # L)"
     using set_mp[OF supp_set_mem[OF `xa \<in> set L`]] set_mp[OF `supp \<Gamma>' \<subseteq> supp L`]
     by (auto simp add: supp_Pair supp_Cons exp_assn.supp)
  hence hyp: "delete x \<Gamma> : (x, e) # (xa, Var x) # \<Gamma>' \<Down> \<Delta> : (x, z) # (xa, Var x) # \<Gamma>'"
    apply (rule Variable.hyps(3)[rotated])
    apply (simp)
    done
  show ?case
    by (rule LaunchburyStacked.reds.Variable[OF `(x,e) \<in> set _` hyp])
next
case (Let as \<Gamma> L body \<Delta> z \<Gamma>' x)
  from `x \<in> set L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* x"
    by (metis fresh_star_Cons fresh_star_list(1) in_set_conv_decomp)

  from `supp \<Gamma>' \<subseteq> supp L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* \<Gamma>'"
    by (auto simp add: fresh_star_def fresh_def)

  have fresh: "set (bn as) \<sharp>* (\<Gamma>, x, \<Gamma>')"
    using Let(1-3)
    by (simp add: fresh_star_Pair)
 
  have hyp: "asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Gamma>'"
    by (rule Let.hyps(4)[OF Let.prems])

  show ?case
    by (rule LaunchburyStacked.reds.Let[OF fresh hyp])
qed

end
