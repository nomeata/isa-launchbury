theory "Launchbury-Unstack"
imports Launchbury LaunchburyStacked
begin

lemma supp_set_mem: "x \<in> set L \<Longrightarrow> supp x \<subseteq> supp L"
  by (induct L, auto simp add: supp_Cons)

lemma forget_stack:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "supp S \<subseteq> supp (tl \<Gamma>')"
  shows "\<Gamma> : snd (hd \<Gamma>') \<Down>\<^bsub>S\<^esub> \<Delta> : snd (hd \<Delta>')"
using assms
proof (nominal_induct avoiding: S rule: reds.strong_induct)
case (Lambda \<Gamma> x y e \<Gamma>')
  show ?case
    by (auto intro: Launchbury.reds.intros)
next
case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z  e' S)
  have "atom z \<sharp> \<Gamma>'" using Application by (simp add: fresh_Pair)
  hence "atom z \<sharp> map fst \<Gamma>'"
    by (induct \<Gamma>')(auto simp add: fresh_Cons fresh_Nil)
  moreover
  have  "atom z \<sharp> snd (hd \<Theta>')"
    using Application stack_not_empty[OF Application(24)]
    by (cases \<Theta>', auto simp add: fresh_Cons fresh_Pair)
  ultimately
  have fresh: "atom z \<sharp> (\<Gamma>, e, y, S, \<Delta>, \<Theta>, snd (hd \<Theta>'), n)"
    using Application
    by (simp add: fresh_Pair fresh_Cons fresh_at_base)[1]

  have "atom n \<sharp> \<Gamma>'" using Application by (simp add: fresh_Pair)
  hence "atom n \<sharp> map fst \<Gamma>'"
    by (induct \<Gamma>')(auto simp add: fresh_Cons fresh_Nil)
  moreover
  have  "atom n \<sharp> snd (hd \<Theta>')"
    using Application stack_not_empty[OF Application(24)]
    by (cases \<Theta>', auto simp add: fresh_Cons fresh_Pair)
  ultimately
  have fresh2: "atom n \<sharp> (\<Gamma>, e, y, S, \<Delta>, \<Theta>, snd (hd \<Theta>'))"
    using Application
    by (simp add: fresh_Pair fresh_Cons fresh_at_base)[1]
 

  have "supp (n # y # S) \<subseteq> supp ( (x, App (Var n) y) # \<Gamma>')"
    using Application.prems(1)
    by (auto simp add: supp_Cons supp_Pair exp_assn.supp)
  hence hyp1: "\<Gamma> : e \<Down>\<^bsub>n # y # S\<^esub> \<Delta> : Lam [z]. e'" 
    by (rule Application.hyps(23)[simplified])
  have "supp S \<subseteq> supp \<Delta>'"
    using Application.prems(1)
    using stack_unchanged[OF Application.hyps(22)]
    by simp
  hence hyp2: "\<Delta> : e'[z::=y] \<Down>\<^bsub>S\<^esub> \<Theta> : snd (hd \<Theta>')"
    by (rule Application.hyps(25)[simplified])
   
  show ?case
    by (simp, rule Launchbury.Application[OF fresh fresh2 hyp1 hyp2])
next
case (Variable y e \<Gamma> x \<Gamma>' \<Delta> z \<Delta>' S)
  have "supp (y # S) \<subseteq> supp ((x, Var y) # \<Gamma>')"
    using Variable.prems(1)
    by (auto simp add: supp_Cons supp_Pair exp_assn.supp)
  hence hyp: "removeAll (y, e) \<Gamma> : e \<Down>\<^bsub>y # S\<^esub> \<Delta> : z"
    by (rule Variable.hyps(3)[simplified])
  show ?case
    by (simp, rule Launchbury.Variable[OF `_ \<in> set _` hyp])   
next
case (Let as \<Gamma> x body \<Gamma>' \<Delta> \<Delta>' S)
  have "supp S \<subseteq> supp \<Gamma>'"
    using Let.prems[simplified].
  hence hyp: "asToHeap as @ \<Gamma> : body \<Down>\<^bsub>S\<^esub> \<Delta> : snd (hd \<Delta>')"
    by (rule Let.hyps(7)[simplified])

  have "set (bn as) \<sharp>* S"
    using Let(4) using `supp S \<subseteq> supp \<Gamma>'`
    by (auto simp add: fresh_star_def fresh_def)

  hence fresh: "set (bn as) \<sharp>* (\<Gamma>, Terms.Let as body, S)"
    using Let by (auto simp add: fresh_star_Pair)

  show ?case
    by (simp, rule Launchbury.Let[OF fresh Let.hyps(5) hyp])
qed

lemma add_stack:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "x \<in> set L"
  assumes "supp \<Gamma>' \<subseteq> supp L"
  shows "\<Gamma> : (x,e) # \<Gamma>' \<Down> \<Delta> : (x,z) # \<Gamma>'"
using assms
proof (nominal_induct avoiding: \<Gamma>' x rule: Launchbury.reds.strong_induct)
case (Lambda \<Gamma> xa e L \<Gamma>')
  show ?case
    by (auto intro: reds.intros)
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
    by (rule reds.Application[OF fresh_n fresh_y hyp1 hyp2])
next
case (Variable x e \<Gamma> L \<Delta> z \<Gamma>' xa)
  have "supp ((xa, Var x) # \<Gamma>') \<subseteq> supp (x # L)"
     using set_mp[OF supp_set_mem[OF `xa \<in> set L`]] set_mp[OF `supp \<Gamma>' \<subseteq> supp L`]
     by (auto simp add: supp_Pair supp_Cons exp_assn.supp)
  hence hyp: "removeAll (x, e) \<Gamma> : (x, e) # (xa, Var x) # \<Gamma>' \<Down> \<Delta> : (x, z) # (xa, Var x) # \<Gamma>'"
    apply (rule Variable.hyps(3)[rotated])
    apply (simp)
    done
  show ?case
    by (rule reds.Variable[OF `(x,e) \<in> set _` hyp])
next
case (Let as \<Gamma> body L \<Delta> z \<Gamma>' x)
  from `x \<in> set L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* x"
    by (metis fresh_star_Cons fresh_star_list(1) in_set_conv_decomp)

  from `supp \<Gamma>' \<subseteq> supp L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* \<Gamma>'"
    by (auto simp add: fresh_star_def fresh_def)

  have fresh: "set (bn as) \<sharp>* (\<Gamma>, x, Terms.Let as body, \<Gamma>')"
    using Let(1-3)
    by (simp add: fresh_star_Pair)
 
  have hyp: "asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Gamma>'"
    apply (rule Let.hyps(6)[OF Let.prems])
    done

  show ?case
    by (rule reds.Let[OF fresh `distinctVars (asToHeap as)` hyp])
qed


end