theory "Launchbury-Unstack"
imports Launchbury LaunchburyStacked
begin

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
  have fresh: "atom z \<sharp> (\<Gamma>, e, y, S, \<Delta>, \<Theta>, snd (hd \<Theta>'))"
    using Application
    by (simp add: fresh_Pair fresh_Cons)[1]

  have "supp (y # S) \<subseteq> supp ( (x, App (Var n) y) # \<Gamma>')"
    using Application.prems(1)
    by (auto simp add: supp_Cons supp_Pair exp_assn.supp)
  hence hyp1: "\<Gamma> : e \<Down>\<^bsub>y # S\<^esub> \<Delta> : Lam [z]. e'" 
    by (rule Application.hyps(23)[simplified])

  have "supp S \<subseteq> supp \<Delta>'"
    using Application.prems(1)
    using stack_unchanged[OF Application.hyps(22)]
    by simp
  hence hyp2: "\<Delta> : e'[z::=y] \<Down>\<^bsub>S\<^esub> \<Theta> : snd (hd \<Theta>')"
    by (rule Application.hyps(25)[simplified])
   
  show ?case
    by (simp, rule Launchbury.Application[OF fresh hyp1 hyp2])
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

  hence fresh: "set (bn as) \<sharp>* (\<Gamma>, S)"
    using Let by (auto simp add: fresh_star_Pair)

  show ?case
    by (simp, rule Launchbury.Let[OF fresh Let.hyps(5) hyp])
qed

end
