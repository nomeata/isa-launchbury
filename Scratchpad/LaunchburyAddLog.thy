theory LaunchburyAddLog
imports Launchbury LaunchburyLog
begin

lemma add_log: "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow> (\<exists> c. \<Gamma> : e \<Down>\<^bsub>n,L\<^esub> \<Delta> : v c)"
proof(induction arbitrary: n rule:Launchbury.reds.induct)
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' n)
  hence "atom y \<sharp> x" by (simp add: fresh_Pair) 
  with Application.IH LaunchburyLog.reds_ApplicationI
  show ?case by blast
qed  (blast intro: LaunchburyLog.reds.intros)+

lemma remove_log: "\<Gamma> : e \<Down>\<^bsub>n,L\<^esub> \<Delta> : v c \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v"
proof(induction rule:LaunchburyLog.reds.induct)
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' n)
  hence "atom y \<sharp> x" by (simp add: fresh_Pair) 
  with Application.IH Launchbury.reds_ApplicationI
  show ?case by blast
qed (blast intro: Launchbury.reds.intros)+

end
