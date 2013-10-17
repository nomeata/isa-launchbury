theory Adequacy
imports "ResourcedAdequacy" "Denotational-Related"
begin

theorem adequacy:
  assumes "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<noteq> \<bottom>"
  and "distinctVars \<Gamma>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
proof-
  have "\<lbrace>\<Gamma>\<rbrace> f\<triangleleft>\<triangleright> \<N>\<lbrace>\<Gamma>\<rbrace>" by (rule heaps_similar)
  hence  "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity>" by (rule denotational_semantics_similar)
  with assms(1)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>" by (metis bot_or_not_bot)
  thus ?thesis by (rule resourced_adequacy[OF _ assms(2)])
qed

end
