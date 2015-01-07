theory CallArityCorrectEnd2End
imports CardinalityEtaExpand CoCallImplCorrect "~~/src/Tools/Permanent_Interpretation" 
begin

thm CardinalityArityTransformation.foo

print_locales
print_interps CardinalityPrognosisCorrectLet

permanent_interpretation CardinalityArityTransformation prognosis Aexp Aheap cHeap
  defining final_consistent = consistent
  and final_conf_transform = conf_transform
  and final_transform = "AbstractTransform.transform (Rep_cfun inc) (Rep_cfun pred) (\<lambda>\<Delta> e a. (a, Aheap \<Delta> e\<cdot>a)) fst snd (\<lambda>a. Var) (\<lambda>a. Var1) (\<lambda>a. App) (\<lambda>a v e . Lam [v]. e)
  (\<lambda>b \<Gamma>. Terms.Let (map_transform Aeta_expand (snd b) \<Gamma>))"
   by default

lemma end2end:
  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow>
  \<not> boring_step c' \<Longrightarrow>
  consistent (ae, ce, a) c \<Longrightarrow>
  \<exists>ae' ce' a'. consistent  (ae', ce', a') c' \<and> final_conf_transform  (ae, ce, a) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform  (ae', ce', a') c'"
  by (rule foo)

lemma end2end_closed:
  assumes "fv e = ({} :: var set)"
  assumes "([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>,v,[])"
  assumes "isLam v"
  shows "\<exists> \<Gamma>' v'. length \<Gamma>' \<le> length \<Gamma> \<and> isLam v' \<and> ([], final_transform 0 e, []) \<Rightarrow>\<^sub>G\<^sup>* (\<Gamma>',v',[])"
proof-
  note assms(2)
  moreover
  have "\<not> boring_step (\<Gamma>,v,[])" by (simp add: boring_step.simps)
  moreover
  have "consistent (\<bottom>,\<bottom>,0) ([], e, [])" using assms(1)  by (rule closed_consistent)
  ultimately
  obtain ae ce a where
    *: "consistent  (ae, ce, a) (\<Gamma>,v,[])" and
    **: "final_conf_transform  (\<bottom>, \<bottom>, 0) ([],e,[]) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae, ce, a) (\<Gamma>,v,[])"
    by (metis end2end)

  let ?\<Gamma> = "restrictA (edom ce) (map_transform Aeta_expand ae (map_transform final_transform ae \<Gamma>))"
  let ?v = "final_transform a v"

  show ?thesis
  proof(intro exI conjI)
    show "length (restrictA (edom ce) (map_transform Aeta_expand ae (map_transform final_transform ae \<Gamma>))) \<le> length \<Gamma>"
      by (rule order_trans[OF length_restrictA_le]) simp

    have "final_conf_transform  (\<bottom>, \<bottom>, 0) ([],e,[]) = ([],final_transform 0 e,[])" by simp
    with **
    show "([], final_transform 0 e, []) \<Rightarrow>\<^sub>G\<^sup>* (?\<Gamma>, ?v, [])" by simp

    show "isLam (transform a v)" using `isLam v` by simp
  qed
qed  

thm conf_transform.simps
find_theorems final_transform

end
