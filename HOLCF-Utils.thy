theory "HOLCF-Utils"
  imports HOLCF
begin



lemma lub_eq_range_is_lub:
  "(\<And> i. F (Y i) \<sqsubseteq> F (Y (Suc i))) \<Longrightarrow> F (\<Squnion> i. Y i) = (\<Squnion> i. F (Y i)) \<Longrightarrow> range (\<lambda>i. F (Y i)::'b::cpo) <<| F (\<Squnion> i. Y i)"
  apply (erule ssubst)
  apply (rule cpo_lubI)
  apply (erule chainI)
  done

lemma range_is_lubI2:
  assumes "(\<And> i. F (Y i) \<sqsubseteq> F (Y (Suc i)))"
  assumes "(\<And> i. F (Y i) \<sqsubseteq> F (\<Squnion>i . Y i))"
  assumes "F (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. F (Y i))"
  shows "range (\<lambda>i. F (Y i)::'b::cpo) <<| F (\<Squnion> i. Y i)"
proof-
  have "chain (\<lambda>i. F (Y i))" using assms(1) by (rule chainI)
  have "(\<Squnion> i. F (Y i)) \<sqsubseteq> F (\<Squnion> i. Y i)" by (rule lub_below[OF `chain _` assms(2)])
  hence "F (\<Squnion> i. Y i) = (\<Squnion> i. F (Y i))" using assms(3) by (rule below_antisym[rotated])
  thus ?thesis
    apply (rule ssubst)
    apply (rule cpo_lubI[OF `chain _`])
    done
qed

end
