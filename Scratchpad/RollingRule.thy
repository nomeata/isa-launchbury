theory RollingRule imports HOLCF
begin

(* http://afp.sourceforge.net/browser_info/current/AFP/WorkerWrapper/FixedPointTheorems.html *)
lemma rolling_rule_ltr: "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
proof -
  have "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by (rule below_refl) -- {* reflexivity *}
  hence "g\<cdot>((f oo g)\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_eq[where F="f oo g"] by simp -- {* computation *}
  hence "(g oo f)\<cdot>(g\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by simp -- {* re-associate @{term "op oo"} *}
  thus "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_least_below by blast -- {* induction *}
qed

lemma rolling_rule_rtl: "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
proof -
  have "fix\<cdot>(f oo g) \<sqsubseteq> f\<cdot>(fix\<cdot>(g oo f))" by (rule rolling_rule_ltr)
  hence "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(f\<cdot>(fix\<cdot>(g oo f)))"
    by (rule monofun_cfun_arg) -- {* g is monotonic *}
  thus "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
    using fix_eq[where F="g oo f"] by simp -- {* computation *}
qed

lemma rolling_rule: "fix\<cdot>(g oo f) = g\<cdot>(fix\<cdot>(f oo g))"
  by (rule below_antisym[OF rolling_rule_ltr rolling_rule_rtl])

lemma rolling_rule2:
  assumes "cont F" and "cont G"
  shows "fix\<cdot>(\<Lambda> x. G (F x)) = G (fix\<cdot>(\<Lambda> x. F (G x)))"
  using cont_compose[OF assms(1), cont2cont] cont_compose[OF assms(2), cont2cont]
  using rolling_rule[where g = "\<Lambda> x. G x" and f = "\<Lambda> x. F x"]
  by (auto simp add: oo_def)

end
