theory "HOLCF-Meet-Classes"
imports "HOLCF-Meet" "HOLCF-Join"
begin

subsubsection {* Type classes for various kinds of meets *}

text {* Meets for finite nonempty sets with a lower bound. *}

class Bounded_Nonempty_Meet_cpo = cpo +
  assumes bounded_nonempty_meet_exists: "S \<noteq> {} \<Longrightarrow> (\<exists>z. S >| z) \<Longrightarrow> \<exists>x. S >>| x"
begin
  lemma nonempty_ub_implies_lub_exists:
  assumes "S <| u"
  assumes "S \<noteq> {}"
  shows "\<exists> z. S <<| z"
  proof-
    have "{u. S <| u} \<noteq> {}" using assms(1) by auto
    hence "\<exists>x. {u. S <| u} >>| x"
      apply (rule bounded_nonempty_meet_exists)
      by (metis CollectE assms(2) equals0I is_lbI is_ub_def)
    then obtain lu where lb: "{u. S <| u} >>| lu" by auto
    hence "S <| lu"
      by (metis is_glb_above_iff is_lb_def is_ub_def mem_Collect_eq)
    hence "S <<| lu"
      by (metis (full_types) is_lubI is_glbD1 is_lb_def lb mem_Collect_eq)
    thus ?thesis ..
  qed

  lemma ub_implies_compatible:
    "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> compatible x y"
    unfolding compatible_def
    by (rule nonempty_ub_implies_lub_exists, auto)
end

text {* Meets for finite nonempty sets. *}

class Nonempty_Meet_cpo = cpo +
  assumes nonempty_meet_exists: "S \<noteq> {} \<Longrightarrow> \<exists>x. S >>| x"
begin
  lemma ub_implies_lub_exists:
  assumes "S <| u"
  shows "\<exists> z. S <<| z"
  proof-
    have "{u. S <| u} \<noteq> {}" using assms by auto
    from nonempty_meet_exists[OF this]
    obtain lu where lb: "{u. S <| u} >>| lu" by auto
    hence "S <| lu"
      by (metis is_glb_above_iff is_lb_def is_ub_def mem_Collect_eq)
    hence "S <<| lu"
      by (metis (full_types) is_lubI is_glbD1 is_lb_def lb mem_Collect_eq)
    thus ?thesis ..
  qed
end

context Nonempty_Meet_cpo
begin
  subclass Bounded_Nonempty_Meet_cpo
  apply default by (metis nonempty_meet_exists)
end

lemma (in Bounded_Nonempty_Meet_cpo) compatible_down_closed:
    assumes "compatible x y"
    and "z \<sqsubseteq> x"
    shows "compatible z y"
proof-
    from assms(1) obtain ub where "{x, y} <<| ub" by (metis compatible_def)
    hence "{x,y} <| ub" by (metis is_lubD1)
    hence "{z,y} <| ub" using assms(2) by (metis is_ub_insert rev_below_trans)
    thus ?thesis unfolding compatible_def by (metis insert_not_empty nonempty_ub_implies_lub_exists)
qed

lemma (in Bounded_Nonempty_Meet_cpo) compatible_down_closed2:
    assumes "compatible y x"
    and "z \<sqsubseteq> x"
    shows "compatible y z"
proof-
    from assms(1) obtain ub where "{y, x} <<| ub" by (metis compatible_def)
    hence "{y,x} <| ub" by (metis is_lubD1)
    hence "{y,z} <| ub" using assms(2) by (metis is_ub_insert rev_below_trans)
    thus ?thesis unfolding compatible_def by (metis insert_not_empty nonempty_ub_implies_lub_exists)
qed

lemma join_mono':
  assumes  "compatible (c::'a::Bounded_Nonempty_Meet_cpo) d"
  and "a \<sqsubseteq> c"
  and "b \<sqsubseteq> d"
  shows "a \<squnion> b \<sqsubseteq> c \<squnion> d"
  apply (rule join_mono[OF _ assms(1) assms(2) assms(3)])
  by (metis assms(1) assms(2) assms(3) compatible_down_closed2 compatible_sym)

subsubsection {* Bifinite domains with finite nonempty meets have arbitrary nonempty meets. *}

class Finite_Meet_bifinite_cpo = Finite_Meet_cpo + bifinite

lemma is_ub_range:
     "S >| u \<Longrightarrow> Rep_cfun f ` S >| f \<cdot> u"
  apply (rule is_lbI)
  apply (erule imageE)
  by (metis monofun_cfun_arg is_lbD)

lemma (in approx_chain) lub_approx_arg: "(\<Squnion>i. approx i \<cdot> u ) = u"
  by (metis chain_approx lub_ID_reach lub_approx)

instance Finite_Meet_bifinite_cpo \<subseteq> Nonempty_Meet_cpo
proof (default)
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" by auto
  fix S
  assume "(S :: 'a set) \<noteq> {}"
  have "\<And>i. \<exists> l . Rep_cfun (approx i) ` S >>|l"
    apply (rule finite_meet_exists)
    using `S \<noteq> {}` apply auto[1]
    using  finite_deflation.finite_range[OF approx_chain.finite_deflation_approx[OF `approx_chain approx`]]
    by (metis (full_types) image_mono rev_finite_subset top_greatest)
  then obtain Y where Y_is_glb: "\<And>i. Rep_cfun (approx i) ` S >>| Y i" by metis
  
  have "chain Y"
    apply (rule chainI)
    apply (subst is_glb_above_iff[OF Y_is_glb])
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule rev_below_trans[OF monofun_cfun_fun[OF chainE[OF approx_chain.chain_approx[OF `approx_chain approx`]]]])
    apply (rule is_lbD[OF is_glbD1[OF Y_is_glb]])
    apply (erule imageI)
    done
  
  have "S >| Lub Y"
  proof(rule is_lbI, rule lub_below[OF `chain Y`])
    fix x i
    assume "x \<in> S"
    hence "Y i \<sqsubseteq> approx i \<cdot> x"
      by (rule imageI[THEN is_lbD[OF is_glbD1[OF Y_is_glb]]])
    also have "approx i \<cdot> x \<sqsubseteq> x"
      by (rule  approx_chain.approx_below[OF `approx_chain approx`])
    finally
    show "Y i \<sqsubseteq> x".
  qed

  have "S >>| Lub Y"
  proof (rule is_glbI[OF `S >| Lub Y`])
    fix u
    assume "S >| u"
    hence "\<And> i. Rep_cfun (approx i) ` S >| approx i \<cdot> u"
      by (rule is_ub_range)
    hence "\<And> i.  approx i \<cdot> u \<sqsubseteq> Y i"
      by (rule is_glbD2[OF Y_is_glb])
    hence "(\<Squnion>i. approx i \<cdot> u ) \<sqsubseteq> Lub Y" 
      by (rule lub_mono[OF
            ch2ch_Rep_cfunL[OF approx_chain.chain_approx[OF `approx_chain approx`]]
            `chain Y`
            ])
    thus "u \<sqsubseteq> Lub Y" 
      by (metis approx_chain.lub_approx_arg[OF `approx_chain approx`])
  qed
  thus "\<exists>x. S >>| x"..
qed

instantiation cfun :: (cpo,"{bifinite,cont_binary_meet}") Finite_Meet_cpo begin
  fixrec cfun_meet :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
    where "cfun_meet\<cdot>f\<cdot>g\<cdot>x = (f\<cdot>x) \<sqinter> (g\<cdot>x)"
  
  lemma[simp]: "cfun_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "cfun_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp)+

  instance
  apply default
  proof(intro exI conjI strip)
    fix x y
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> x" by (auto simp add: cfun_below_iff)
    show "cfun_meet\<cdot>x\<cdot>y \<sqsubseteq> y" by (auto simp add: cfun_below_iff)
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> cfun_meet\<cdot>x\<cdot>y" by (auto simp add: cfun_below_iff meet_above_iff)
  qed
end



end
