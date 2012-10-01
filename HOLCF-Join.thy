theory "HOLCF-Join"
imports 
  "Down"
begin

subsection {* Lower bounds *}

context po
begin
definition is_lb :: "'a set => 'a => bool" (infix ">|" 55) where
  "S >| x <-> (\<forall>y\<in>S. x \<sqsubseteq> y)"

lemma is_lbI: "(!!x. x \<in> S ==> l \<sqsubseteq> x) ==> S >| l"
  by (simp add: is_lb_def)

lemma is_lbD: "[|S >| l; x \<in> S|] ==> l \<sqsubseteq> x"
  by (simp add: is_lb_def)

lemma is_lb_empty [simp]: "{} >| l"
  unfolding is_lb_def by fast

lemma is_lb_insert [simp]: "(insert x A) >| y = (y \<sqsubseteq> x \<and> A >| y)"
  unfolding is_lb_def by fast

lemma is_lb_downward: "[|S >| l; y \<sqsubseteq> l|] ==> S >| y"
  unfolding is_lb_def by (fast intro: below_trans)

subsection {* Greatest lower bounds *}

definition is_glb :: "'a set => 'a => bool" (infix ">>|" 55) where
  "S >>| x <-> S >| x \<and> (\<forall>u. S >| u --> u \<sqsubseteq> x)"

definition glb :: "'a set => 'a" ("\<Sqinter>_" [60]60) where
  "glb S = (THE x. S >>| x)" 

text {* access to some definition as inference rule *}

lemma is_glbD1: "S >>| x ==> S >| x"
  unfolding is_glb_def by fast

lemma is_glbD2: "[|S >>| x; S >| u|] ==> u \<sqsubseteq> x"
  unfolding is_glb_def by fast

lemma (in po) is_glbI: "[|S >| x; !!u. S >| u ==> u \<sqsubseteq> x|] ==> S >>| x"
  unfolding is_glb_def by fast

lemma is_glb_above_iff: "S >>| x ==> u \<sqsubseteq> x <-> S >| u"
  unfolding is_glb_def is_lb_def by (metis below_trans)

text {* glbs are unique *}

lemma is_glb_unique: "[|S >>| x; S >>| y|] ==> x = y"
  unfolding is_glb_def is_lb_def by (blast intro: below_antisym)


text {* technical lemmas about @{term glb} and @{term is_glb} *}

lemma is_glb_glb: "M >>| x ==> M >>| glb M"
  unfolding glb_def by (rule theI [OF _ is_glb_unique])

lemma glb_eqI: "M >>| l ==> glb M = l"
  by (rule is_glb_unique [OF is_glb_glb])

lemma is_glb_singleton: "{x} >>| x"
  by (simp add: is_glb_def)

lemma glb_singleton [simp]: "glb {x} = x"
  by (rule is_glb_singleton [THEN glb_eqI])

lemma is_glb_bin: "x \<sqsubseteq> y ==> {x, y} >>| x"
  by (simp add: is_glb_def)

lemma glb_bin: "x \<sqsubseteq> y ==> glb {x, y} = x"
  by (rule is_glb_bin [THEN glb_eqI])

lemma is_glb_maximal: "[|S >| x; x \<in> S|] ==> S >>| x"
  by (erule is_glbI, erule (1) is_lbD)

lemma glb_maximal: "[|S >| x; x \<in> S|] ==> glb S = x"
  by (rule is_glb_maximal [THEN glb_eqI])

end

lemma (in Top_cpo) meet_empty[simp]: "\<Sqinter>{} = (\<top>::'a)"
    by (metis glb_eqI is_glbI is_lb_empty maximal)

lemma (in cpo) Meet_insert: "S >>| l \<Longrightarrow> {x, l} >>| l2 \<Longrightarrow> insert x S >>| l2"
  apply (rule is_glbI)
  apply (metis is_glb_above_iff is_glb_def is_lb_insert)
  by (metis is_glb_above_iff is_glb_def is_glb_singleton is_lb_insert)

class Finite_Meet_cpo = cpo +
  assumes binary_meet_exists: "\<exists> l. l \<sqsubseteq> x \<and> l \<sqsubseteq> y \<and> (\<forall> z. (z \<sqsubseteq> x \<and> z \<sqsubseteq> y) \<longrightarrow> z \<sqsubseteq> l)"
begin

  lemma binary_meet_exists': "\<exists>l. {x, y} >>| l"
    using binary_meet_exists[of x y]
    unfolding is_glb_def is_lb_def
    by auto

  lemma finite_meet_exists:
    assumes "S \<noteq> {}"
    and "finite S"
    shows "\<exists>x. S >>| x"
  using `S \<noteq> {}`
  apply (induct rule: finite_induct[OF `finite S`])
  apply (erule notE, rule refl)[1]
  apply (case_tac "F = {}")
  apply (metis is_glb_singleton)
  apply (metis Meet_insert binary_meet_exists')
  done
end

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

class Meet_cpo = Top_cpo + Nonempty_Meet_cpo
begin
  lemma  meet_exists: "\<exists>x. S >>| (x::'a)"
  using [[show_types]] [[show_sorts]]
   apply (cases "S = {}")
   thm nonempty_meet_exists maximal top_def
   apply (rule_tac x = "\<top>" in exI)
   apply (rule is_glbI)
   apply (rule is_lbI)
   apply auto[1]
   apply (rule maximal)
   apply (metis nonempty_meet_exists)
   done

  text {* Properties of the glb *}  

  lemma glbI: "S >>| (\<Sqinter>S :: 'a)"
    by (metis meet_exists is_glb_glb)

  lemma thelubE: "\<lbrakk>(\<Sqinter>S) = l\<rbrakk> \<Longrightarrow> S  >>| (l::'a)"
    by (metis meet_exists is_glb_glb)

  lemma is_lb_theglb: "x \<in> S \<Longrightarrow> \<Sqinter> S \<sqsubseteq> x"
    by (metis meet_exists is_lbD is_glb_glb[THEN is_glbD1])
  
  lemma is_glb_theglb:
    "[|S >| x|] ==> x \<sqsubseteq> (\<Sqinter>S)"
    by (metis meet_exists is_glb_glb[THEN is_glbD2])
  
  lemma glb_above_iff: "x \<sqsubseteq> (\<Sqinter>S) <-> (\<forall>y \<in> S. x \<sqsubseteq> y)"
    by (simp add: is_glb_above_iff [OF glbI] is_lb_def)
  
  lemma glb_above: "[| \<And>y. y \<in> S \<Longrightarrow> x \<sqsubseteq> y|] ==> x \<sqsubseteq> (\<Sqinter>S)"
    by (simp add: glb_above_iff)
  
  lemma above_glb: "[|y \<in> S ; y \<sqsubseteq> x|] ==> (\<Sqinter>S) \<sqsubseteq> y"
    by (metis is_lb_theglb)

end 

(* More about Joins aka least upper bounds *)

context po
begin
definition join :: "'a  => 'a => 'a " (infixl "\<squnion>" 65)
  where "x \<squnion> y = lub {x,y}"

lemma join_commute: "x \<squnion> y = y \<squnion> x"
  unfolding join_def
  by (metis insert_commute)

lemma join_compareable2:  "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  unfolding join_def
  by (metis lub_bin)

lemma join_compareable1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  apply (subst join_commute)
  by (rule join_compareable2)
end

lemma (in pcpo) join_empty: "lub {} = (\<bottom>::'a)"
  by (metis (full_types) is_lub_def is_ub_empty lub_eqI minimal)

class Join_cpo = cpo +
  assumes join_exists: "\<exists>x. S <<| x"
begin
  lemma lub_belowI: "\<lbrakk>\<And> x. x \<in> S \<Longrightarrow> x \<sqsubseteq> z \<rbrakk> \<Longrightarrow> lub S  \<sqsubseteq> z"
    by (metis is_lubD2 is_ubI join_exists lub_eqI)

  lemma join_belowI: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
    unfolding join_def
    by (auto intro: lub_belowI)
  
  lemma join_above1: "x \<sqsubseteq> x \<squnion> y"
    unfolding join_def
    by (metis is_lubD1 is_ub_insert join_exists lub_eqI)
  
  lemma join_above2: "y \<sqsubseteq> x \<squnion> y"
    unfolding join_def
    by (metis is_lubD1 is_ub_insert join_exists lub_eqI)

end

instance Join_cpo \<subseteq> pcpo
  apply default
  apply (rule_tac x = "lub {}" in exI)
  by (metis is_lub_thelub_ex is_ub_empty join_exists)


(* Complete cpos; Meet is sufficient *)

class complete_cpo = Meet_cpo + Join_cpo

instance Meet_cpo \<subseteq> Join_cpo
  apply default
  apply (metis is_lubI is_ubI glb_above is_ubD is_lb_theglb mem_Collect_eq)
  done


(* Stuff for the down type *)

lemma down_set_cases:
  fixes S  :: "'a d set"
  obtains Stop and  Sbelow
  where "Stop \<subseteq> {Itop}" and "Stop \<union> Idown ` Sbelow = S"
proof-
  have "S \<inter> {Itop} \<subseteq> {Itop}" by auto
  moreover
  have "Idown ` ((\<lambda>x. THE z. x = Idown z) ` (S - {Itop})) = S - {Itop}" 
    apply (intro set_eqI)
    apply (case_tac x rule:d.exhaust)
    apply auto[1]

    apply rule

    apply (erule imageE)
    apply auto[1]
    apply (rule classical)
    apply (erule notE)
    apply (rule the1I2)
    apply auto[1]
    apply (metis d.exhaust)
    apply simp

    apply (simp only:)
    apply (rule imageI)
    apply (erule rev_image_eqI)
    apply (rule the1I2)
    apply auto
    done
  hence "(S \<inter> {Itop}) \<union> Idown ` ((\<lambda>x. THE z. x = Idown z) ` (S - {Itop})) = S" by auto
  ultimately
  show thesis ..
qed

instance d :: (Nonempty_Meet_cpo) Nonempty_Meet_cpo
proof(default)
  fix S :: "'a d set"
  assume "S \<noteq> {}"
  
  obtain S1 S2 where "S1 \<subseteq> {Itop}" and "S1 \<union> Idown ` S2 = S" by (rule down_set_cases)
  
  show "\<exists> x. S >>| x"
  proof (cases "S2 = {}")
  case True
    hence "S = S1" using `_ \<union> _ = _` by (metis Un_empty_right image_empty)
    hence "S = {Itop}" using  `S \<noteq> {}` `S1 \<subseteq> _` by (metis subset_singletonD)
    hence "S >>| Itop"
      by (metis is_glb_singleton)
    thus ?thesis..
  next
  case False
    then obtain u where "S2 >>| u" by (metis nonempty_meet_exists)
  
    from `S2 \<noteq> {}` obtain a where "Idown a \<in> S"  using `_ \<union> _ = _` by auto
  
    have lb: "S >| Idown u"
      using `_ \<union> _ = _` `S1 \<subseteq> _` is_lbD[OF is_glbD1[OF `S2 >>| u`]]
      by (auto intro: is_lbI)
  
    have "S >>| Idown u"
      apply(rule is_glbI[OF lb])
      apply (case_tac ua rule:d.exhaust)  
      apply (drule is_lbD[OF _ `Idown a \<in> S`])
      apply simp
      apply simp
      apply (rule is_glbD2[OF `S2 >>| u`])
      apply (rule is_lbI)
      apply (drule is_lbD)
      using  `_ \<union> _ = _`
      apply auto
      done
    thus ?thesis ..
  qed
qed

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

end
