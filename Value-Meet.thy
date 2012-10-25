theory "Value-Meet"
  imports "HOLCF-Join"  "Denotational-Common"
begin


fixrec value_meet :: "Value \<rightarrow> Value \<rightarrow> Value"
  where "value_meet\<cdot>(Fn\<cdot>f)\<cdot>(Fn\<cdot>g) = Fn\<cdot>(\<Lambda> x. value_meet\<cdot>(f\<cdot>x)\<cdot>(g\<cdot>x))"

lemma[simp]: "value_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "value_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)

instance Value :: Finite_Meet_cpo
apply default
proof(rule exI, intro conjI strip)
  fix x y
  {
    fix t
    have "(t \<sqsubseteq> value_meet\<cdot>x\<cdot>y) = (t \<sqsubseteq> x \<and> t \<sqsubseteq> y)"
    proof (induct t rule:Value.take_induct)
      fix n
      show "(Value_take n\<cdot>t \<sqsubseteq> value_meet\<cdot>x\<cdot>y) = (Value_take n\<cdot>t \<sqsubseteq> x \<and> Value_take n\<cdot>t \<sqsubseteq> y)"
      proof (induct n arbitrary: t x y rule:nat_induct)
        case 0 thus ?case by auto
        next
        case (Suc n t x y) thus ?case
          apply -
          apply (cases t, simp)
          apply (cases x, simp)
          apply (cases y, simp)
          apply (fastforce simp add: cfun_below_iff)
          done
      qed
   qed auto
  } note * = this
  show "value_meet\<cdot>x\<cdot>y \<sqsubseteq> x" using * by auto
  show "value_meet\<cdot>x\<cdot>y \<sqsubseteq> y" using * by auto
  fix z
  assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
  thus "z \<sqsubseteq> value_meet\<cdot>x\<cdot>y" using * by auto
qed

instance Value :: Finite_Meet_bifinite_cpo by default

instance fmap :: (type, Nonempty_Meet_cpo) Bounded_Nonempty_Meet_cpo
apply default
proof-
  fix S :: "('a, 'b) fmap set"
  assume "S \<noteq> {}" and "\<exists>z. S >| z"
  then obtain b where "\<And> m. m\<in>S \<Longrightarrow> b \<sqsubseteq> m" by (metis is_lbD)
  hence [simp]:"\<And> m. m \<in> S \<Longrightarrow> fdom m = fdom b" by (metis fmap_below_dom)
  
  obtain f where f: "\<And> x. x \<in> fdom b \<Longrightarrow> (\<lambda>m . the (lookup m x)) ` S >>| f x "
  proof-
    {
    fix x
    assume "x \<in> fdom b"
    have "(\<lambda>m . the (lookup m x)) ` S \<noteq> {}" using `S \<noteq> {}` by auto
    then obtain l where  "(\<lambda>m . the (lookup m x)) ` S >>| l" by (metis nonempty_meet_exists)
    hence "(\<lambda>m . the (lookup m x)) ` S >>| (SOME l. (\<lambda>m . the (lookup m x)) ` S >>| l)"
      by (rule someI)
    }
    thus ?thesis by (rule that)
  qed 

  let ?zm = "\<lambda> x. if x \<in> fdom b then Some (f x) else None"
  have "dom ?zm = fdom b" by (auto simp add: dom_def)

  obtain z where [simp]: "fdom z = fdom b" and z: "\<And> x m . x \<in> fdom b \<Longrightarrow> (\<lambda>m . the (lookup m x)) ` S >>| the (lookup z x)"
  proof-
    show ?thesis  
      apply (rule that[of "Abs_fmap ?zm"])
      apply (subst fdom.rep_eq)
      apply (subst  Abs_fmap_inverse)
      prefer 3
      apply (subst (2) lookup.rep_eq)
      apply (subst  Abs_fmap_inverse)
      apply (auto simp add: dom_def)
      apply (erule f)
      done
  qed

  have "S >>| z"
    apply (rule is_glbI)
    apply (rule is_lbI)
    apply (rule fmap_belowI')
    apply simp
    apply (rule is_lbD)
    apply (rule is_glbD1)
    apply (rule z, simp)
    apply auto
    apply (rule fmap_belowI')
    apply (metis `S \<noteq> {}` `\<And>m. m \<in> S \<Longrightarrow> fdom m = fdom b` `fdom z = fdom b` all_not_in_conv fmap_below_dom is_lbD)
    apply (rule is_glbD2)
    apply (rule z, simp)
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule fmap_belowE)
    apply (erule (1) is_lbD)
    done
  thus "\<exists> z. S >>| z" by auto
qed

end
