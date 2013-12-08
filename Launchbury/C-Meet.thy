theory "C-Meet"
imports C "HOLCF-Meet"
begin

lemma nat_mono_characterization:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "mono f"
  obtains n where "\<And>m . n \<le> m \<Longrightarrow> f n = f m" | "\<And> m . \<exists> n . m \<le> f n"
proof (cases "finite (range f)")
  case True
  from Max_in[OF True]
  obtain n where Max: "f n = Max (range f)" by auto
  show thesis
  proof(rule that)
    fix m
    assume "n \<le> m"
    hence "f n \<le> f m" using `mono f` by (metis monoD)
    also
    have "f m \<le> f n" unfolding Max by (rule Max_ge[OF True rangeI])
    finally
    show "f n = f m".
  qed
next
  case False
  thus thesis by (fastforce intro: that(2) simp add: infinite_nat_iff_unbounded_le)
qed

lemma C_cases:
  obtains n where "r = C\<^bsup>n\<^esup>" | "r = C\<^sup>\<infinity>"
proof-
  { fix m
    have "\<exists> n. C_take m \<cdot> r = C\<^bsup>n\<^esup> "
    proof (rule C.finite_induct)
      have "\<bottom> = C\<^bsup>0\<^esup>" by simp
      thus "\<exists>n. \<bottom> = C\<^bsup>n\<^esup>"..
    next
      fix r
      show "\<exists>n. r = C\<^bsup>n\<^esup> \<Longrightarrow> \<exists>n. C\<cdot>r = C\<^bsup>n\<^esup>"
        by (auto simp del: iterate_Suc simp add: iterate_Suc[symmetric])
    qed
  }
  then obtain f where take: "\<And> m. C_take m \<cdot> r = C\<^bsup>f m\<^esup>" by metis
  have "chain (\<lambda> m. C\<^bsup>f m\<^esup>)" using ch2ch_Rep_cfunL[OF C.chain_take, where x=r, unfolded take].
  hence "mono f" by (auto simp add: mono_iff_le_Suc chain_def elim!:chainE)
  have r: "r = (\<Squnion> m. C\<^bsup>f m\<^esup>)"  by (metis (lifting) take C.reach lub_eq)
  from `mono f`
  show thesis
  proof(rule nat_mono_characterization)
    fix n
    assume n: "\<And> m. n \<le> m ==> f n = f m"
    have "max_in_chain n (\<lambda> m. C\<^bsup>f m\<^esup>)"
      apply (rule max_in_chainI)
      apply simp
      apply (erule n)
      done
    hence "(\<Squnion> m. C\<^bsup>f m\<^esup>) = C\<^bsup>f n\<^esup>" unfolding  maxinch_is_thelub[OF `chain _`].
    thus ?thesis using that unfolding r by blast
  next
    assume "\<And>m. \<exists>n. m \<le> f n"
    hence "\<And> n. C\<^bsup>n\<^esup> \<sqsubseteq> r" unfolding r by (fastforce intro: below_lub[OF `chain _`])
    hence "(\<Squnion> n. C\<^bsup>n\<^esup>) \<sqsubseteq> r" 
      by (rule lub_below[OF chain_iterate])
    hence "C\<^sup>\<infinity> \<sqsubseteq> r" unfolding Cinf_def fix_def2.
    hence "C\<^sup>\<infinity> = r" using below_Cinf by (metis below_antisym)
    thus thesis using that by blast
  qed
qed

instantiation C :: Finite_Meet_cpo begin
  fixrec C_meet :: "C \<rightarrow> C \<rightarrow> C"
    where "C_meet\<cdot>(C\<cdot>a)\<cdot>(C\<cdot>b) = C\<cdot>(C_meet\<cdot>a\<cdot>b)"
  
  lemma[simp]: "C_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "C_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)  

  instance
  apply default
  proof(intro exI conjI strip)
    fix x y
    {
      fix t
      have "(t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (t \<sqsubseteq> x \<and> t \<sqsubseteq> y)"
      proof (induct t rule:C.take_induct)
        fix n
        show "(C_take n\<cdot>t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>t \<sqsubseteq> x \<and> C_take n\<cdot>t \<sqsubseteq> y)"
        proof (induct n arbitrary: t x y rule:nat_induct)
          case 0 thus ?case by auto
          next
          case (Suc n t x y)
            with C.nchotomy[of t] C.nchotomy[of x] C.nchotomy[of y]
            show ?case by fastforce
        qed
     qed auto
    } note * = this
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> x" using * by auto
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> y" using * by auto
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> C_meet\<cdot>x\<cdot>y" using * by auto
qed
end

lemma C_meet_is_meet: "(z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (z \<sqsubseteq> x \<and> z \<sqsubseteq> y)"
proof (induct z rule:C.take_induct)
  fix n
  show "(C_take n\<cdot>z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>z \<sqsubseteq> x \<and> C_take n\<cdot>z \<sqsubseteq> y)"
  proof (induct n arbitrary: z x y rule:nat_induct)
    case 0 thus ?case by auto
    next
    case (Suc n z x y) thus ?case
      apply -
      apply (cases z, simp)
      apply (cases x, simp)
      apply (cases y, simp)
      apply (fastforce simp add: cfun_below_iff)
      done
  qed
qed auto

instance C :: cont_binary_meet
proof
  have [simp]:"\<And> x y. x \<sqinter> y = C_meet\<cdot>x\<cdot>y"
    using C_meet_is_meet
    by (blast intro: is_meetI)
  case goal1 thus ?case
    by (simp add: ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun)
qed

lemma [simp]: "C\<cdot>r \<sqinter> r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma [simp]: "r \<sqinter> C\<cdot>r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma [simp]: "(r \<sqinter> Cpred\<cdot>r) = Cpred \<cdot> r"
  by (metis Cpred_below below_refl is_meetI)

lemma [simp]: "(Cpred\<cdot>r \<sqinter> r) = Cpred \<cdot> r"
  by (metis Cpred_below below_refl is_meetI)

lemma [simp]: "C\<cdot>r \<sqinter> C\<cdot>r' = C\<cdot>(r \<sqinter> r')"
  apply (rule is_meetI)
  apply (metis below_refl meet_below1 monofun_cfun_arg)
  apply (metis below_refl meet_below2 monofun_cfun_arg)
  apply (case_tac a)
  apply auto
  by (metis meet_above_iff)

end
