theory "Value-Complete"
  imports "HOLCF-Join" "Down"
begin


domain Value_ = Fn (lazy "Value_ d \<rightarrow> Value_ d")
type_synonym Value = "Value_ d"

lemma maximal_fun: "f \<sqsubseteq> (\<lambda>x. \<top>)"
  by (simp add: below_fun_def)

instance "fun"  :: (type, Top_cpo) Top_cpo
  by default (fast intro: maximal_fun)

lemma inst_fun_Top_cpo: "\<top> = (\<lambda>x. \<top>)"
  by (rule maximal_fun [THEN topI, symmetric])

lemma app_strict [simp]: "\<top> x = \<top>"
  by (simp add: inst_fun_Top_cpo)

lemma lambda_preserves_top: "(\<lambda>x. \<top>) = \<top>"
  by (rule topI, rule maximal_fun)

lemma top_cfun: "\<top> \<in> cfun"
  by (simp add: cfun_def inst_fun_Top_cpo)

instance cfun :: (cpo, Top_cpo) Top_cpo
  apply default
  apply (rule exI[where x = "\<Lambda> _ . \<top>"])
  apply (simp add: cfun_below_iff)
  done

lemma cfun_top: "\<top> = (\<Lambda> _ . \<top>)"
  apply (subst top_def)
  apply (rule the1_equality)
  apply (metis most po_eq_conv)
  apply (auto simp add: cfun_below_iff)
  done

lemma cfun_top_simp[simp]: "\<top>\<cdot>x = \<top>"
  unfolding cfun_top  by simp

context
  fixes lift_d :: "((Value_ \<rightarrow> Value_ \<rightarrow> Value_) \<rightarrow> (Value \<rightarrow> Value \<rightarrow> Value))"
begin
fixrec
  meet' :: "Value_ \<rightarrow> Value_ \<rightarrow> Value_"
  where 
    "meet'\<cdot>\<bottom>\<cdot>x = \<bottom>"
  | "meet'\<cdot>x\<cdot>\<bottom> = \<bottom>"
  | "meet'\<cdot>(Fn\<cdot>f)\<cdot>(Fn\<cdot>g) =  Fn\<cdot>(\<Lambda> x. lift_d\<cdot>meet'\<cdot>(f \<cdot> x)\<cdot>(g \<cdot> x))"
end

definition meet_d :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<rightarrow> 'a d \<rightarrow> 'a d \<rightarrow> 'a d"
  where
    "meet_d = (\<Lambda> m x y . (case x of Itop \<Rightarrow> y | Idown a => (case y of Itop \<Rightarrow> x | Idown b => down\<cdot>(m\<cdot>a\<cdot>b))))"

definition meet :: "Value_ \<rightarrow> Value_ \<rightarrow> Value_"
  where "meet = meet' meet_d"

lemma meet_simps[simp]:
  "meet\<cdot>\<bottom>\<cdot>x = \<bottom>"
  "meet\<cdot>x\<cdot>\<bottom> = \<bottom>"
 unfolding meet_def by auto


(*
lemma cont2cont_meet_d[simp, cont2cont]: "cont h \<Longrightarrow> cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x . meet_d (h x) (f x) (g x))"
  oops

fixrec meet :: "Value_ \<rightarrow> Value_ \<rightarrow> Value_"
  where 
    "meet\<cdot>\<bottom>\<cdot>x = \<bottom>"
  | "meet\<cdot>x\<cdot>\<bottom> = \<bottom>"
  | "meet\<cdot>(Fn\<cdot>f)\<cdot>(Fn\<cdot>g) =  Fn\<cdot>(\<Lambda> x. meet_d meet (f \<cdot> x) (g \<cdot> x))"
*)


lemma "(t \<sqsubseteq> meet\<cdot>u\<cdot>v) = (t \<sqsubseteq> u \<and> t \<sqsubseteq> v)"
proof (induct t rule: Value_.take_induct)
  fix n
  show "(Value__take n\<cdot>t \<sqsubseteq> meet\<cdot>u\<cdot>v) = (Value__take n\<cdot>t \<sqsubseteq> u \<and> Value__take n\<cdot>t \<sqsubseteq> v)"
  proof(induct n arbitrary: u v)
  print_cases
  case 0 thus ?case by auto
  next
  case (Suc n u v)
    show ?case
    proof(cases u)
    case bottom thus ?thesis by auto
    next
    case (Fn u')
      thus ?thesis 
      proof(cases v)
      case bottom thus ?thesis by auto
      next
      case (Fn v') 
      show ?thesis
      proof (cases t)
        case bottom thus ?thesis by auto
      next
        have tmp: "\<And>P Q R. (\<And> x. P x = (Q x \<and> R x)) \<Longrightarrow> (\<forall>x. P x) = ((\<forall>x. Q x) \<and> (\<forall>x. R x))" by metis
        case (Fn t')
          show ?thesis
          proof
            assume "Value__take (Suc n)\<cdot>t \<sqsubseteq> meet\<cdot>u\<cdot>v"
            (*
            with `u = _`  `v = _` `t = _` 
            have asm: "cfun_map\<cdot>(d_map\<cdot>(Value__take n))\<cdot>(d_map\<cdot>(Value__take n))\<cdot>t' \<sqsubseteq>  (\<Lambda> x. (case u'\<cdot>x of down\<cdot>a \<Rightarrow> \<Lambda> (down\<cdot>b). down\<cdot>(meet\<cdot>a\<cdot>b))\<cdot>(v'\<cdot>x))"  apply simp
            *)
            
            have "cfun_map\<cdot>(d_map\<cdot>(Value__take n))\<cdot>(d_map\<cdot>(Value__take n))\<cdot>t' \<sqsubseteq> u'"
            proof (rule cfun_belowI)
              fix x
              (*
              from asm
              have "cfun_map\<cdot>(d_map\<cdot>(Value__take n))\<cdot>(d_map\<cdot>(Value__take n))\<cdot>t' \<cdot>x \<sqsubseteq>  (\<Lambda> x. (case u'\<cdot>x of down\<cdot>a \<Rightarrow> \<Lambda> (down\<cdot>b). down\<cdot>(meet\<cdot>a\<cdot>b))\<cdot>(v'\<cdot>x))\<cdot>x"
                by (auto simp add: cfun_below_iff)
              *)
              have "d_map\<cdot>(Value__take n)\<cdot>(t'\<cdot>(d_map\<cdot>(Value__take n)\<cdot>x)) \<sqsubseteq> (case u'\<cdot>x of down\<cdot>a \<Rightarrow> \<Lambda> (down\<cdot>b). down\<cdot>(meet\<cdot>a\<cdot>b))\<cdot>(v'\<cdot>x)" sorry
              also
              have "(case u'\<cdot>x of down\<cdot>a \<Rightarrow> \<Lambda> (down\<cdot>b). down\<cdot>(meet\<cdot>a\<cdot>b))\<cdot>(v'\<cdot>x) \<sqsubseteq> u'\<cdot>x"
                apply (cases "u' \<cdot> x")
                apply simp
                apply simp
                apply (cases "v' \<cdot> x")
                apply simp
                sorry
              finally
              have "d_map\<cdot>(Value__take n)\<cdot>(t'\<cdot>(d_map\<cdot>(Value__take n)\<cdot>x)) \<sqsubseteq> u'\<cdot>x " .             
              thus "cfun_map\<cdot>(d_map\<cdot>(Value__take n))\<cdot>(d_map\<cdot>(Value__take n))\<cdot>t'\<cdot>x \<sqsubseteq> u'\<cdot>x" by simp
            qed
            hence "Value__take (Suc n)\<cdot>(Fn\<cdot>t') \<sqsubseteq> (Fn\<cdot>u')" by simp
            hence "Value__take (Suc n)\<cdot>t \<sqsubseteq> u" unfolding `t = _` `u = _` .
            moreover
            have "Value__take (Suc n)\<cdot>t \<sqsubseteq> v" sorry
            ultimately
            show "Value__take (Suc n)\<cdot>t \<sqsubseteq> u \<and> Value__take (Suc n)\<cdot>t \<sqsubseteq> v" ..



 apply simp
          apply (simp add: cfun_below_iff)
          apply (rule tmp)
          apply (case_tac "u' \<cdot> x")
          apply simp
          apply (case_tac "t'\<cdot>(d_map\<cdot>(Value__take n)\<cdot>x)")
          apply simp

          apply (case_tac "v' \<cdot> x")
          apply simp
          apply (case_tac "x")
          apply auto[1]
          find_theorems d_map

    find_theorems Value__take
    apply (simp add: Value_.take_Suc)
    apply auto
    

apply auto[1]
apply (induct_tac n )
apply auto[1]




find_theorems name:Value_ name:take
*)

lemma up_set_cases:
  fixes S  :: "'a u set"
  obtains Sbottom and  Sabove
  where "Sbottom \<subseteq> {Ibottom}" and "Sbottom \<union> Iup ` Sabove = S"
proof-
  have "S \<inter> {Ibottom} \<subseteq> {Ibottom}" by auto
  moreover
  have "Iup ` ((\<lambda>x. THE z. x = Iup z) ` (S - {Ibottom})) = S - {Ibottom}" 
    apply (intro set_eqI)
    apply (case_tac x rule:u.exhaust)
    apply auto[1]

    apply rule

    apply (erule imageE)
    apply auto[1]
    apply (rule classical)
    apply (erule notE)
    apply (rule the1I2)
    apply auto[1]
    apply (metis u.exhaust)
    apply simp

    apply (simp only:)
    apply (rule imageI)
    apply (erule rev_image_eqI)
    apply (rule the1I2)
    apply auto
    done
  hence "(S \<inter> {Ibottom}) \<union> Iup ` ((\<lambda>x. THE z. x = Iup z) ` (S - {Ibottom})) = S" by auto
  ultimately
  show thesis ..
qed

lemma is_glb_with_bottom: "\<bottom> \<in> S \<Longrightarrow> S >>| \<bottom>"
  by (metis is_glb_maximal is_lbI minimal)

lemma "Rep_cfun (Value__take (Suc i)) (Fn \<cdot> x) = undefined"
  apply simp 
  unfolding cfun_map_def
  thm cfun_map_def d_map_def
  apply simp
  oops

lemma is_lb_cfun_iff: " S >| u \<longleftrightarrow> (\<forall>x. (\<lambda>f. f\<cdot>x) ` S >| u\<cdot>x)"
  apply rule
  apply rule
  apply (rule is_lbI)
  apply (erule imageE)
  apply (metis cfun_below_iff is_lbD)
  apply (metis cfun_below_iff imageI  is_lbD is_lbI)
  done

lemma is_glb_cfunI: "(\<And> x. (\<lambda> f. f\<cdot>x) ` S >>| l\<cdot>x ) \<Longrightarrow> S >>| l"
  by (metis cfun_below_iff is_glbD1 is_glbD2 is_glbI is_lb_cfun_iff)

lemma has_glb_cfunI: assumes "(\<And> x. \<exists> l. (\<lambda> f. f\<cdot>x) ` S >>| l)" shows "(\<exists> l. S >>| l)"
proof-
  obtain f
  where "\<And> x. (\<lambda> f. f\<cdot>x) ` S >>| f x"
    apply (erule_tac x = "\<lambda> x. SOME z . (\<lambda> f. f\<cdot>x) ` S >>| z"  in meta_allE)
    apply (erule meta_mp)
    apply (rule someI_ex[OF assms])
    done
  thus ?thesis
oops  


lemma is_glb_glb': "(\<exists>x . M >>| x) \<Longrightarrow> M >>| \<Sqinter>M " by (metis is_glb_glb)

lemma monofun_glb_image: assumes "(\<And> S. \<exists>l . Rep_cfun g ` S >>| l)" shows "monofun (\<lambda>y . \<Sqinter> Rep_cfun g ` y ` S)"
  apply (rule monofunI)
  
  apply (subst is_glb_above_iff [OF is_glb_glb'[OF assms]])
  
  apply (rule is_lbI)
  apply (erule imageE)+
  apply (subst (asm) below_fun_def)
  apply (erule_tac x = xc in allE)
  apply (frule_tac f = g in monofun_cfun_arg)
  apply simp
  apply (erule rev_below_trans)
  apply (rule is_lbD[OF is_glbD1[OF is_glb_glb'[OF assms]]])
  apply auto
  done

lemma cont_glb_image: assumes "(\<And> S. \<exists>l . Rep_cfun g ` S >>| l)" shows "cont (\<lambda>y . \<Sqinter> Rep_cfun g ` y ` S)"
  apply (rule contI2[OF monofun_glb_image[OF assms]])
  
  find_theorems lub below
  find_theorems lub name:cfun
  apply (rule is_lbD[OF is_glbD1[OF is_glb_glb'[OF assms]]])
oops

(* lemmas cont2cont_glb_image[simp,cont2cont] = cont_compose[OF cont_glb_image] *)
  

lemma 
  assumes "\<And> x y . \<exists> l. l \<sqsubseteq> g \<cdot> x \<and> l \<sqsubseteq> g \<cdot> y \<and> (\<forall> z. (z \<sqsubseteq> g \<cdot> x \<and> z \<sqsubseteq> g \<cdot> y) \<longrightarrow> z \<sqsubseteq> l)"
  shows "\<exists> l. l \<sqsubseteq> cfun_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> cfun_map\<cdot>f\<cdot>g\<cdot>y \<and> (\<forall> z. (z \<sqsubseteq> cfun_map\<cdot>f\<cdot>g\<cdot>x \<and> z \<sqsubseteq> cfun_map\<cdot>f\<cdot>g\<cdot>y) \<longrightarrow> z \<sqsubseteq> l)"
proof-
  oops

  
lemma 
  assumes "\<And> S. \<exists>l . Rep_cfun g ` S >>| l"
  shows "\<exists>l. Rep_cfun (cfun_map\<cdot>f\<cdot>g) ` S >>| l"
proof-
  let ?l = "(\<Lambda> x. (\<Sqinter> Rep_cfun g ` (\<lambda> h. h\<cdot>(f\<cdot>x)) ` S))"
  have "\<And> x. (\<lambda>f. f\<cdot>x) ` Rep_cfun (cfun_map\<cdot>f\<cdot>g) ` S = Rep_cfun g ` (\<lambda>h. h\<cdot>(f\<cdot>x)) ` S" 
    apply (subst (1 2) image_compose[symmetric])
    apply auto
    done
  hence "Rep_cfun (cfun_map\<cdot>f\<cdot>g) ` S >>| ?l"
  apply -
  apply (rule is_glb_cfunI)
  apply (subst beta_cfun)
  apply (rule cont2cont_glb_image[OF assms])
  apply simp
  apply simp
  apply (rule is_glb_glb')
  apply (rule assms)
  done
  thus ?thesis ..
qed


lemma take_has_meet:
  "S \<noteq> {} \<Longrightarrow> \<exists> u. {Value__take i \<cdot> x | x . x \<in> S } >>| u"
proof (induct i arbitrary: S)
  case 0
  hence "{Value__take 0 \<cdot> x | x . x \<in> S } = {\<bottom>}" by auto
  thus ?case by (metis is_glb_singleton)
next
  case (Suc i)
  show ?case
  proof (cases "\<bottom> \<in> S")
  case True 
    hence "\<bottom> \<in> {Value__take (Suc i)\<cdot>x |x. x \<in> S}"
      by (metis (lifting, full_types) CollectI Value_.take_strict)
    hence "{Value__take (Suc i)\<cdot>x |x. x \<in> S} >>| \<bottom>"
      by (rule is_glb_with_bottom)
    thus ?thesis ..
  next
  case False
    then obtain f where f: "\<And> x . x \<in> S \<Longrightarrow> x = Fn \<cdot> (f x)"
      by (metis Value_.nchotomy)
    (* hence "S = {Fn \<cdot> x | x . x \<in> f ` S}" sledgehammer *)
    have "{Value__take (Suc i)\<cdot>x |x. x \<in> S} = Rep_cfun (Value__take (Suc i)) ` S"  by auto also
    have "... =  Rep_cfun (Value__take (Suc i)) ` Rep_cfun Fn ` f ` S" using f by auto
    have "... =  Rep_cfun Fn ` Rep_cfun (Value__take (Suc i)) ` Rep_cfun Fn ` f ` S" using f by auto
    
    show ?thesis sorry
  qed
qed


instance Value_ :: Nonempty_Meet_cpo
proof default
  fix S
  assume "(S :: Value_ set) \<noteq> {}"
  show "\<exists> u. S >>| u"
  proof (cases "\<exists> u. S = {u}")
  case True thus ?thesis by (metis is_glb_singleton)
  next
  case False then obtain x1 x2 where "x1 \<in> S" and "x2 \<in> S" and "x1 \<noteq> x2"
    using `S \<noteq> {}` by (metis insertCI nonempty_iff)
  find_theorems name:Value_ name:take

  hence "\<exists> i. Value__take i \<cdot> x1 \<noteq> Value__take i \<cdot> x2"
    by (metis Value_.take_lemma)
  then obtain i where "Value__take i \<cdot> x1 \<noteq> Value__take i \<cdot> x2" by auto
  hence "\<not> (\<exists> u. {Value__take i \<cdot> x | x . x \<in> S } = {u})" (is " \<not> ?P i")
    using `S \<noteq> {}` `x1 \<in> S` `x2 : S`
    apply -
    apply (rule notI)
    apply (erule exE)
    apply (drule equalityD1)
    apply auto
    done
  moreover
  have "\<not> \<not> ?P 0"
    using `S \<noteq> {}` by auto
  ultimately
  have "\<exists>k<i. (\<forall>j\<le>k. \<not> \<not> ?P j) \<and> \<not> ?P (k+1)"
    by -(rule ex_least_nat_less) 
  oops

end
