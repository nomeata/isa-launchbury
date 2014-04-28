theory ValueSimilarity
imports Value CValue
begin

subsubsection {* Working with @{typ Value} and @{typ CValue} *}

lemma value_CValue_cases:
  obtains
  "x = \<bottom>" "y = \<bottom>" |
  f where "x = Fn\<cdot>f" "y = \<bottom>" |
  g where "x = \<bottom>" "y = CFn \<cdot> g" |
  f g where "x = Fn\<cdot>f" "y = CFn \<cdot> g"
by (metis CValue'.exhaust Value.exhaust)

lemma Value_CValue_take_induct:
  assumes "adm (split P)"
  assumes "\<And> n. P (Value_take n\<cdot>x) (CValue_take n\<cdot>y)"
  shows "P x y"
proof-
  have "split P (\<Squnion>n. (Value_take n\<cdot>x, CValue_take n\<cdot>y))"
    by (rule admD[OF `adm (split P)` ch2ch_Pair[OF ch2ch_Rep_cfunL[OF Value.chain_take] ch2ch_Rep_cfunL[OF CValue_chain_take]]])
       (simp add: assms(2))
  hence "split P (x,y)"
    by (simp add: lub_Pair[OF ch2ch_Rep_cfunL[OF Value.chain_take] ch2ch_Rep_cfunL[OF CValue_chain_take]]
                  Value.reach CValue_reach)
  thus ?thesis by simp
qed

subsubsection {* Restricted similarity is defined recursively *}

text {* The base case *}

inductive similar'_base :: "Value \<Rightarrow> CValue' \<Rightarrow> bool" where
  bot_similar'_base[simp,intro]: "similar'_base \<bottom> \<bottom>"

inductive_cases [elim!]:
   "similar'_base x y"

text {* The inductive case *}

inductive similar'_step :: "(Value \<Rightarrow> CValue' \<Rightarrow> bool) \<Rightarrow> Value \<Rightarrow> CValue' \<Rightarrow> bool" for s where
  bot_similar'_step[intro!]: "similar'_step s \<bottom> \<bottom>" |
  Fun_similar'_step[intro]: "(\<And> x y . s x (y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> s (f\<cdot>x) (g\<cdot>y\<cdot>C\<^sup>\<infinity>)) \<Longrightarrow> similar'_step s (Fn\<cdot>f) (CFn\<cdot>g)"

inductive_cases [elim!]:
   "similar'_step s x \<bottom>"
   "similar'_step s \<bottom> y"
   "similar'_step s (Fn\<cdot>f) (CFn\<cdot>g)"

text {* Combining the cases *}

text {* This cannot be one inductive definition as it would not be monotone. *}

fun similar' where
 "similar' 0 = similar'_base" |
 "similar' (Suc n) = similar'_step (similar' n)"
declare similar'.simps[simp del]

abbreviation similar'_syn  ("_ \<triangleleft>\<triangleright>\<^bsub>_\<^esub> _" [50,50,50] 50)
  where "similar'_syn x n y \<equiv> similar' n x y"

lemma similar'_botI[intro!,simp]: "\<bottom> \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<bottom>"
  by (cases n) (auto simp add: similar'.simps)

lemma similar'_FnI[intro]:
  assumes "\<And>x y.  x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
  shows "Fn\<cdot>f \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CFn\<cdot>g"
using assms by (auto simp add: similar'.simps)

lemma similar'_FnE[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CFn\<cdot>g"
  assumes "(\<And>x y.  x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g\<cdot>y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> P"
  shows P
using assms by (auto simp add: similar'.simps)

lemma bot_or_not_bot':
  "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y \<Longrightarrow> (x = \<bottom> \<longleftrightarrow> y = \<bottom>)"
  by (cases n) (auto simp add: similar'.simps elim: similar'_base.cases similar'_step.cases)

lemma similar'_bot[elim_format, elim!]:
    "\<bottom> \<triangleleft>\<triangleright>\<^bsub>n\<^esub> x \<Longrightarrow> x = \<bottom>"
    "y \<triangleleft>\<triangleright>\<^bsub>n\<^esub> \<bottom> \<Longrightarrow> y = \<bottom>"
by (metis bot_or_not_bot')+

subsubsection {* Moving up and down the similarity relations *}

lemma similar'_down: "d \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> e \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>e"
  and similar'_up: "d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> e \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>Suc n\<^esub> CValue'_take n\<cdot>e"
proof (induction n arbitrary: d e)
  case (Suc n) case 1 with  Suc
  show ?case
  by (cases d e rule:value_CValue_cases) auto
next
  case (Suc n) case 2 with Suc
  show ?case
  by (cases d e rule:value_CValue_cases) auto
qed auto

lemma similar'_up_le: "n \<le> m \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n \<cdot> e \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>m\<^esub> CValue'_take n\<cdot>e"
  by (induction rule: dec_induct )
     (auto dest: similar'_up simp add: Value.take_take CValue'.take_take min_absorb2)

lemma similar'_down_le: "n \<le> m \<Longrightarrow> Value_take m \<cdot> d \<triangleleft>\<triangleright>\<^bsub>m\<^esub> CValue'_take m \<cdot> e \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>e"
  by (induction rule: inc_induct )
     (auto dest: similar'_down simp add: Value.take_take CValue'.take_take min_absorb1)

lemma similar'_take: "d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> e \<Longrightarrow> Value_take n \<cdot> d \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>e"
  apply (drule similar'_up)
  apply (drule similar'_down)
  apply (simp add: Value.take_take CValue'.take_take)
  done

subsubsection {* Admissibility *}

lemma similar'_base_adm: "adm (\<lambda> x. similar'_base (fst x) (snd x))"
proof (rule admI)
  case (goal1 Y)
  from goal1 have "Y = (\<lambda> _ . \<bottom>)" by (metis PairE fst_eqD inst_prod_pcpo prod_case_beta similar'_base.simps snd_eqD)
  thus ?case by auto
qed  

lemma similar'_step_adm:
  assumes "adm (\<lambda> x. s (fst x) (snd x))"
  shows "adm (\<lambda> x. similar'_step s (fst x) (snd x))"
proof (rule admI)
  case (goal1 Y)
  from `chain Y`
  have "chain (\<lambda> i. fst (Y i))" by (rule ch2ch_fst)
  thus ?case
  proof(rule Value_chainE)
    assume "(\<lambda>i. fst (Y i)) = (\<lambda> _ . \<bottom>)"
    hence *: "\<And> i. fst (Y i) = \<bottom>" by metis
    with goal1(2)[unfolded split_beta]
    have "\<And> i. snd (Y i) = \<bottom>" by auto
    hence "Y = (\<lambda> i. (\<bottom>, \<bottom>))" using * by (metis surjective_pairing)
    thus ?thesis by auto
  next
    fix n
    fix Y'
    assume "chain Y'" and "(\<lambda>i. fst (Y i)) = (\<lambda> m. (if m < n then \<bottom> else Fn\<cdot>(Y' (m-n))))"
    hence Y': "\<And> i. fst (Y (i+n)) = Fn\<cdot>(Y' i)" by (metis add_diff_cancel_right' not_add_less2)
    with goal1(2)[unfolded split_beta]
    have "\<And> i. \<exists> g'. snd (Y (i+n)) = CFn\<cdot>g'"  by (metis CValue'.con_rews Value.con_rews similar'_step.simps)
    then obtain Y'' where Y'': "\<And> i. snd (Y (i+n)) = CFn\<cdot>(Y'' i)" by metis
    
    have "chain Y''"
      apply (rule chainI)
      apply (rule iffD1[OF CValue'.inverts])
      apply (subst (1 2) Y''[symmetric])
      by (metis add_Suc_right comm_semiring_1_class.normalizing_semiring_rules(24) goal1(1) po_class.chain_def snd_monofun)
    
    have "similar'_step s (Fn\<cdot>(\<Squnion> i. (Y' i))) (CFn \<cdot> (\<Squnion> i. Y'' i))"
    proof (rule Fun_similar'_step)
      fix x y
      from goal1(2) Y' Y''
      have "\<And>i. similar'_step s (Fn\<cdot>(Y' i)) (CFn\<cdot>(Y'' i))" by metis
      moreover
      assume "s x (y\<cdot>C\<^sup>\<infinity>)"
      ultimately
      have "\<And>i. s (Y' i\<cdot>x) (Y'' i\<cdot>y\<cdot>C\<^sup>\<infinity>)" by auto
      hence "split s (\<Squnion> i. ((Y' i)\<cdot>x, (Y'' i)\<cdot>y\<cdot>C\<^sup>\<infinity>))"
        apply -
        apply (rule admD[OF adm_prod_case[where P = "\<lambda>_ . s", OF assms]])
        apply (simp add:  `chain Y'`  `chain Y''`)
        apply simp
        done
      thus "s ((\<Squnion> i. Y' i)\<cdot>x) ((\<Squnion> i. Y'' i)\<cdot>y\<cdot>C\<^sup>\<infinity>)"
        by (simp add: lub_Pair  ch2ch_Rep_cfunL contlub_cfun_fun  `chain Y'`  `chain Y''`)
    qed
    hence "similar'_step s (fst (\<Squnion> i. Y (i+n))) (snd (\<Squnion> i. Y (i+n)))"
      by (simp add: Y' Y''
          cont2contlubE[OF cont_fst chain_shift[OF goal1(1)]]  cont2contlubE[OF cont_snd chain_shift[OF goal1(1)]]
           contlub_cfun_arg[OF `chain Y''`] contlub_cfun_arg[OF `chain Y'`])
    thus "similar'_step s (fst (\<Squnion> i. Y i)) (snd (\<Squnion> i. Y i))"
      by (simp add: lub_range_shift[OF `chain Y`])
  qed
qed

lemma similar'_adm: "adm (\<lambda>x. fst x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> snd x)"
  by (induct n) (auto simp add: similar'.simps intro: similar'_base_adm similar'_step_adm)

lemma similar'_admI: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> g x)"
  by (rule adm_subst[OF _ similar'_adm, where t = "\<lambda>x. (f x, g x)", simplified]) auto

subsubsection {* The real similarity relation *}

definition similar :: "Value \<Rightarrow> CValue' \<Rightarrow> bool" (infix "\<triangleleft>\<triangleright>" 50) where
  "x \<triangleleft>\<triangleright> y \<longleftrightarrow> (\<forall>n. Value_take n \<cdot> x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n \<cdot> y)"

lemma similarI:
  "(\<And> n.  Value_take n \<cdot> x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n \<cdot> y) \<Longrightarrow> x \<triangleleft>\<triangleright> y"
  unfolding similar_def by blast

lemma similarE:
  "x \<triangleleft>\<triangleright> y \<Longrightarrow> Value_take n \<cdot> x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n \<cdot> y"
  unfolding similar_def by blast

lemma similar_bot[simp]: "\<bottom> \<triangleleft>\<triangleright> \<bottom>" by (auto intro: similarI)
 
lemma [elim_format, elim!]: "x \<triangleleft>\<triangleright> \<bottom> \<Longrightarrow> x = \<bottom>"
  unfolding similar_def
  apply (cases x)
  apply auto
  apply (erule_tac x = "Suc 0" in allE)
  apply auto
  done

lemma [elim_format, elim!]: "\<bottom> \<triangleleft>\<triangleright> y \<Longrightarrow> y = \<bottom>"
  unfolding similar_def
  apply (cases y)
  apply auto
  apply (erule_tac x = "Suc 0" in allE)
  apply auto
  done

lemma take_similar'_similar:
  assumes "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y"
  shows  "Value_take n \<cdot> x \<triangleleft>\<triangleright> CValue'_take n \<cdot> y"
proof(rule similarI)
  fix m
  from assms
  have "Value_take n \<cdot> x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n \<cdot> y" by (rule similar'_take)
  moreover
  have "n \<le> m \<or> m \<le> n" by auto
  ultimately
  show "Value_take m\<cdot>(Value_take n\<cdot>x) \<triangleleft>\<triangleright>\<^bsub>m\<^esub> CValue'_take m\<cdot>(CValue'_take n\<cdot>y)"
    by (auto elim: similar'_up_le similar'_down_le dest: similar'_take
        simp add: min_absorb2 min_absorb1 Value.take_take CValue'.take_take)
qed

lemma bot_or_not_bot:
  "x \<triangleleft>\<triangleright> y \<Longrightarrow> (x = \<bottom> \<longleftrightarrow> y = \<bottom>)"
  by (cases x y rule:value_CValue_cases) auto

lemma slimilar_bot_cases[consumes 1, case_names bot Fn]:
  assumes "x \<triangleleft>\<triangleright> y"
  obtains "x = \<bottom>" "y = \<bottom>" |
  f g where "x = Fn\<cdot>f" "y = CFn \<cdot> g"
using assms
by (metis bot_or_not_bot CValue'.exhaust Value.exhaust)

lemma similar_adm: "adm (\<lambda>x. fst x \<triangleleft>\<triangleright> snd x)"
  unfolding similar_def
  by (intro adm_lemmas similar'_admI cont2cont)

lemma similar_admI: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f x \<triangleleft>\<triangleright> g x)"
  by (rule adm_subst[OF _ similar_adm, where t = "\<lambda>x. (f x, g x)", simplified]) auto

lemma admD2:
  assumes "adm (\<lambda>x. P (fst x) (snd x))"
  assumes "chain Y1"
  assumes "chain Y2"
  assumes "(\<And> i. P (Y1 i) (Y2 i))"
  shows "P (\<Squnion> i. Y1 i) (\<Squnion> i. Y2 i)"
proof-
  from assms(1) have "adm (split P)" by simp
  moreover
  from assms(2,3) have "chain (\<lambda>i. (Y1 i, Y2 i))" by simp
  moreover
  from assms(4) have "\<And> i. split P (Y1 i, Y2 i)" by simp
  ultimately
  have "split P (\<Squnion> i. (Y1 i, Y2 i))" by (rule admD)
  also have "(\<Squnion> i. (Y1 i, Y2 i)) = (\<Squnion> i. Y1 i, \<Squnion> i. Y2 i)"
    using assms(2,3) by (rule lub_Pair)
  finally
  show ?thesis by simp
qed

lemma similar_nice_def: "x \<triangleleft>\<triangleright> y \<longleftrightarrow> (x = \<bottom> \<and> y = \<bottom> \<or> (\<exists> f g. x = Fn \<cdot> f \<and> y = CFn \<cdot> g \<and> (\<forall> a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>)))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  thus "?R"
  proof (cases x y rule:slimilar_bot_cases)
    case bot thus ?thesis by simp
  next 
    case (Fn f g)
    note `?L`[unfolded Fn]
    have "\<forall>a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>"
    proof(intro impI allI)
      fix a b
      assume "a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity>"

      show "f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>" 
      proof(rule similarI)
        fix n
        have "adm (\<lambda>(b, a). Value_take n\<cdot>(f\<cdot>b) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>(g\<cdot>a\<cdot>C\<^sup>\<infinity>))"
          by (rule adm_prod_case, intro similar'_admI cont2cont)
        thus "Value_take n\<cdot>(f\<cdot>a) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>(g\<cdot>b\<cdot>C\<^sup>\<infinity>)"
        proof (induct a b rule: Value_CValue_take_induct[consumes 1])
          fix m

          from `a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity>`
          have "Value_take m \<cdot> a \<triangleleft>\<triangleright>\<^bsub>m\<^esub> CValue'_take m \<cdot>(b\<cdot>C\<^sup>\<infinity>)" by (rule similarE)
          hence "Value_take m \<cdot> a \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub> CValue'_take m \<cdot>(b\<cdot>C\<^sup>\<infinity>)" by (rule similar'_up_le[rotated]) auto
          moreover
          from `Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g`
          have "Value_take (Suc (max m n))\<cdot>(Fn\<cdot>f) \<triangleleft>\<triangleright>\<^bsub>Suc (max m n) \<^esub> CValue'_take (Suc (max m n))\<cdot>(CFn\<cdot>g)" by (rule similarE)
          ultimately
          have "Value_take (max m n)\<cdot>(f\<cdot>(Value_take (max m n)\<cdot>(Value_take m\<cdot>a))) \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub>
              CValue'_take (max m n)\<cdot>(g\<cdot>(CValue_take (max m n)\<cdot>(CValue_take m\<cdot>b))\<cdot>C\<^sup>\<infinity>)"
            by (auto)
          hence "Value_take (max m n)\<cdot>(f\<cdot>(Value_take m\<cdot>a)) \<triangleleft>\<triangleright>\<^bsub>max m n\<^esub> CValue'_take (max m n)\<cdot>(g\<cdot>(CValue_take m\<cdot>b)\<cdot>C\<^sup>\<infinity>)"
            by (simp add: Value.take_take cfun_map_map CValue'.take_take ID_def eta_cfun min_absorb2 min_absorb1)
          thus "Value_take n\<cdot> (f\<cdot>(Value_take m\<cdot>a)) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>(g\<cdot>(CValue_take m\<cdot>b)\<cdot>C\<^sup>\<infinity>)"
            by (rule similar'_down_le[rotated]) auto
        qed
      qed
    qed
    thus ?thesis unfolding Fn by simp
  qed
next
  assume "?R"
  thus "?L"
  proof(elim conjE disjE exE ssubst)
    show "\<bottom> \<triangleleft>\<triangleright> \<bottom>" by simp
  next
    fix f g
    assume imp: "\<forall>a b. a \<triangleleft>\<triangleright> b\<cdot>C\<^sup>\<infinity> \<longrightarrow> f\<cdot>a \<triangleleft>\<triangleright> g\<cdot>b\<cdot>C\<^sup>\<infinity>"
    show "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
    proof (rule similarI)
      fix n
      show "Value_take n\<cdot>(Fn\<cdot>f) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>(CFn\<cdot>g)"
      proof(cases n)
        case 0 thus ?thesis by simp
      next
        case (Suc n)
        { fix x y
          assume "x \<triangleleft>\<triangleright>\<^bsub>n\<^esub> y\<cdot>C\<^sup>\<infinity>"
          hence "Value_take n \<cdot> x \<triangleleft>\<triangleright> CValue'_take n \<cdot>(y\<cdot>C\<^sup>\<infinity>)" by (rule take_similar'_similar)
          hence "f\<cdot>(Value_take n \<cdot> x) \<triangleleft>\<triangleright> g\<cdot>(cfun_map\<cdot>ID\<cdot>(CValue'_take n)\<cdot>y)\<cdot>C\<^sup>\<infinity>" using imp by auto
          hence "Value_take n\<cdot>(f\<cdot>(Value_take n\<cdot>x)) \<triangleleft>\<triangleright>\<^bsub>n\<^esub> CValue'_take n\<cdot>(g\<cdot>(cfun_map\<cdot>ID\<cdot>(CValue'_take n)\<cdot>y)\<cdot>C\<^sup>\<infinity>)"
            by (rule similarE)
        }
        with Suc
        show ?thesis by auto
      qed
    qed
  qed
qed

lemma similar_FnI[intro]:
  assumes "\<And>x y.  x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
  shows "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
by (metis assms similar_nice_def)

lemma similar_FnD[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
  assumes "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
  shows "f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>"
using assms 
by (subst (asm) similar_nice_def) auto

lemma similar_FnE[elim!]:
  assumes "Fn\<cdot>f \<triangleleft>\<triangleright> CFn\<cdot>g"
  assumes "(\<And>x y.  x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity> \<Longrightarrow> f\<cdot>x \<triangleleft>\<triangleright> g\<cdot>y\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> P"
  shows P
by (metis assms similar_FnD)

subsubsection {* The similarity relation lifted to function *}

abbreviation fmap_similar :: "('a::type \<Rightarrow> Value) \<Rightarrow> ('a \<Rightarrow> CValue) \<Rightarrow> bool"  (infix "f\<triangleleft>\<triangleright>" 50) where
  "fmap_similar \<equiv> pointwise (\<lambda>x y. x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>)"

lemma fmap_similar_adm: "adm (\<lambda>x. fst x f\<triangleleft>\<triangleright> snd x)"
  by (intro pointwise_adm similar_admI) auto

lemma fmap_similar_fmap_bottom[simp]: "\<bottom> f\<triangleleft>\<triangleright> \<bottom>"
  by auto

lemma fmap_similarE[elim]:
  assumes "m f\<triangleleft>\<triangleright> m'"
  assumes "(\<And>x. (m  x) \<triangleleft>\<triangleright> (m' x)\<cdot>C\<^sup>\<infinity>) \<Longrightarrow> Q"
  shows Q
  apply (rule assms(2))
  using assms(1) unfolding pointwise_def
  by blast

end
