theory SestoftGC
imports Sestoft 
begin

inductive gc_step :: "(var list \<times> conf) \<Rightarrow> (var list \<times> conf) \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>G" 50) where
  normal:  "c \<Rightarrow> c' \<Longrightarrow> (r, c) \<Rightarrow>\<^sub>G (r, c')"
| dropUpd: "(r, \<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G (x # r, \<Gamma>, e, S)"

lemmas gc_step_intros[intro] =
  normal[OF step.intros(1)] normal[OF step.intros(2)] normal[OF step.intros(3)]
  normal[OF step.intros(4)] normal[OF step.intros(5)]  dropUpd


abbreviation gc_steps (infix "\<Rightarrow>\<^sub>G\<^sup>*" 50) where "gc_steps \<equiv> gc_step\<^sup>*\<^sup>*"
lemmas converse_rtranclp_into_rtranclp[of gc_step, OF _ r_into_rtranclp, trans]

lemma var_onceI:
  assumes "map_of \<Gamma> x = Some e"
  shows "(r, \<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* (x#r, delete x \<Gamma>, e , S)"
proof-
  from assms 
  have "(r, \<Gamma>, Var x, S) \<Rightarrow>\<^sub>G (r, delete x \<Gamma>, e , Upd x # S)"..
  moreover
  have "\<dots> \<Rightarrow>\<^sub>G  (x #r, delete x \<Gamma>, e , S)"..
  ultimately
  show ?thesis by (rule converse_rtranclp_into_rtranclp[OF _ r_into_rtranclp])
qed

lemma normal_trans:  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow> (r, c) \<Rightarrow>\<^sub>G\<^sup>* (r, c')"
  by (induction rule:rtranclp_induct)
     (simp, metis normal rtranclp.rtrancl_into_rtrancl)

fun to_gc_conf :: "var list \<Rightarrow> conf \<Rightarrow> conf"
  where "to_gc_conf r (\<Gamma>, e, S) = (restrictA (- set r) \<Gamma>, e, restr_stack (- set r) S)"

lemma to_gc_conf_append[simp]:
  "to_gc_conf (r@r') c = to_gc_conf r (to_gc_conf r' c)"
  by (cases c) auto

lemma to_gc_conf_eqE[elim!]:
  assumes  "to_gc_conf r c = (\<Gamma>, e, S)"
  obtains \<Gamma>' S' where "c = (\<Gamma>', e, S')" and "\<Gamma> = restrictA (- set r) \<Gamma>'" and "S = restr_stack (- set r) S'"
  using assms
  by (cases c) auto

fun safe_hd :: "'a list \<Rightarrow> 'a option"
 where  "safe_hd (x#_) = Some x"
     |  "safe_hd [] = None"

lemma safe_hd_None[simp]: "safe_hd xs = None \<longleftrightarrow> xs = []"
  by (cases xs) auto

abbreviation r_ok :: "(var list \<times> conf) \<Rightarrow> bool"
  where "r_ok c \<equiv> set (fst c) \<subseteq> domA (fst (snd c)) \<union> upds (snd (snd (snd c)))"


lemma sestoftUnGCStack:
  assumes "heap_upds_ok (\<Gamma>, S)"
  assumes "set r \<subseteq> domA \<Gamma> \<union> upds S"
  obtains \<Gamma>' S' where
    "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
    "heap_upds_ok (\<Gamma>', S')"
    "to_gc_conf r (\<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
    "\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S')"
    "set r \<subseteq> domA \<Gamma>' \<union> upds S'"
(*proof(atomize_elim)
  show "\<exists>\<Gamma>' S'. (\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S') \<and> heap_upds_ok (\<Gamma>', S') \<and> to_gc_conf r (\<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S') \<and> (\<not> isVal e \<or>  safe_hd S' = safe_hd (restr_stack (- set r) S'))"
*)
proof-
  show ?thesis
  proof(cases "isVal e")
    case False
    thus ?thesis using assms  by -(rule that, auto)
  next
    case True
    from that assms 
    show ?thesis
    apply (atomize_elim)
    proof(induction S arbitrary: \<Gamma>)
      case Nil thus ?case by (fastforce)
    next
      case (Cons s S)
      show ?case
      proof(cases "Some s = safe_hd (restr_stack (- set r) (s#S))")
        case True
        thus ?thesis
          using `isVal e` `heap_upds_ok (\<Gamma>, s # S)` `set r \<subseteq> domA \<Gamma> \<union> upds (s # S)`
          apply auto
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply auto
          done
      next
        case False
        then obtain x where [simp]: "s = Upd x" and [simp]: "x \<in> set r"
          by(cases s) (auto split: if_splits)
      
        from `heap_upds_ok (\<Gamma>, s # S)` `s = Upd x`
        have [simp]: "x \<notin> domA \<Gamma>" and "heap_upds_ok ((x,e) # \<Gamma>, S)"
          by (auto dest: heap_upds_okE) 

        from `set r \<subseteq> domA \<Gamma> \<union> upds (s # S)`
        have "set r \<subseteq> domA ((x,e) # \<Gamma>) \<union> upds S" by auto
        
        have "(\<Gamma>, e, s # S) \<Rightarrow>\<^sup>* (\<Gamma>, e, Upd x # S)" unfolding `s = _` ..
        also have "\<dots> \<Rightarrow> ((x,e) # \<Gamma>, e, S)" by (rule var\<^sub>2[OF `x \<notin> domA \<Gamma>` `isVal e`])
        also
        from Cons.IH[OF `heap_upds_ok ((x,e) # \<Gamma>, S)`  `set r \<subseteq> domA ((x,e) # \<Gamma>) \<union> upds S`]
        obtain \<Gamma>' S' where  "((x,e) # \<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
            and res: "heap_upds_ok (\<Gamma>', S')"
                     "to_gc_conf r ((x,e) # \<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
                     "(\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S'))"
                     "set r \<subseteq> domA \<Gamma>' \<union> upds S'"
          by blast
        note this(1)
        finally
        have "(\<Gamma>, e, s # S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')".
        thus ?thesis  using res by auto
      qed
    qed
  qed
qed
  

lemma sestoftUnGCstep:
  assumes "to_gc_conf r c \<Rightarrow> d"
  assumes "heap_upds_ok_conf c"
  assumes "r_ok (r, c)"
  shows   "\<exists> c'. c \<Rightarrow>\<^sup>* c' \<and> d = to_gc_conf r c' \<and> heap_upds_ok_conf c' \<and> r_ok (r, c')"
proof-
  obtain \<Gamma> e S where "c = (\<Gamma>, e, S)" by (cases c) auto
  with assms
  have "heap_upds_ok (\<Gamma>,S)" and "set r \<subseteq> domA \<Gamma> \<union> upds S" by auto
  from sestoftUnGCStack[OF this]
  obtain \<Gamma>' S' where
    "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
    and *: "to_gc_conf r (\<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
    and disj: "\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S')"
    and "heap_upds_ok (\<Gamma>', S')"
    and "set r \<subseteq> domA \<Gamma>' \<union> upds S'" by metis
  note this(1)
  also

  from assms(1)[unfolded `c =_ ` *]
  have "\<exists> \<Gamma>'' e'' S''. (\<Gamma>', e, S') \<Rightarrow> (\<Gamma>'', e'', S'')  \<and> d = to_gc_conf r (\<Gamma>'', e'', S'') \<and> heap_upds_ok (\<Gamma>'', S'') \<and> set r \<subseteq> domA \<Gamma>'' \<union> upds S''"
  proof(cases rule: step.cases)
    case app\<^sub>1
    thus ?thesis
      using `heap_upds_ok (\<Gamma>', S')` and `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply auto
      done
  next
    case app\<^sub>2
    thus ?thesis
      using disj  `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply (cases S')
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply auto
      done
  next
    case var\<^sub>1
    thus ?thesis
      using `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply (auto simp add: restr_delete_twist)
      done
  next
    case var\<^sub>2
    thus ?thesis
      using disj `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply (cases S')
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
      done
  next
    case (let\<^sub>1 \<Delta>'' \<Gamma>'' S'' e')
    thus ?thesis
      using `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply (auto simp add: restrictA_append)
      sorry
  next
    case if\<^sub>1
    thus ?thesis
      using `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply auto
      apply (intro exI conjI)
      apply (rule step.intros)
      apply (auto)
      done
  next
    case if\<^sub>2
    thus ?thesis
      using disj `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`
      apply (cases S')
      apply auto
      apply (intro exI conjI)
      apply (rule step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
      apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
      apply (intro exI conjI)
      apply (rule step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
      apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
      done
  qed
  then obtain \<Gamma>'' e'' S''
    where "(\<Gamma>', e, S') \<Rightarrow> (\<Gamma>'', e'', S'')"
    and "d = to_gc_conf r (\<Gamma>'', e'', S'')"
    and "heap_upds_ok (\<Gamma>'', S'')"
    and "set r \<subseteq> domA \<Gamma>'' \<union> upds S''"
    by blast
  note this(1)
  finally
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>'', e'', S'')".
  with `d = _` `heap_upds_ok (\<Gamma>'', S'')` `set r \<subseteq> domA \<Gamma>'' \<union> upds S''`
  show ?thesis unfolding `c = _` by auto
qed


lemma sestoftUnGC:
  assumes "(r, to_gc_conf r c) \<Rightarrow>\<^sub>G\<^sup>* (r', d)" and "heap_upds_ok_conf c" and "r_ok (r, c)"
  shows   "\<exists> c'. c \<Rightarrow>\<^sup>* c' \<and> d = to_gc_conf r' c' \<and> heap_upds_ok_conf c' \<and> r_ok (r', c')"
using assms
proof(induction r' "d"  rule: rtranclp_induct2)
  case refl
  thus ?case by blast
next
  case (step r' d' r'' d'')
  then obtain c' where "c \<Rightarrow>\<^sup>* c'" and "d' = to_gc_conf r' c'" and "heap_upds_ok_conf c'" and "r_ok (r', c')" by auto
  with step
  have "(r', to_gc_conf r' c') \<Rightarrow>\<^sub>G (r'', d'')" by simp
  hence "\<exists> c''. c' \<Rightarrow>\<^sup>* c'' \<and> d'' = to_gc_conf r'' c'' \<and> heap_upds_ok_conf c'' \<and> r_ok (r'', c'')"
  proof(cases rule: gc_step.cases)
    case normal
    from sestoftUnGCstep[OF normal(2) `heap_upds_ok_conf c'` `r_ok (r',c')`] `r'' = r'`
    show ?thesis by auto
  next
    case (dropUpd \<Gamma> e x S)
    from `to_gc_conf r' c' = (\<Gamma>, e, Upd x # S)`
    have "x \<notin> set r'" by (auto dest: Upd_eq_restr_stackD)
    
    from `heap_upds_ok_conf c'` and `to_gc_conf r' c' = (\<Gamma>, e, Upd x # S)`
    have "heap_upds_ok (\<Gamma>, Upd x # S)" by fastforce
    hence [simp]: "x \<notin> domA \<Gamma>" "x \<notin> upds S" by (auto dest: heap_upds_ok_upd)

    from `to_gc_conf r' c' = (\<Gamma>, e, Upd x # S)`
    have "Upd x # S = restr_stack (- set r') (snd (snd c'))"  by auto
    from arg_cong[where f = upds, OF this]
    have "x \<in> upds (snd (snd c'))" by auto
    with `r_ok (r', c')` have "r_ok (x # r', c')" by auto

    have "to_gc_conf (x # r') c' = to_gc_conf ([x]@ r') c'" by simp
    also have "\<dots> = to_gc_conf [x] (to_gc_conf r' c')" by (rule to_gc_conf_append)
    also have "\<dots> = to_gc_conf [x] (\<Gamma>, e, Upd x # S)" unfolding `to_gc_conf r' c' = _`..
    also have "\<dots> = (\<Gamma>, e, S)" by (auto intro: restrictA_noop)
    finally have "to_gc_conf (x # r') c' = (\<Gamma>, e, S)".
    with dropUpd  `heap_upds_ok_conf c'` `r_ok (x # r', c')`
    show ?thesis by fastforce
  qed
  then obtain c'' where "c' \<Rightarrow>\<^sup>* c''" and "d'' = to_gc_conf r'' c''" and "heap_upds_ok_conf c''" and "r_ok (r'', c'')" by auto
  with `c \<Rightarrow>\<^sup>* c'` `c' \<Rightarrow>\<^sup>* c''`
  have "c \<Rightarrow>\<^sup>* c''" by auto
  with `d'' = _` `heap_upds_ok_conf c''` `r_ok (r'', c'')`
  show ?case by blast
qed
  
lemma sestoftUnGC':
  assumes "([], [], e, []) \<Rightarrow>\<^sub>G\<^sup>* (r, \<Gamma>, e', [])"
  assumes "isVal e'"
  shows   "\<exists> \<Gamma>''. ([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>'', e', []) \<and> \<Gamma> = restrictA (- set r) \<Gamma>'' \<and> set r \<subseteq> domA \<Gamma>''"
proof-
 from sestoftUnGC[where r = "[]" and c = "([], e, [])", simplified, OF assms(1)]
 obtain \<Gamma>' S'
  where "([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>', e', S')"
    and "\<Gamma> = restrictA (- set r) \<Gamma>'"
    and "restr_stack (- set r) S' = []"
    and "heap_upds_ok (\<Gamma>', S')"
    and "set r \<subseteq> domA \<Gamma>' \<union> upds S'"
    by auto
 
  from `isVal e'` sestoftUnGCStack[where e = e', OF `heap_upds_ok (\<Gamma>', S')` `set r \<subseteq> domA \<Gamma>' \<union> upds S'`]
  obtain \<Gamma>'' S''
    where "(\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Gamma>'', e', S'')"
    and   "heap_upds_ok (\<Gamma>'', S'')"
    and "to_gc_conf r (\<Gamma>', e', S') = to_gc_conf r (\<Gamma>'', e', S'')"
    and "safe_hd S'' = safe_hd (restr_stack (- set r) S'')"
    and "set r \<subseteq> domA \<Gamma>'' \<union> upds S''"
    by metis
  from this (3,4) `restr_stack (- set r) S' = []`
  have "S'' = []" by auto
 
  from `([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>', e', S')` and `(\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Gamma>'', e', S'')` and `S'' = []`
  have "([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>'', e', [])" by auto
  moreover
  have "\<Gamma> = restrictA (- set r) \<Gamma>''" using `to_gc_conf r _ = _` `\<Gamma> = _` by auto
  moreover
  from `set r \<subseteq> domA \<Gamma>'' \<union> upds S''` `S'' = []`
  have "set r \<subseteq> domA \<Gamma>''" by simp
  ultimately
  show ?thesis by blast
qed


end

