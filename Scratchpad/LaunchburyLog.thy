theory LaunchburyLog
imports Terms Substitution "Arity-Nominal"
begin

type_synonym CallLog = "(var \<times> Arity) list"

inductive
  reds :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<Rightarrow>  var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> CallLog \<Rightarrow> bool"
  ("_ : _ \<Down>\<^bsub>_,_\<^esub> _ : _ (_)" [50,50,50,50,50,50] 50)
where
  Lambda:
    "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>n,L\<^esub> \<Gamma> : (Lam [x]. e) []" 
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z,c\<^sub>1,c\<^sub>2) ;
    \<Gamma> : e \<Down>\<^bsub>inc\<cdot>n,x#L\<^esub> \<Delta> : (Lam [y]. e') c\<^sub>1;
    \<Delta> : e'[y ::= x] \<Down>\<^bsub>n,L\<^esub> \<Theta> : z c\<^sub>2
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^bsub>n,L\<^esub> \<Theta> : z c\<^sub>1@c\<^sub>2"
 | Variable: "\<lbrakk>
    map_of \<Gamma> x = Some e;
    delete x \<Gamma> : e \<Down>\<^bsub>n,x#L\<^esub> \<Delta> : z c
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^bsub>n,L\<^esub> (x, z) # \<Delta> : z (x,n)#c"
 | Let: "\<lbrakk>
    atom ` domA as \<sharp>* (\<Gamma>, L);
    as @ \<Gamma> : body \<Down>\<^bsub>n,L\<^esub> \<Delta> : z c
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Terms.Let as body \<Down>\<^bsub>n,L\<^esub> \<Delta> : z c"

equivariance reds

nominal_inductive reds
  avoids Application: "y"
  by (auto simp add: fresh_star_def fresh_append pure_fresh fresh_Pair)

subsubsection {* Example evaluations *}

lemma eval_test:
  "[] : (Terms.Let [(x, Lam [y]. Var y)] (Var x)) \<Down>\<^bsub>0,[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y) [(x,0)]"
by(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def pure_fresh )

lemma ApplicationI: "
  atom y \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z, c\<^sub>1, c\<^sub>2) \<Longrightarrow>
  \<Gamma> : e \<Down>\<^bsub>inc\<cdot>n,x # L\<^esub> \<Delta> : Lam [y]. e' c\<^sub>1 \<Longrightarrow>
  \<Delta> : e'[y::=x] \<Down>\<^bsub>n,L\<^esub> \<Theta> : z c\<^sub>2 \<Longrightarrow>
  c\<^sub>1@c\<^sub>2 = c \<Longrightarrow>
  \<Gamma> : App e x \<Down>\<^bsub>n,L\<^esub> \<Theta> : z c"
by (metis Application)

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>[] : (Terms.Let [(x, Lam [y]. Var y)] (App (Var x) x)) \<Down>\<^bsub>0,[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y) [(x,inc\<cdot>0),(x,0)]"
  by (auto intro!: Lambda ApplicationI[where y = y and c\<^sub>2 = "[(x,0)]"] Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)


subsubsection {* Properties of the semantics *}

text {*
Heap entries are never removed.
*}

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^bsub>n,L\<^esub> \<Delta> : z c \<Longrightarrow> domA \<Gamma> \<subseteq> domA \<Delta>"
proof(induct rule: reds.induct)
case(Variable \<Gamma> v e n L \<Delta> z c)
  show ?case
  proof
    fix x
    assume "x \<in> domA \<Gamma>"
    show "x \<in> domA ((v, z) # \<Delta>)"
    proof(cases "x = v")
    case True 
      thus ?thesis by simp
    next
    case False
      with `x \<in> domA \<Gamma>`
      have "x \<in> domA (delete v \<Gamma>)" by simp
      hence "x \<in> domA \<Delta>" using Variable.hyps(3) by auto
      thus ?thesis by simp
    qed
  qed
qed (auto)

subsubsection {* Log talks about heap *}

lemma log_heap_subset:
  assumes  "\<Gamma> : e \<Down>\<^bsub>n,L\<^esub> \<Delta> : v c"
  shows "domA c \<subseteq> domA \<Delta>"
using assms
by (induction rule: reds.induct)(auto simp add: set_mp[OF reds_doesnt_forget])


subsubsection {* Better Introduction variables *}

lemma reds_ApplicationI:
  assumes "atom y \<sharp> x" (* Less freshness required here *)
  assumes "\<Gamma> : e \<Down>\<^bsub>inc\<cdot>n, x # L\<^esub> \<Delta> : Lam [y]. e' c\<^sub>1"
  assumes "\<Delta> : e'[y::=x] \<Down>\<^bsub>n,L\<^esub> \<Theta> : z c\<^sub>2"
  shows "\<Gamma> : App e x \<Down>\<^bsub>n,L\<^esub> \<Theta> : z (c\<^sub>1@c\<^sub>2)"
proof-
  obtain y' :: var where "atom y' \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z, e',c\<^sub>1,c\<^sub>2)" by (rule obtain_fresh)

  have a: "Lam [y']. ((y' \<leftrightarrow> y) \<bullet> e') = Lam [y]. e'"
    using `atom y' \<sharp> _`
    by (auto simp add: Abs1_eq_iff fresh_Pair fresh_at_base)

  have [simp]: "(y' \<leftrightarrow> y) \<bullet> x = x" using `atom y \<sharp> _`  `atom y' \<sharp> _`
      by (simp add: flip_fresh_fresh fresh_Pair fresh_at_base)

  have "((y' \<leftrightarrow> y) \<bullet> e')[y'::=x] = (y' \<leftrightarrow> y) \<bullet> (e'[y::=x])" by simp
  also have "\<dots> = e'[y::=x]"
    using `atom y \<sharp> _`  `atom y' \<sharp> _`
    by (simp add: flip_fresh_fresh fresh_Pair fresh_at_base subst_pres_fresh)
  finally
  have b: "((y' \<leftrightarrow> y) \<bullet> e')[y'::=x] = e'[y::=x]".


  have "atom y' \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z, c\<^sub>1, c\<^sub>2)" using  `atom y' \<sharp> _` by (simp add: fresh_Pair)
  from  this assms(2,3)[folded a b]
  show ?thesis ..
qed

(*
text {*
Live variables are not added to the heap.
*}

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> domA \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> domA \<Delta>"
proof(induct rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e') thus ?case by auto
next
case (Variable \<Gamma> x e L \<Delta> z)
   from Variable(1) have "x \<in> domA \<Gamma>" by (metis domA_from_set map_of_is_SomeD)
   with Variable
   show ?case by auto
next
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> domA \<Gamma>" by fact moreover
  have "set (bn as) \<sharp>* L" using `set (bn as) \<sharp>* (\<Gamma>, L)` by (simp add: fresh_star_Pair)
  hence "x \<notin> domA (asToHeap as)"
    using `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> domA (asToHeap as @ \<Gamma>)" by auto  
  thus ?case
    by (rule Let.hyps(3)[OF `x \<in> set L`])
qed

lemma reds_avoids_live':
 assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
 shows "set L \<subseteq> - (domA \<Delta> - domA \<Gamma>)"
using reds_avoids_live[OF assms] by auto

text {*
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (domA \<Delta> - set L)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> domA \<Delta> - set (x' # L)" by (auto simp add: fresh_Pair)

  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    show ?thesis
    proof(cases "x = y")
    case False
      hence "atom x \<sharp> e'" using `atom x \<sharp> (\<Delta>, Lam [y]. e')`
        by (auto simp add:fresh_Pair)
      hence "atom x \<sharp> e'[y ::= x']" using Application.prems
        by (auto intro: subst_pres_fresh[rule_format] simp add: fresh_Pair)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    qed
  next
    assume "x \<in> domA \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4)] by auto
  qed
next

case(Variable \<Gamma> v e L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair)
  from fresh_delete[OF this(1)]
  have "atom x \<sharp> delete v \<Gamma>".
  moreover
  have "v \<in> domA \<Gamma>" using Variable.hyps(1) by (metis domA_from_set map_of_is_SomeD)
  from fresh_map_of[OF this  `atom x \<sharp> \<Gamma>`]
  have "atom x \<sharp> the (map_of \<Gamma> v)".
  hence "atom x \<sharp> e" using `map_of \<Gamma> v = Some e` by simp
  ultimately
  have "atom x \<sharp> (\<Delta>, z) \<or> x \<in> domA \<Delta> - set (v # L)"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
  thus ?case using `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Let as \<Gamma> L body \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair)      
      show ?thesis
        apply(rule Let.hyps(3))
        using Let.prems `atom x \<sharp> as` False
        by (auto simp add: fresh_Pair fresh_append fresh_fun_eqvt_app[OF asToHeap_eqvt])
    next
    case True
      hence "x \<in> domA (asToHeap as)" 
        by(induct as rule:asToHeap.induct)(auto simp add: exp_assn.bn_defs)      
      moreover
      have "x \<notin> set L"
        using Let(1)
        by (metis True fresh_list_elem fresh_star_Pair fresh_star_def not_self_fresh)
      ultimately
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(2)] by auto
    qed
qed

lemma reds_fresh_fv: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> fv (\<Delta>, z) \<and> (x \<notin> domA \<Delta> \<or>  x \<in> set L)
  \<rbrakk> \<Longrightarrow> x \<in> fv (\<Gamma>, e)"
using reds_fresh
unfolding fv_def fresh_def
by blast

lemma new_vars_not_free:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "x \<in> domA \<Delta>"
  assumes "x \<in> set L"
  shows "x \<in> fv (\<Gamma>, e)"
  apply (rule reds_fresh_fv[OF assms(1)])
  using assms(2,3)
  apply (auto dest: set_mp[OF domA_fv_subset])
  done

lemma new_free_vars_on_heap:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  shows "fv (\<Delta>, z) - domA \<Delta> \<subseteq> fv (\<Gamma>, e) - domA \<Gamma>"
using reds_fresh_fv[OF assms(1)] reds_doesnt_forget[OF assms(1)] by auto

text {*
Reducing the set of variables to avoid is always possible.
*} 

lemma reds_smaller_L: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   set L' \<subseteq> set L
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule reds.Lambda)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z e' L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)
  
    have "set (xa # L') \<subseteq> set (xa # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^bsub>xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(10))

    show "\<Delta> : e'[y::=xa] \<Down>\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(12)[OF Application.prems])
  qed
next 
case (Variable \<Gamma> xa e L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (Let as \<Gamma>  L body \<Delta> z L')
  have "set (bn as) \<sharp>* (\<Gamma>, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _ Let.hyps(4)[OF Let.prems]])
qed

text {* Things are evaluated to a lambda expression, and the variable can be freely chose. *}

lemma result_evaluated_fresh:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  obtains y e'
  where "z = (Lam [y]. e')" and "atom y \<sharp> (c::'a::fs)"
proof-
  from assms
  have "\<exists> x e'. z = Lam [x]. e'"
    by (induct \<Gamma> e L \<Delta> z rule:reds.induct) (auto dest: reds_doesnt_forget)
  hence "\<exists> y e'. z = Lam [y]. e' \<and> atom y \<sharp> c"
    by (nominal_induct z avoiding: c rule:exp_assn.strong_induct(1)) auto
  thus thesis using that by blast
qed

*)
end

