theory LaunchburyAbstractTransformation
imports Launchbury
begin


locale reds_rel = 
  fixes rel :: "(heap \<times> exp) \<Rightarrow> var list \<Rightarrow> (heap \<times> exp) \<Rightarrow>  bool" ("_ \<triangleright>\<^bsub>_\<^esub> _" [50,50,50] 50 )

locale reds_rel_fresh = reds_rel +
  assumes fresh_rel1[simp]: "(\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> \<Gamma>'"
  assumes fresh_rel2[simp]: "(\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> a \<sharp> e \<Longrightarrow> a \<sharp> e'"

locale rel_lambda_cong = reds_rel + 
  assumes rel_lambda_cong: "(\<Gamma>, Lam [x]. e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', lam) \<Longrightarrow> (\<And>e'. lam = Lam [x]. e' \<Longrightarrow> thesis) \<Longrightarrow> thesis"

locale rel_lambda_case = rel_lambda_cong
begin
lemma lambda_case:
  fixes \<Gamma> x e L \<Gamma>' e'
  assumes "(\<Gamma>, Lam [x]. e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')"
  shows "\<exists>\<Delta>' z'. (\<Gamma>, Lam [x]. e) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
proof-
  note assms
  moreover
  then obtain e'' where "e' = Lam [x]. e''" by (rule rel_lambda_cong)
  moreover
  have "\<Gamma>' : Lam [x]. e'' \<Down>\<^bsub>L\<^esub> \<Gamma>' : Lam [x]. e''"..
  ultimately show ?thesis by auto
qed
end

locale rel_app_cong = reds_rel + 
  assumes rel_app_cong: "(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> (\<And>e''. e' = App e'' x \<Longrightarrow> thesis) \<Longrightarrow> thesis"

locale rel_app_case = reds_rel_fresh + rel_lambda_cong + rel_app_cong +
  assumes rel_app_apply: "(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', App e'' x) \<Longrightarrow> (\<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e'')"
  assumes rel_lam_subst: "(\<Gamma>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', Lam [y]. body') \<Longrightarrow> (\<Gamma>, body[y::=x]) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', body'[y::=x])"
begin
lemma app_case:
  fixes y \<Gamma> e x L \<Delta> \<Theta> z body
  assumes "atom y \<sharp> \<Gamma>"
  assumes "atom y \<sharp> e"
  assumes "atom y \<sharp> x"
  assumes "atom y \<sharp> L"
  assumes "atom y \<sharp> \<Delta>"
  assumes "atom y \<sharp> \<Theta>"
  assumes "atom y \<sharp> z"
  assumes "\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. body"
  assumes "\<And> \<Gamma>' e'. (\<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e') \<Longrightarrow> \<exists>\<Delta>'' z'. (\<Delta>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>'', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>x # L\<^esub> \<Delta>'' : z'"
  assumes "\<Delta> : body[y::=x] \<Down>\<^bsub>L\<^esub> \<Theta> : z"
  assumes "\<And> \<Gamma>' e'. (\<Delta>, body[y::=x]) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> \<exists>\<Delta>' z'. (\<Theta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
  assumes "(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')"
  shows "\<exists>\<Delta>' z'. (\<Theta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
proof-
  from `(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')`
  obtain e'' where "e' = App e'' x" by (rule rel_app_cong)
  from `(\<Gamma>, App e x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')`[unfolded this]
  have "(\<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e'')" by (rule rel_app_apply)
  from assms(9)[OF this]
  obtain \<Delta>' lam
  where "(\<Delta>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>', lam)" and reds1: "\<Gamma>' : e'' \<Down>\<^bsub>x # L\<^esub> \<Delta>' : lam" by blast
  from this(1)
  obtain body' where "lam = Lam [y]. body'" by (rule rel_lambda_cong)

  from `(\<Delta>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>', lam)`[unfolded `lam = _`]
  have "(\<Delta>, body[y::=x]) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', body'[y::=x])" by (rule rel_lam_subst)
  from assms(11)[OF this]
  obtain \<Theta>' z'
  where "(\<Theta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Theta>', z')" and reds2: "\<Delta>' : body'[y::=x] \<Down>\<^bsub>L\<^esub> \<Theta>' : z'" by blast

  have "atom y \<sharp> (\<Gamma>', e'', x, L, \<Delta>', \<Theta>', z')"
    using assms(1-7) `(\<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e'')` `(\<Delta>, Lam [y]. body) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>', lam)` `(\<Theta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Theta>', z')`
    by (auto simp add: fresh_Pair)
    
  hence "\<Gamma>' :  App e'' x \<Down>\<^bsub>L\<^esub> \<Theta>' : z'"
    by (rule reds.Application[OF _ reds1[unfolded `lam = _`] reds2])
  with `(\<Theta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Theta>', z')` `e' = _`
  show ?thesis by blast
qed
end

locale rel_var_cong = reds_rel + 
  assumes rel_var_cong: "(\<Gamma>, Var x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> e' = Var x"

locale rel_var_case = rel_var_cong +
  assumes rel_lookup: "(\<Gamma>, Var x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', Var x) \<Longrightarrow> map_of \<Gamma> x = Some e \<Longrightarrow> (\<And>e'. map_of \<Gamma>' x = Some e' \<Longrightarrow> (delete x \<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (delete x \<Gamma>', e') \<Longrightarrow> thesis) \<Longrightarrow>  thesis"
  assumes rel_add_binding: " x \<notin> domA \<Delta> \<Longrightarrow> (\<Delta>, z) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>'', z') \<Longrightarrow> ((x, z) # \<Delta>, z) \<triangleright>\<^bsub>L\<^esub> ((x, z') # \<Delta>'', z')"
begin
lemma var_case:
  fixes \<Gamma> x e L \<Delta> z \<Gamma>' var
  assumes "map_of \<Gamma> x = Some e"
  assumes "delete x \<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : z"
  assumes "\<And> \<Gamma>' e'. (delete x \<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (\<Gamma>', e') \<Longrightarrow> \<exists>\<Delta>'' z'. (\<Delta>, z) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>'', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>x # L\<^esub> \<Delta>'' : z'"
  assumes "(\<Gamma>, Var x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', var)"
  shows "\<exists>\<Delta>'' z'. ((x, z) # \<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>'', z') \<and> \<Gamma>' : var \<Down>\<^bsub>L\<^esub> \<Delta>'' : z'"
  proof-
    from `(\<Gamma>, Var x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', var)`
    have "var = Var x" by (rule rel_var_cong)
  
    from `(\<Gamma>, Var x) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', var)`[unfolded `var = _`]
        and `map_of \<Gamma> x = Some e`
    obtain e' where "map_of \<Gamma>' x = Some e'" and  "(delete x \<Gamma>, e) \<triangleright>\<^bsub>x # L\<^esub> (delete x \<Gamma>', e')" by (rule rel_lookup)
    from assms(3)[OF this(2)]
    obtain \<Delta>'' z'
    where "(\<Delta>, z) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>'', z')" and "delete x \<Gamma>' : e' \<Down>\<^bsub>x # L\<^esub> \<Delta>'' : z'" by blast

    have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF assms(2)]) simp_all
    with `(\<Delta>, z) \<triangleright>\<^bsub>x # L\<^esub> (\<Delta>'', z')`
    have "((x,z)#\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> ((x,z')#\<Delta>'', z')" by (rule rel_add_binding[rotated])
    moreover
    from  `map_of \<Gamma>' x = Some e'` and `delete x \<Gamma>' : e' \<Down>\<^bsub>x # L\<^esub> \<Delta>'' : z'`
    have "\<Gamma>' : (Var x) \<Down>\<^bsub>L\<^esub> (x,z')#\<Delta>'' : z'"..
    ultimately
    show ?thesis unfolding `var = _` by auto
  qed
end

locale rel_let_cong = reds_rel +
  fixes \<Gamma> as body
  assumes rel_let_cong: "(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let') \<Longrightarrow> (\<And>as' body'. let' = Let as' body' \<Longrightarrow> map fst as = map fst as' \<Longrightarrow> thesis) \<Longrightarrow> thesis"

locale rel_let_case = rel_let_cong + reds_rel_fresh + 
  assumes rel_let:
    "(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', Let as' body') \<Longrightarrow>
     map fst as = map fst as' \<Longrightarrow>
     atom ` domA as \<sharp>* \<Gamma> \<Longrightarrow>  
     atom ` domA as \<sharp>* L \<Longrightarrow>  
     (as @ \<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (as' @ \<Gamma>', body')"
  (*  assumes rel_heap_subset: " (\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e'') \<Longrightarrow> domA as' \<subseteq> domA as" *)
begin
lemma let_case:
  fixes L \<Delta> z \<Gamma>' let'
  assumes "atom ` domA as \<sharp>* \<Gamma>"
  assumes "atom ` domA as \<sharp>* L"
  assumes "as @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "\<And> \<Gamma>' e' . (as @ \<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e') \<Longrightarrow> \<exists>\<Delta>'' z'. (\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>'', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>'' : z'"
  assumes "(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')"
  shows "\<exists>\<Delta>'' z'. (\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>'', z') \<and> \<Gamma>' : let' \<Down>\<^bsub>L\<^esub> \<Delta>'' : z'"
proof-
  from `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')`
  obtain as' body' where "let' = Let as' body'" and "map fst as = map fst as'"   by (rule rel_let_cong)

  from `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')`[unfolded `let' = _`] `map _ _ = _` assms(1,2)
  have "(as@\<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (as'@\<Gamma>', body')" by (rule rel_let)
  from assms(4)[OF this]
  obtain \<Delta>' z' where "(\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z')" and "as' @ \<Gamma>' : body' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'" by blast

  (* from `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')`[unfolded `let' = _`] *)
  have "domA as' \<subseteq> domA as" using `map fst as = map fst as'` unfolding domA_def by (metis list.set_map order_refl)
  hence "atom ` domA as' \<sharp>* (\<Gamma>', L)"
    using assms(1-2) `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')`
    by (auto simp add: fresh_Pair fresh_star_def)

  from this `as' @ \<Gamma>' : body' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'`
  have "\<Gamma>' : Let as' body' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
    by (rule reds.Let)
  with `(\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z')`
  show ?thesis unfolding `let' = _` by auto
qed
end


end
