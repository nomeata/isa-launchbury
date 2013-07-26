theory LaunchburyNoBH
imports Terms Heap  "~~/src/HOL/Library/Permutation"
begin

lemma perm_eqvt[eqvt]: "\<pi> \<bullet> (G <~~> G') \<longleftrightarrow> (\<pi> \<bullet> G) <~~> (\<pi> \<bullet> G')"
  by (auto intro!: perm_rel_lemma2 elim: perm.induct simp add: permute_pure)

lemma perm_supp: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> supp \<Gamma> = supp \<Gamma>'"
  by (induction rule: perm.induct) (auto simp add: supp_Cons)

lemma perm_heapVars: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> heapVars \<Gamma> = heapVars \<Gamma>'"
  by (induction rule: perm.induct) auto

lemma perm_distinctVars: "\<Gamma> <~~> \<Gamma>' \<Longrightarrow> distinctVars \<Gamma> \<longleftrightarrow> distinctVars \<Gamma>'"
  by (induction rule: perm.induct) (auto simp add: distinctVars_Cons perm_heapVars)

inductive reds :: "heap \<Rightarrow> var \<Rightarrow> heap \<Rightarrow> bool" ("_/ \<Down>\<^bsub>_\<^esub>/ _" [50,50,50] 50)
where
  Lambda:
    "(x, (Lam [y]. e)) # \<Gamma> \<Down>\<^bsub>x\<^esub> (x, (Lam [y]. e)) # \<Gamma>" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,\<Delta>,\<Theta>);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^bsub>n\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (x, e'[z ::= y]) # \<Delta> \<Down>\<^bsub>x\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^bsub>x\<^esub> \<Theta>" 
 | ApplicationInd: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,x,e,y,\<Delta>,\<Theta>,z);
      atom z \<sharp> (\<Gamma>,x,e,y,\<Delta>);
      (n, e) # (x, App (Var n) y) # \<Gamma> \<Down>\<^bsub>n\<^esub> (n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>;
      (z,Var y) # (x, e') # \<Delta> \<Down>\<^bsub>x\<^esub> \<Theta>
    \<rbrakk> \<Longrightarrow>
      (x, App e y) # \<Gamma> \<Down>\<^bsub>x\<^esub> \<Theta>" 
 | Variable: "\<lbrakk>
      (x, Var y) # \<Gamma> \<Down>\<^bsub>y\<^esub> (y,z) # (x, Var y) # \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Var y) # \<Gamma> \<Down>\<^bsub>x\<^esub> (y,z) # (x,z) # \<Delta>"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x);
      distinctVars (asToHeap as);
      (x, body) # asToHeap as @ \<Gamma> \<Down>\<^bsub>x\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow>
      (x, Let as body) # \<Gamma> \<Down>\<^bsub>x\<^esub> \<Delta>"
 | Permute: "\<lbrakk>
      \<Gamma> <~~> \<Gamma>';
      \<Delta> <~~> \<Delta>';
      \<Gamma> \<Down>\<^bsub>x\<^esub> \<Delta>
   \<rbrakk> \<Longrightarrow> 
      \<Gamma>' \<Down>\<^bsub>x\<^esub> \<Delta>'"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z" | ApplicationInd: "n"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair pure_fresh)


end

