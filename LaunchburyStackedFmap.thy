theory LaunchburyStackedFmap
imports Terms Heap "FMap-Nominal"
begin

type_synonym fheap = "(var, exp) fmap"

inductive reds :: "fheap \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> fheap \<Rightarrow> fheap \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> fheap \<Rightarrow> bool" ("_ : _ \<mapsto> _ : _ \<Down> _ : _ \<mapsto> _ : _" [50,50,50,50,50,50,50,50] 50)
where
  Lambda: "\<Gamma> : x \<mapsto> (Lam [y]. e) : \<Gamma>' \<Down> \<Gamma> : x \<mapsto> (Lam [y]. e) : \<Gamma>'" 
 | Application: "\<lbrakk>
      atom n \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,fmap_delete x \<Delta>',x,e,y,\<Theta>,\<Theta>',z',z);
      atom z \<sharp> (\<Gamma>,\<Gamma>',\<Delta>,fmap_delete x \<Delta>',x,e,y,\<Theta>,\<Theta>',z');
      \<Gamma> : n \<mapsto> e : \<Gamma>'( x  f\<mapsto> App (Var n) y) \<Down> \<Delta> : n \<mapsto> (Lam [z]. e') : \<Delta>';
      \<Delta> : x \<mapsto> e'[z ::= y] : fmap_delete x \<Delta>' \<Down> \<Theta> : x \<mapsto> z' : \<Theta>'
    \<rbrakk> \<Longrightarrow>
      \<Gamma> : x \<mapsto> (App e y) : \<Gamma>' \<Down>  \<Theta> : x \<mapsto> z' : \<Theta>'" 
 | Variable: "\<lbrakk>
      y \<in> fdom \<Gamma>;
      Some e = lookup \<Gamma> y;
      fmap_delete y \<Gamma> : y \<mapsto> e: \<Gamma>'(x f\<mapsto> Var y) \<Down> \<Delta> : y \<mapsto> z : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : x \<mapsto> Var y : \<Gamma>' \<Down> \<Delta>(y f\<mapsto> z) : x \<mapsto> z : fmap_delete x \<Delta>'"
 | Let: "\<lbrakk>
      set (bn as) \<sharp>* (\<Gamma>, x, Let as body, \<Gamma>');
      distinctVars (asToHeap as);
      \<Gamma> f++ fmap_of (asToHeap as) : x \<mapsto> body : \<Gamma>' \<Down> \<Delta> : x \<mapsto> z : \<Delta>'
   \<rbrakk> \<Longrightarrow>
      \<Gamma> : x \<mapsto> Let as body : \<Gamma>' \<Down> \<Delta> :  x \<mapsto> z : \<Delta>'"

equivariance reds

nominal_inductive reds
  avoids Application: "n" and "z"
  by (auto simp add: fresh_star_def fresh_Cons fresh_Pair exp_assn.fresh)


end

