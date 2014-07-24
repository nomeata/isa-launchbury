theory ImageP
imports Relation
begin

subsubsection {* Image of a set under a relation *}

definition ImageP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) => 'a set => 'b set" (infixr "```" 90)
where
  "r ``` s = {y. \<exists>x\<in>s. r x y}"

declare Image_def [no_atp]

lemma ImageP_iff: "(b : r```A) = (EX x:A. r x b)"
  by (simp add: ImageP_def)

lemma ImageP_singleton: "r```{a} = {b. r a b}"
  by (simp add: ImageP_def)

lemma ImageP_singleton_iff [iff]: "(b : r```{a}) = (r a b)"
  by (rule ImageP_iff [THEN trans]) simp

lemma ImagePI [intro,no_atp]: "r a b ==> a : A ==> b : r```A"
  by (unfold ImageP_def) blast

lemma ImagePE [elim!]:
  "b : r ``` A ==> (!!x. r x b ==> x : A ==> P) ==> P"
  by (unfold ImageP_def) (iprover elim!: CollectE bexE)

lemma rev_ImageIP: "a : A ==> r a b ==> b : r ``` A"
  -- {* This version's more effective when we already have the required @{text a} *}
  by blast

lemma ImageP_empty [simp]: "R```{} = {}"
  by blast

(*
lemma ImageP_Id [simp]: "Id ``` A = A"
  by blast

lemma ImageP_Id_on [simp]: "Id_on A ``` B = A \<inter> B"
  by blast
*)

lemma ImageP_Int_subset: "R ``` (A \<inter> B) \<subseteq> R ``` A \<inter> R ``` B"
  by blast

lemma ImageP_Int_eq:
  "single_valuedP (conversep R) ==> R ``` (A \<inter> B) = R ``` A \<inter> R ``` B"
  by (simp add: single_valued_def, blast) 

lemma ImageP_Un: "R ``` (A \<union> B) = R ``` A \<union> R ``` B"
  by blast

(*
lemma Un_ImageP: "(R \<union> S) ``` A = R ``` A \<union> S ``` A"
  by blast

lemma Image_subset: "r \<subseteq> A \<times> B ==> r``C \<subseteq> B"
  by (iprover intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (\<Union>y\<in> B. r``{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma Image_mono: "r' \<subseteq> r ==> A' \<subseteq> A ==> (r' `` A') \<subseteq> (r `` A)"
  by blast

lemma Image_UN: "(r `` (UNION A B)) = (\<Union>x\<in>A. r `` (B x))"
  by blast

lemma Image_INT_subset: "(r `` INTER A B) \<subseteq> (\<Inter>x\<in>A. r `` (B x))"
  by blast

text{*Converse inclusion requires some assumptions*}
lemma Image_INT_eq:
     "[|single_valued (r\<inverse>); A\<noteq>{}|] ==> r `` INTER A B = (\<Inter>x\<in>A. r `` B x)"
apply (rule equalityI)
 apply (rule Image_INT_subset) 
apply  (simp add: single_valued_def, blast)
done

lemma Image_subset_eq: "(r``A \<subseteq> B) = (A \<subseteq> - ((r^-1) `` (-B)))"
  by blast

lemma Image_Collect_split [simp]: "{(x, y). P x y} `` A = {y. EX x:A. P x y}"
  by auto
*)

end
