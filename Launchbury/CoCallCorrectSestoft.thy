theory CoCallCorrectSestoft
imports CoCallAnalysis SestoftCorrect AEnv
begin

fun Astack :: "AEnv \<Rightarrow> stack \<Rightarrow> Arity"
  where "Astack ae [] = 0"
      | "Astack ae (Arg x # S) = inc\<cdot>(Astack ae S)"
      | "Astack ae (Upd x # S) = (case ae x of Iup a \<Rightarrow> a)"
      | "Astack ae (Dummy x # S) = 0"

lemma Astack_cong: "(\<And> x. x \<in> upds S \<Longrightarrow> ae x = ae' x) \<Longrightarrow>  Astack ae S = Astack ae' S"
  by (induction S  rule: Astack.induct) auto

lemma Astack_Upd_simps[simp]:
  "ae x = up\<cdot>u \<Longrightarrow> Astack ae (Upd x # S) = u"
  by (simp add: up_def cont_Iup)
declare Astack.simps(3)[simp del]


inductive AE_consistent :: "AEnv \<Rightarrow> CoCalls \<Rightarrow> conf \<Rightarrow> bool" where
  AE_consistentI: 
  "edom ae \<subseteq> domA \<Gamma> \<union> upds S
  \<Longrightarrow> upds S \<subseteq> edom ae
(*  \<Longrightarrow> AEstack ae S \<sqsubseteq> ae  *)
  \<Longrightarrow> Aexp e \<cdot> (Astack ae S) \<sqsubseteq> ae
  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> Aexp' e \<cdot> (ae x) \<sqsubseteq> ae)
(*  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ae x = up\<cdot>0) not needed with CoCall Analysis *)
  \<Longrightarrow> ae ` ap S \<subseteq> {up\<cdot>0}
  \<Longrightarrow> ae ` upds S \<subseteq> {up\<cdot>0}
  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> ae x = \<bottom> \<or>  ae x = up\<cdot>0 \<or> (x--x\<notin>G))
  \<Longrightarrow> AE_consistent ae G (\<Gamma>, e, S)"

