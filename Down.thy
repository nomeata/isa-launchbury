(*  Title:      Down.ty
    Author:     Franz Regensburger
    Author:     Brian Huffman
    Author:     Joachim Breitner
*)

header {* The type of lifted values *}

theory Down
imports "HOLCF-Join"
begin

default_sort cpo

datatype 'a d = Itop | Idown 'a

type_notation (xsymbols)
  u  ("(_\<^sub>\<top>)" [1000] 999)

primrec Ifdown :: "('a \<rightarrow> 'b::Top_cpo) \<Rightarrow> 'a d \<Rightarrow> 'b" where
    "Ifdown f Itop = \<top>"
 |  "Ifdown f (Idown x) = f\<cdot>x"

subsection {* Ordering on lifted cpo *}

instantiation d :: (cpo) below
begin

definition
  below_down_def:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. case y of Itop \<Rightarrow> True | Idown a \<Rightarrow>
      (case x of Itop \<Rightarrow> False | Idown b \<Rightarrow> b \<sqsubseteq> a))"

instance ..
end

lemma maximal_down [iff]: "z \<sqsubseteq> Itop"
by (simp add: below_down_def)

lemma not_Idown_above [iff]: "Itop \<notsqsubseteq> Idown x "
by (simp add: below_down_def)

lemma Idown_below [iff]: "(Idown x \<sqsubseteq> Idown y) = (x \<sqsubseteq> y)"
by (simp add: below_down_def)

subsection {* Lifted cpo is a partial order *}

instance d :: (cpo) po
proof
  fix x :: "'a d"
  show "x \<sqsubseteq> x"
    unfolding below_down_def by (simp split: d.split)
next
  fix x y :: "'a d"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding below_down_def
    by (auto split: d.split_asm intro: below_antisym)
next
  fix x y z :: "'a d"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding below_down_def
    by (auto split: d.split_asm intro: below_trans)
qed

subsection {* Lifted cpo is a cpo *}

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (\<lambda>i. Idown (S i)) <<| Idown x"
unfolding is_lub_def is_ub_def ball_simps
by (auto simp add: below_down_def split: d.split)

lemma down_chain_lemma:
  assumes Y: "chain Y" obtains
    i where "Y i = Itop"
  | A where "\<forall>i. Idown (A i) = Y i" and "chain A" and "range Y <<| Idown (\<Squnion>i. A i)"
proof (cases "\<forall>k. Y k \<noteq> Itop")
  case True
  def A \<equiv> "\<lambda>i. THE a. Idown a = Y i"
  have Idown_A: "\<forall>i. Idown (A i) = Y i"
  proof
    fix i :: nat
    have "Y i \<noteq> Itop" using True by (auto)
    thus "Idown (A i) = Y i"
      by (cases "Y i", simp_all add: A_def)
  qed
  from Y have chain_A: "chain A"
    unfolding chain_def Idown_below [symmetric]
    by (simp add: Idown_A)
  hence "range A <<| (\<Squnion>i. A i)"
    by (rule cpo_lubI)
  hence "range (\<lambda>i. Idown (A i)) <<| Idown (\<Squnion>i. A i)"
    by (rule is_lub_Iup)
  hence "range (\<lambda>i. Y i) <<| Idown (\<Squnion>i. A i)"
    by (simp only: Idown_A)
  with Idown_A chain_A show ?thesis ..
next
  case False
  then obtain i where "Y i = Itop" by auto
  then show ?thesis ..
qed

lemma is_lub_maximal_Itop: "Y i = Itop \<Longrightarrow> range Y <<| Itop"
    by (metis  is_lub_maximal is_ubI  maximal_down rangeI)

instance d :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a d"
  assume S: "chain S"
  thus "\<exists>x. range (\<lambda>i. S i) <<| x"
  proof (rule down_chain_lemma)
    fix i
    assume "S i = Itop"
    hence "range (\<lambda>i. S i) <<| Itop"
      by (rule is_lub_maximal_Itop)
    thus ?thesis ..
  next
    fix A :: "nat \<Rightarrow> 'a"
    assume "range S <<| Idown (\<Squnion>i. A i)"
    thus ?thesis ..
  qed
qed


subsection {* Lifted cpo is pointed *}

instance d :: (cpo) Top_cpo
by intro_classes fast

text {* for compatibility with old HOLCF-Version *}
lemma inst_down_Top_cpo: "\<top> = Itop"
by (rule maximal_down [THEN topI, symmetric])

subsection {* Continuity of \emph{Idown} and \emph{Ifdown} *}

text {* continuity for @{term Idown} *}

lemma cont_Idown: "cont Idown"
apply (rule contI)
apply (rule is_lub_Iup)
apply (erule cpo_lubI)
done

text {* continuity for @{term Ifdown} *}

lemma cont_Ifdown1: "cont (\<lambda>f. Ifdown f x)"
by (induct x, simp_all)

lemma monofun_Ifdown2: "monofun (\<lambda>x. Ifdown f x)"
apply (rule monofunI)
apply (case_tac y, simp)
apply (case_tac x, simp)
apply (simp add: monofun_cfun_arg)
done

lemma cont_Ifdown2: "cont (\<lambda>x. Ifdown f x)"
proof (rule contI2)
  fix Y assume Y: "chain Y" and Y': "chain (\<lambda>i. Ifdown f (Y i))"
  from Y show "Ifdown f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Ifdown f (Y i))"
  proof (rule down_chain_lemma)
    fix A
    assume A: "\<forall>i. Idown (A i) = Y i"
    assume "chain A" and "range Y <<| Idown (\<Squnion>i. A i)"
    hence "Ifdown f (\<Squnion>i. Y i) = (\<Squnion>i. Ifdown f (Idown (A i)))"
      by (simp add: lub_eqI contlub_cfun_arg)
    also have "\<dots> = (\<Squnion>i. Ifdown f (Y i))"
      by (simp add: A)
    finally show ?thesis by simp
  next
    fix i
    assume "Y i = Itop"
    hence "range Y <<| Itop"
      by (rule is_lub_maximal_Itop)
    hence "(\<Squnion>i. Y i) = Itop"
      by (metis lub_eqI)
    moreover
    assume "Y i = Itop"
    hence "Ifdown f (Y i) = \<top>" by simp
    hence "range (\<lambda>i. Ifdown f (Y i)) <<| \<top>"
      by (metis (mono_tags) Y' above_top_iff cpo_class.thelubE is_ub_thelub)
    hence "(\<Squnion>i. Ifdown f (Y i)) = \<top>"
      by (metis lub_eqI)
    ultimately
    show ?thesis by simp
  qed
qed (rule monofun_Ifdown2)

subsection {* Continuous versions of constants *}

definition
  down  :: "'a \<rightarrow> 'a d" where
  "down = (\<Lambda> x. Idown x)"

definition
  fdown :: "('a \<rightarrow> 'b::Top_cpo) \<rightarrow> 'a d \<rightarrow> 'b" where
  "fdown = (\<Lambda> f p. Ifdown f p)"

translations
  "case l of XCONST down\<cdot>x \<Rightarrow> t" == "CONST fdown\<cdot>(\<Lambda> x. t)\<cdot>l"
  "case l of (XCONST down :: 'a)\<cdot>x \<Rightarrow> t" => "CONST fdown\<cdot>(\<Lambda> x. t)\<cdot>l"
  "\<Lambda>(XCONST down\<cdot>x). t" == "CONST fdown\<cdot>(\<Lambda> x. t)"

text {* continuous versions of lemmas for @{typ "('a)d"} *}

lemma Exh_Down: "z = \<top> \<or> (\<exists>x. z = down\<cdot>x)"
apply (induct z)
apply (simp add: inst_down_Top_cpo)
apply (simp add: down_def cont_Idown)
done

lemma down_eq [simp]: "(down\<cdot>x = down\<cdot>y) = (x = y)"
by (simp add: down_def cont_Idown)

lemma down_inject: "down\<cdot>x = down\<cdot>y \<Longrightarrow> x = y"
by simp

lemma down_defined [simp]: "down\<cdot>x \<noteq> \<top>"
by (simp add: down_def cont_Idown inst_down_Top_cpo)

lemma not_down_less_UU: "\<top> \<notsqsubseteq> down\<cdot>x "
by simp (* FIXME: remove? *)

lemma down_above [simp]: "down\<cdot>x \<sqsubseteq> down\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
by (simp add: down_def cont_Idown)

lemma downE [case_names top down, cases type: d]:
  "\<lbrakk>p = \<top> \<Longrightarrow> Q; \<And>x. p = down\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp add: inst_down_Top_cpo)
apply (simp add: down_def cont_Idown)
done

lemma down_induct [case_names top down, induct type: d]:
  "\<lbrakk>P \<top>; \<And>x. P (down\<cdot>x)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

(*
text {* lifting preserves chain-finiteness *}

lemma up_chain_cases:
  assumes Y: "chain Y" obtains "\<forall>i. Y i = \<bottom>"
  | A k where "\<forall>i. up\<cdot>(A i) = Y (i + k)" and "chain A" and "(\<Squnion>i. Y i) = up\<cdot>(\<Squnion>i. A i)"
apply (rule up_chain_lemma [OF Y])
apply (simp_all add: inst_up_pcpo up_def cont_Iup lub_eqI)
done

lemma compact_up: "compact x \<Longrightarrow> compact (up\<cdot>x)"
apply (rule compactI2)
apply (erule up_chain_cases)
apply simp
apply (drule (1) compactD2, simp)
apply (erule exE)
apply (drule_tac f="up" and x="x" in monofun_cfun_arg)
apply (simp, erule exI)
done

lemma compact_upD: "compact (up\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_cfun2 [where f=up]], simp)

lemma compact_up_iff [simp]: "compact (up\<cdot>x) = compact x"
by (safe elim!: compact_up compact_upD)

instance u :: (chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (rule_tac p="\<Squnion>i. Y i" in upE, simp_all)
done
*)

text {* properties of fup *}

lemma fdown1 [simp]: "fdown\<cdot>f\<cdot>\<top> = \<top>"
by (simp add: fdown_def cont_Ifdown1 cont_Ifdown2 inst_down_Top_cpo cont2cont_LAM)

lemma fdown2 [simp]: "fdown\<cdot>f\<cdot>(down\<cdot>x) = f\<cdot>x"
by (simp add: down_def fdown_def cont_Idown cont_Ifdown1 cont_Ifdown2 cont2cont_LAM)

lemma fdown3 [simp]: "fdown\<cdot>down\<cdot>x = x"
by (cases x, simp_all)

end
