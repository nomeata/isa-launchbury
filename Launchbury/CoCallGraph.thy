theory CoCallGraph
imports Main Vars "HOLCF-Join-Classes"
begin

typedef CoCalls = "UNIV :: (var \<times> var) set set"
  morphisms Rep_CoCall Abs_CoCall
  by auto

setup_lifting type_definition_CoCalls

instantiation CoCalls :: po
begin
lift_definition below_CoCalls :: "CoCalls \<Rightarrow> CoCalls \<Rightarrow> bool" is "op \<subseteq>".
instance
  apply default
  apply ((transfer, auto)+)
  done
end

lift_definition coCallsLub :: "CoCalls set \<Rightarrow> CoCalls" is "\<lambda> S. \<Union> S".

lemma coCallsLub_is_lub: "S <<| coCallsLub S"
proof (rule is_lubI)
  show "S <| coCallsLub S"
    by (rule is_ubI, transfer, auto)
next
  fix u
  assume "S <| u"
  hence "\<forall>x \<in> S. x \<sqsubseteq> u" by (auto dest: is_ubD)
  thus "coCallsLub S \<sqsubseteq> u" by transfer auto
qed

instance CoCalls :: cpo
proof default
  fix S :: "nat \<Rightarrow> CoCalls"
  show "\<exists>x. range S <<| x" using coCallsLub_is_lub..
qed

lemma ccLubTransfer[transfer_rule]: "(rel_set pcr_CoCalls ===> pcr_CoCalls) Union lub"
proof-
  have "lub = coCallsLub"
    apply (rule)
    apply (rule lub_eqI)
    apply (rule coCallsLub_is_lub)
    done
  with coCallsLub.transfer
  show ?thesis by metis
qed

lift_definition is_cc_lub :: "CoCalls set \<Rightarrow> CoCalls \<Rightarrow> bool" is "(\<lambda> S x . x = Union S)".
print_theorems

lemma ccis_lubTransfer[transfer_rule]: "(rel_set pcr_CoCalls  ===> pcr_CoCalls ===> op =) (\<lambda> S x . x = Union S) op <<|"
proof-
  have "is_cc_lub = op <<|"
  apply (rule, rule, rule)
  unfolding is_lub_def is_ub_def
  apply transfer
  apply auto
  unfolding is_lub_def is_ub_def
  apply transfer
  apply blast
  done
  thus ?thesis using is_cc_lub.transfer by simp
qed

lift_definition ccEmpty :: "CoCalls" is "{}".

instance CoCalls :: pcpo
proof default
  have "\<forall>y . ccEmpty \<sqsubseteq> y" by transfer simp
  thus "\<exists>x. \<forall>y. (x::CoCalls) \<sqsubseteq> y"..
qed

lemma ccBotTransfer[transfer_rule]: "pcr_CoCalls {} \<bottom>"
proof-
  have "\<And>x. ccEmpty \<sqsubseteq> x" by transfer simp
  hence "ccEmpty = \<bottom>" by (rule bottomI)
  thus ?thesis using ccEmpty.transfer by simp
qed

lift_definition ccField :: "CoCalls \<Rightarrow> var set" is Field.

lift_definition inCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<in>_")
  is "\<lambda> x y s. (x,y) \<in> s".

abbreviation notInCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<notin>_")
  where "x--y\<notin>S \<equiv> \<not> (x--y\<in>S)"

lemma notInCC_bot[simp]: "(x--y\<in>\<bottom>) \<longleftrightarrow> False"
  by transfer auto

lift_definition cc_delete :: "var \<Rightarrow> CoCalls \<Rightarrow> CoCalls"
  is "\<lambda> z. Set.filter (\<lambda> (x,y) . x \<noteq> z \<and> y \<noteq> z)".

lemma ccField_cc_delete: "ccField (cc_delete x S) \<subseteq> ccField S - {x}"
  by transfer (auto simp add: Field_def )

lift_definition ccProd :: "var set \<Rightarrow> var set \<Rightarrow> CoCalls"
  is "\<lambda> S1 S2. S1 \<times> S2 \<union> S2 \<times> S1".

lemma ccProd_empty[simp]: "ccProd {} S = \<bottom>" by transfer auto

lemma ccProd_empty'[simp]: "ccProd S {} = \<bottom>" by transfer auto


lift_definition cc_restr :: "var set \<Rightarrow> CoCalls \<Rightarrow> CoCalls"
  is "\<lambda> S. Set.filter (\<lambda> (x,y) . x \<in> S \<and> y \<in> S)".

lemma ccFieldd_cc_restr: "ccField (cc_restr S G) \<subseteq> ccField G \<inter> S"
  by transfer (auto simp add: Field_def)

lemma cc_restr_bot[simp]: "cc_restr S \<bottom> = \<bottom>"
  by transfer auto

lemma cont_cc_restr: "cont (cc_restr S)"
  apply (rule contI)
  apply (thin_tac "chain ?x")
  apply transfer
  apply auto
  done

lemmas cont_compose[OF cont_cc_restr, cont2cont, simp]

definition ccSquare where "ccSquare S = ccProd S S"

lemma ccField_ccSquare[simp]: "ccField (ccSquare S) = S"
  unfolding ccSquare_def by transfer (auto simp add: Field_def)
  
lemma below_ccSquare[iff]: "G \<sqsubseteq> ccSquare S  \<longleftrightarrow> ccField G \<subseteq> S"
  unfolding ccSquare_def by transfer (auto simp add: Field_def)

lift_definition ccNeighbors :: "var set \<Rightarrow> CoCalls \<Rightarrow> var set" 
  is "\<lambda> S G. {y . \<exists> x \<in> S. (y,x) \<in> G \<or> (x,y) \<in> G}".

lemma ccNeighbors_bot[simp]: "ccNeighbors S \<bottom> = {}" by transfer auto

lemma cont_ccProd_ccNeighbors:
  "cont (\<lambda>x. ccProd S (ccNeighbors S' x))"
  apply (rule contI)
  apply (thin_tac "chain ?x")
  apply transfer
  apply auto
  done

lemmas cont_compose[OF cont_ccProd_ccNeighbors, cont2cont]

instance CoCalls :: Finite_Join_cpo
proof default
  fix x y :: CoCalls
  show "compatible x y"
    unfolding compatible_def
    apply (rule exI)
    apply (rule coCallsLub_is_lub)
    done
qed

end
