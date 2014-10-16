theory CoCallGraph
imports Main Vars HOLCF
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

lift_definition ccField :: "CoCalls \<Rightarrow> var set" is Field.

lift_definition inCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<in>_")
  is "\<lambda> x y s. (x,y) \<in> s".

abbreviation notInCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<notin>_")
  where "x--y\<notin>S \<equiv> \<not> (x--y\<in>S)"

lift_definition cc_delete :: "var \<Rightarrow> CoCalls \<Rightarrow> CoCalls"
  is "\<lambda> z. Set.filter (\<lambda> (x,y) . x \<noteq> z \<and> y \<noteq> z)".

lemma ccField_cc_delete: "ccField (cc_delete x S) \<subseteq> ccField S - {x}"
  by transfer (auto simp add: Field_def )

lift_definition ccProd :: "var set \<Rightarrow> var set \<Rightarrow> CoCalls"
  is "\<lambda> S1 S2. S1 \<times> S2 \<union> S2 \<times> S1".

definition ccSquare where "ccSquare S = ccProd S S"

end
