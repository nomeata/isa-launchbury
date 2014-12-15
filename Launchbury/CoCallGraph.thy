theory CoCallGraph
imports Main Vars "HOLCF-Join-Classes"
begin

default_sort type

typedef CoCalls = "{G :: (var \<times> var) set.  sym G}"
  morphisms Rep_CoCall Abs_CoCall
  by (auto intro: exI[where x = "{}"] symI)

setup_lifting type_definition_CoCalls

instantiation CoCalls :: po
begin
lift_definition below_CoCalls :: "CoCalls \<Rightarrow> CoCalls \<Rightarrow> bool" is "op \<subseteq>".
instance
  apply default
  apply ((transfer, auto)+)
  done
end

lift_definition coCallsLub :: "CoCalls set \<Rightarrow> CoCalls" is "\<lambda> S. \<Union> S"
  by (auto intro: symI elim: symE)

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

lemma ccis_lubTransfer[transfer_rule]: "(rel_set pcr_CoCalls  ===> pcr_CoCalls ===> op =) (\<lambda> S x . x = Union S) op <<|"
proof-
  have "\<And> x xa . is_cc_lub x xa \<longleftrightarrow> xa = coCallsLub x" by transfer auto
  hence "is_cc_lub = op <<|"
  apply -
  apply (rule, rule)
  by (metis coCallsLub_is_lub is_lub_unique)
  thus ?thesis using is_cc_lub.transfer by simp
qed

lift_definition coCallsJoin :: "CoCalls \<Rightarrow> CoCalls  \<Rightarrow> CoCalls" is "op \<union>"
    by (rule sym_Un)

lemma ccJoinTransfer[transfer_rule]: "(pcr_CoCalls ===> pcr_CoCalls ===> pcr_CoCalls) op \<union> op \<squnion>"
proof-
  have "op \<squnion> = coCallsJoin"
    apply (rule)
    apply rule
    apply (rule lub_is_join)
    unfolding is_lub_def is_ub_def
    apply transfer
    apply auto
    done
  with coCallsJoin.transfer
  show ?thesis by metis
qed

lift_definition ccEmpty :: "CoCalls" is "{}" by (auto intro: symI)

lemma ccEmpty_below[simp]: "ccEmpty \<sqsubseteq> G"
  by transfer auto

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

lemma cc_lub_below_iff:
  fixes G :: CoCalls
  shows "lub X \<sqsubseteq> G \<longleftrightarrow> (\<forall> G'\<in>X. G' \<sqsubseteq> G)" 
  by transfer auto

lift_definition ccField :: "CoCalls \<Rightarrow> var set" is Field.

term fun_upd
lift_definition inCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<in>_" [1000, 1000, 900] 900)
  is "\<lambda> x y s. (x,y) \<in> s".

abbreviation notInCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<notin>_" [1000, 1000, 900] 900)
  where "x--y\<notin>S \<equiv> \<not> x--y\<in>S"

lemma notInCC_bot[simp]: "x--y\<in>\<bottom> \<longleftrightarrow> False"
  by transfer auto

lemma below_CoCallsI:
   "(\<And> x y. x--y\<in>G \<Longrightarrow> x--y\<in>G') \<Longrightarrow> G \<sqsubseteq> G'"
  by transfer auto

lemma CoCalls_eqI:
   "(\<And> x y. x--y\<in>G \<longleftrightarrow> x--y\<in>G') \<Longrightarrow> G = G'"
  by transfer auto

lemma in_join[simp]:
  "x--y \<in> (G\<squnion>G') \<longleftrightarrow> x--y\<in>G \<or> x--y\<in>G'"
by transfer auto

lemma in_lub[simp]: "x--y\<in>(lub S) \<longleftrightarrow> (\<exists> G\<in>S. x--y\<in>G)"
  by transfer auto

lemma in_CoCallsLubI:
  "x--y\<in>G \<Longrightarrow> G \<in> S \<Longrightarrow> x--y\<in>lub S"
by transfer auto

lift_definition cc_delete :: "var \<Rightarrow> CoCalls \<Rightarrow> CoCalls"
  is "\<lambda> z. Set.filter (\<lambda> (x,y) . x \<noteq> z \<and> y \<noteq> z)"
  by (auto intro!: symI elim: symE)

lemma ccField_cc_delete: "ccField (cc_delete x S) \<subseteq> ccField S - {x}"
  by transfer (auto simp add: Field_def )

lift_definition ccProd :: "var set \<Rightarrow> var set \<Rightarrow> CoCalls"
  is "\<lambda> S1 S2. S1 \<times> S2 \<union> S2 \<times> S1"
  by (auto intro!: symI elim: symE)

lemma ccProd_empty[simp]: "ccProd {} S = \<bottom>" by transfer auto

lemma ccProd_empty'[simp]: "ccProd S {} = \<bottom>" by transfer auto

lemma ccProd_union2[simp]: "ccProd S (S' \<union> S'') = ccProd S S' \<squnion> ccProd S S''"
  by transfer auto

lemma ccProd_Union2[simp]: "ccProd S (\<Union>S') = (\<Squnion> X\<in>S'. ccProd S X)"
  by transfer auto

lemma ccProd_Union2'[simp]: "ccProd S (\<Union> X \<in> S'. f X) = (\<Squnion> X\<in>S'. ccProd S (f X))"
  by transfer auto

lemma in_ccProd[simp]: "x--y\<in>ccProd S S' \<longleftrightarrow> x \<in> S \<and> y \<in> S' \<or> x \<in> S' \<and> y \<in> S"
  by transfer auto

lemma ccProd_union1[simp]: "ccProd (S' \<union> S'') S = ccProd S' S \<squnion> ccProd S'' S"
  by transfer auto

lemma ccProd_insert2: "ccProd S (insert x S') = ccProd S {x} \<squnion> ccProd S S'"
  by transfer auto

lemma ccProd_insert1: "ccProd (insert x S') S = ccProd {x} S \<squnion> ccProd S' S"
  by transfer auto

lemma ccProd_mono1: "S' \<subseteq> S'' \<Longrightarrow> ccProd S' S \<sqsubseteq> ccProd S'' S"
  by transfer auto

lemma ccProd_mono2: "S' \<subseteq> S'' \<Longrightarrow> ccProd S S' \<sqsubseteq> ccProd S S''"
  by transfer auto

lemma ccProd_mono: "S \<subseteq> S' \<Longrightarrow> T \<subseteq> T' \<Longrightarrow> ccProd S T \<sqsubseteq> ccProd S' T'"
  by transfer auto

lemma ccProd_comm: "ccProd S S' = ccProd S' S" by transfer auto

lemma ccProd_belowI:
   "(\<And> x y. x \<in> S \<Longrightarrow> y \<in> S' \<Longrightarrow> x--y\<in>G) \<Longrightarrow> ccProd S S' \<sqsubseteq> G"
  by transfer (auto elim: symE)


lift_definition cc_restr :: "var set \<Rightarrow> CoCalls \<Rightarrow> CoCalls"
  is "\<lambda> S. Set.filter (\<lambda> (x,y) . x \<in> S \<and> y \<in> S)"
  by (auto intro!: symI elim: symE)

lemma elem_cc_restr[simp]: "x--y\<in>(cc_restr S G) \<longleftrightarrow> (x--y\<in>G) \<and> x \<in> S \<and> y \<in> S"
  by transfer auto

lemma ccFieldd_cc_restr: "ccField (cc_restr S G) \<subseteq> ccField G \<inter> S"
  by transfer (auto simp add: Field_def)

lemma cc_restr_empty: "ccField G \<subseteq> -S \<Longrightarrow> cc_restr S G = \<bottom>"
  apply transfer
  apply (auto simp add: Field_def)
  apply (drule DomainI)
  apply (drule (1) set_mp)
  apply simp
  done
  
lemma ccField_nil[simp]: "ccField \<bottom> = {}"
  by transfer auto

lemma cc_restr_noop[simp]: "ccField G \<subseteq> S \<Longrightarrow> cc_restr S G = G"
  by transfer (force simp add: Field_def dest: DomainI RangeI elim: set_mp)

lemma cc_restr_bot[simp]: "cc_restr S \<bottom> = \<bottom>"
  by simp

lemma cont_cc_restr: "cont (cc_restr S)"
  apply (rule contI)
  apply (thin_tac "chain ?x")
  apply transfer
  apply auto
  done

lemmas cont_compose[OF cont_cc_restr, cont2cont, simp]

lemma cc_restr_mono1:
  "S \<subseteq> S' \<Longrightarrow> cc_restr S G \<sqsubseteq> cc_restr S' G" by transfer auto

lemma cc_restr_mono2:
  "G \<sqsubseteq> G' \<Longrightarrow> cc_restr S G \<sqsubseteq> cc_restr S G'" by transfer auto

lemma cc_restr_below_arg:
  "cc_restr S G \<sqsubseteq> G" by transfer auto

lemma cc_restr_lub[simp]:
  "cc_restr S (lub X) = (\<Squnion> G\<in>X. cc_restr S G)" by transfer auto

lemma elem_to_ccField: "x--y\<in>G \<Longrightarrow> x \<in> ccField G \<and> y \<in> ccField G"
  by transfer (auto simp add: Field_def)

lemma cc_restr_intersect: "ccField G \<inter> ((S - S') \<union> (S' - S)) = {} \<Longrightarrow> cc_restr S G = cc_restr S' G"
  by (rule CoCalls_eqI) (auto dest: elem_to_ccField)

lemma cc_restr_cc_restr[simp]: "cc_restr S (cc_restr S' G) = cc_restr (S \<inter> S') G"
  by transfer auto


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

lemma ccNeighbors_join[simp]: "ccNeighbors S (G \<squnion> G') = ccNeighbors S G \<union> ccNeighbors S G'"
  by transfer auto

lemma ccNeighbors_union[simp]: "ccNeighbors (S \<union> S') G = ccNeighbors S G \<union> ccNeighbors S' G"
  by transfer auto

lemma ccNeighbors_ccProd:
  "ccNeighbors S (ccProd S' S'') = (if S \<inter> S' = {} then {} else S'') \<union> (if S \<inter> S'' = {} then {} else S')"
by transfer auto

lemma ccNeighbors_ccSquare: 
  "ccNeighbors S (ccSquare S') = (if S \<inter> S' = {} then {} else S')"
  unfolding ccSquare_def by (auto simp add: ccNeighbors_ccProd)

lemma ccNeighbors_cc_restr[simp]:
  "ccNeighbors S (cc_restr S' G) = ccNeighbors (S \<inter> S') G \<inter> S'"
by transfer auto

lemma ccNeighbors_mono:
  "S \<subseteq> S' \<Longrightarrow> G \<sqsubseteq> G' \<Longrightarrow> ccNeighbors S G \<subseteq> ccNeighbors S' G'"
  by transfer auto

lemmas cont_compose[OF cont_ccProd_ccNeighbors, cont2cont]

instance CoCalls :: Join_cpo
  by default (metis coCallsLub_is_lub)

lift_definition ccManyCalls:: "CoCalls \<Rightarrow> var set" 
  is "\<lambda> G. {y . (y,y) \<in> G}".

lemma ccManyCalls_bot[simp]:
  "ccManyCalls \<bottom> = {}" by transfer simp

lemma ccNeighbors_ccManyCalls[simp]: "x \<in> ccNeighbors {x} G \<longleftrightarrow> x \<in> ccManyCalls G"
  by transfer auto

lemma in_ccManyCalls[simp]:
  "x \<in> ccManyCalls G \<longleftrightarrow> x--x\<in>G" by transfer auto

inductive list_pairs :: "'a list \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool"
  where "list_pairs xs p \<Longrightarrow> list_pairs (x#xs) p"
      | "y \<in> set xs \<Longrightarrow> list_pairs (x#xs) (x,y)"

lift_definition ccFromList :: "var list \<Rightarrow> CoCalls" is "\<lambda> xs. {(x,y). list_pairs xs (x,y) \<or> list_pairs xs (y,x)}"
  by (auto intro: symI)

lemma ccFromList_Nil[simp]: "ccFromList [] = \<bottom>"
  by transfer (auto elim: list_pairs.cases)

lemma ccFromList_Cons[simp]: "ccFromList (x#xs) = ccProd {x} (set xs) \<squnion> ccFromList xs"
  by transfer (auto elim: list_pairs.cases intro: list_pairs.intros)

lemma ccFromList_append[simp]: "ccFromList (xs@ys) = ccFromList xs \<squnion> ccFromList ys \<squnion> ccProd (set xs) (set ys)"
  by (induction xs) (auto simp add: ccProd_insert1[where S' = "set xs" for xs])

definition ccLinear :: "var set \<Rightarrow> CoCalls \<Rightarrow> bool"
  where "ccLinear S G = (\<forall> x\<in>S. \<forall> y\<in>S. x--y\<notin>G)"

lemma ccLinear_bottom[simp]:
  "ccLinear S \<bottom>"
  unfolding ccLinear_def by simp

lemma ccLinear_empty[simp]:
  "ccLinear {} G"
  unfolding ccLinear_def by simp

lemma ccLinear_lub[simp]:
  "ccLinear S (lub X) = (\<forall> G\<in>X. ccLinear S G)"
 unfolding ccLinear_def by auto

lemma ccLinear_ccNeighbors:
  "ccLinear S G \<Longrightarrow> ccNeighbors S G \<inter> S = {}"
 unfolding ccLinear_def by transfer auto

lemma ccLinear_cc_restr[intro]:
  "ccLinear S G \<Longrightarrow> ccLinear S (cc_restr S' G)"
 unfolding ccLinear_def by transfer auto

(* TODO: Sort *)

lemma ccLinear_join[simp]:
  "ccLinear S (G \<squnion> G') \<longleftrightarrow> ccLinear S G \<and> ccLinear S G'"
  unfolding ccLinear_def
  by transfer auto

lemma ccLinear_ccProd[simp]:
  "ccLinear S (ccProd S\<^sub>1 S\<^sub>2) \<longleftrightarrow> S\<^sub>1 \<inter> S = {} \<or> S\<^sub>2 \<inter> S = {}"
  unfolding ccLinear_def
  by transfer auto

lemma ccLinear_mono1: "ccLinear S' G \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> ccLinear S G"
  unfolding ccLinear_def
  by transfer auto

lemma ccLinear_mono2: "ccLinear S G' \<Longrightarrow> G \<sqsubseteq> G' \<Longrightarrow> ccLinear S G"
  unfolding ccLinear_def
  by transfer auto

lemma ccField_join[simp]:
  "ccField (G \<squnion> G') = ccField G \<union> ccField G'" by transfer auto

lemma ccField_ccProd:
  "ccField (ccProd S S') = (if S = {} then {} else if S' = {} then {} else  S \<union> S')"
  by transfer (auto simp add: Field_def)

lemma cc_restr_join[simp]:
  "cc_restr S (G \<squnion> G') = cc_restr S G \<squnion> cc_restr S G'"
by transfer auto

lemma cc_restr_ccProd[simp]:
  "cc_restr S (ccProd S\<^sub>1 S\<^sub>2) = ccProd (S\<^sub>1 \<inter> S) (S\<^sub>2 \<inter> S)"
  by transfer auto


end
