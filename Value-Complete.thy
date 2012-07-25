theory "Value-Complete"
  imports "HOLCF-Join" "Down"
begin

domain Value_ = Fn (lazy "Value_ d \<rightarrow> Value_ d")
type_synonym Value = "Value_ d"

instance Value_ :: Nonempty_Meet_cpo
proof default
  fix S
  assume "(S :: Value_ set) \<noteq> {}"
  show "\<exists> u. S >>| u"
  proof (cases "\<exists> u. S = {u}")
  case True thus ?thesis by (metis is_glb_singleton)
  next
  case False then obtain x1 x2 where "x1 \<in> S" and "x2 \<in> S" and "x1 \<noteq> x2"
    using `S \<noteq> {}` by (metis insertCI nonempty_iff)
  find_theorems name:Value_ name:take

  hence "\<exists> i. Value__take i \<cdot> x1 \<noteq> Value__take i \<cdot> x2"
    by (metis Value_.take_lemma)
  then obtain i where "Value__take i \<cdot> x1 \<noteq> Value__take i \<cdot> x2" by auto
  hence "\<not> (\<exists> u. {Value__take i \<cdot> x | x . x \<in> S } = {u})" (is " \<not> ?P i")
    using `S \<noteq> {}` `x1 \<in> S` `x2 : S`
    apply -
    apply (rule notI)
    apply (erule exE)
    apply (drule equalityD1)
    apply auto
    done
  moreover
  have "\<not> \<not> ?P 0"
    using `S \<noteq> {}` by auto
  ultimately
  have "\<exists>k<i. (\<forall>j\<le>k. \<not> \<not> ?P j) \<and> \<not> ?P (k+1)"
    by -(rule ex_least_nat_less) 
  oops

end
