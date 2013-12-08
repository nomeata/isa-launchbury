theory "HOLCF-Utils"
  imports HOLCF Pointwise
begin

default_sort type

lemmas cont_fun[simp]
lemmas cont2cont_fun[simp]

lemma cont_compose2:
  assumes "cont c"
  assumes "\<And> x. cont (c x)"
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda>x. c (f x) (g x))"
proof-
  have "monofun (\<lambda>x. c (f x) (g x))"
    apply (rule monofunI)
    apply (rule below_trans[OF cont2monofunE[OF assms(2) cont2monofunE[OF `cont g`]]], assumption)
    apply (rule fun_belowD[OF cont2monofunE[OF `cont c` cont2monofunE[OF `cont f`]]], assumption)
    done
  thus ?thesis
    apply (rule contI2)
    apply (subst cont2contlubE[OF `cont f`], assumption)
    apply (subst cont2contlubE[OF `cont g`], assumption)
    apply (subst cont2contlubE[OF `cont c` ch2ch_cont[OF `cont f`]], assumption)
    apply (subst lub_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (subst cont2contlubE[OF assms(2)ch2ch_cont[OF `cont g`]], assumption)
    apply (subst diag_lub)
    apply (rule ch2ch_fun[OF ch2ch_cont[OF `cont c` ch2ch_cont[OF `cont f`]]], assumption)
    apply (rule ch2ch_cont[OF assms(2) ch2ch_cont[OF `cont g`]], assumption)
    apply (rule below_refl)
    done
qed

lemma pointwise_adm:
  fixes P :: "'a::pcpo \<Rightarrow> 'b::pcpo \<Rightarrow> bool"
  assumes "adm (\<lambda> x. P (fst x) (snd x))"
  shows "adm (\<lambda> m. pointwise P (fst m) (snd m))"
proof (rule admI)
  case (goal1 Y)
    show ?case
    apply (rule pointwiseI)
    apply (rule admD[OF adm_subst[where t = "\<lambda>p . (fst p x, snd p x)", standard, OF _ assms, simplified] `chain Y`])
    using goal1(2) unfolding pointwise_def by auto
qed 


end
