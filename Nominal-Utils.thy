theory "Nominal-Utils"
imports "Nominal/Nominal/Nominal2"
begin

lemma image_eqvt[eqvt]: "\<pi> \<bullet> (f ` S) = (\<pi> \<bullet> f) ` (\<pi> \<bullet> S)"
  unfolding permute_set_def permute_fun_def
  by (auto simp add: image_def)

lemma range_eqvt: "\<pi> \<bullet> range Y = range (\<pi> \<bullet> Y)"
  unfolding image_eqvt UNIV_eqvt ..

lemma option_case_eqvt[eqvt]:
  "\<pi> \<bullet> option_case d f x = option_case (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  by(cases x, auto simp add: permute_fun_def)

lemma fresh_star_singleton: "{ x } \<sharp>* e \<longleftrightarrow> x \<sharp> e"
  by (simp add: fresh_star_def)

end
