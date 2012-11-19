theory CorrectnessStacked
  imports "Denotational-Props" LaunchburyStacked
begin

lemma compatible_fmap_expand:
  assumes "\<And> x. x \<in> fdom \<rho>1 \<Longrightarrow> x \<in> fdom \<rho>2 \<Longrightarrow> compatible (the (lookup \<rho>1 x)) (the (lookup \<rho>2 x))"
  shows "compatible (fmap_expand \<rho>1 S) (fmap_expand \<rho>2 S)"
  apply (case_tac "finite S")
  apply (rule compatible_fmap_is_compatible[OF compatible_fmapI])
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto simp add: assms fmap_expand_nonfinite)
  done

lemma fmap_restr_le:
  assumes "\<rho>1 \<le> \<rho>2"
  shows "fmap_restr S \<rho>1 \<le> fmap_restr S \<rho>2"
proof(cases "finite S")
case True[simp]
  show ?thesis
  proof (rule fmap_less_eqI)
    have "fdom \<rho>1 \<subseteq> fdom \<rho>2"
      by (metis assms less_eq_fmap_def)
    thus "fdom (fmap_restr S \<rho>1) \<subseteq> fdom (fmap_restr S \<rho>2)"
      by auto
  next
    fix x
    assume "x \<in> fdom (fmap_restr S \<rho>1) "
    hence [simp]:"x \<in> fdom \<rho>1" and [simp]:"x \<in> S" by auto
    have "the (lookup \<rho>1 x) = the (lookup \<rho>2 x)"
      by (metis `x \<in> fdom \<rho>1` assms less_eq_fmap_def)
    thus "the (lookup (fmap_restr S \<rho>1) x) = the (lookup (fmap_restr S \<rho>2) x)"
      by simp
  qed
next
case False
  thus ?thesis
    by (simp add: fmap_restr_not_finite)
qed

theorem correctness:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<lbrace>\<Gamma>'@\<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>'@\<Delta>\<rbrace>fempty"
  using assms
proof(induct rule:reds_distinct_ind)
print_cases
case (Lambda x y e \<Gamma> \<Gamma>')
  show ?case by simp
next

case (Application n \<Gamma> \<Gamma>' x e y \<Theta> \<Theta>' z e' \<Delta>' \<Delta>)
  let "?restr \<rho>" = "fmap_restr (insert x (heapVars \<Gamma>') \<union> (heapVars \<Gamma>)) (\<rho>::Env)"

  have "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> ?restr (\<lbrace>((n, e) # (x, App (Var n) y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty)"
    (* Adding a fresh variable and stubstituting it *)
    sorry
  also
  have "... \<le> ?restr  (\<lbrace>((n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>') @ \<Delta>\<rbrace>fempty)"
    (* Restriction and \<le> *)
    by (rule fmap_restr_le[OF Application.hyps(9)])
  also
  have "... \<le>  \<lbrace>((x, e'[z::=y]) # \<Delta>') @ \<Delta>\<rbrace>fempty"
    (* Substituting a fresh variable, denotation of application *)
    sorry
  also
  have "... \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>fempty" by fact
  finally
  show "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>fempty".

next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>((y, e) # (x, Var y) # \<Gamma>') @ removeAll (y, e) \<Gamma>\<rbrace>fempty"
    (* Shifting a variable around *)
    sorry
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>fempty"
    by fact
  also
  have "... \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>fempty"
    (* Substituting a variable indirection, moving stuff around *)
    sorry
  finally
  show "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>fempty".

next
case (Let as \<Gamma> x body \<Gamma>' \<Delta>' \<Delta>)
  have "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>\<rbrace>fempty"
    (* Unrolling a let *)
    sorry
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>fempty"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>fempty".
qed

end

