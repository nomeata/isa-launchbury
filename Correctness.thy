theory Correctness
  imports "CorrectnessStacked" "Launchbury-Unstack"
begin


theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z"
  and [simp]:"distinctVars \<Gamma>"
  and fresh: "atom x \<sharp> (\<Gamma>,e)"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>fempty\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>fempty\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>\<rbrace>fempty"
proof-

  have "\<Gamma> : [(x, e)] \<Down> \<Delta> : [(x, z)]"
    by (rule add_stack[OF assms(1)], simp_all add: supp_Nil)
  moreover
  from `atom x \<sharp> (\<Gamma>,e)`
  have "x \<notin> heapVars \<Gamma>"
    by (metis heapVars_not_fresh fresh_Pair)
  hence "distinctVars ([(x, e)] @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  ultimately
  have le: "\<lbrace>[(x, e)] @ \<Gamma>\<rbrace>fempty \<le> \<lbrace>[(x, z)] @ \<Delta>\<rbrace>fempty"
    by (rule CorrectnessStacked.correctness)
 
  have "atom x \<sharp> (\<Delta>, z)"
    using reds_fresh[OF assms(1) fresh]
    by auto

  have "\<lbrace>\<Gamma>\<rbrace>fempty = fmap_restr (fst ` set \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>fempty)"
    apply (rule HSem_add_fresh[of fempty, simplified (no_asm), unfolded heapVars_def, symmetric])
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    using fresh apply (simp add: fresh_Pair)
    done
  also have "... \<le> fmap_restr (fst ` set \<Delta>) (\<lbrace>(x, z) # \<Delta>\<rbrace>fempty)"
    by (rule fmap_restr_le[OF le reds_doesnt_forget[unfolded heapVars_def, OF assms(1)], simplified])
  also have "... = \<lbrace>\<Delta>\<rbrace>fempty"
    apply (rule HSem_add_fresh[of fempty, simplified (no_asm), unfolded heapVars_def])
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    using `_ \<sharp> (\<Delta>,z)` apply (simp add: fresh_Pair)
    done
  finally show "\<lbrace>\<Gamma>\<rbrace>fempty \<le> \<lbrace>\<Delta>\<rbrace>fempty".
 

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>fempty\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e) # \<Gamma>\<rbrace>fempty\<^esub>"
    apply (rule ESem_add_fresh[symmetric])
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    using fresh by (simp add: fresh_Pair)
  also have "... = the (lookup (\<lbrace>(x, e) # \<Gamma>\<rbrace>fempty) x)"
    apply (rule the_lookup_HSem_heap[of _ "(x, e) # \<Gamma>" x, simplified (no_asm), symmetric])
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply simp_all    
    done
  also have "... = the (lookup (\<lbrace>(x, z) # \<Delta>\<rbrace>fempty) x)"
    apply (rule arg_cong[OF fmap_less_eqD[OF le, simplified]])
    apply simp
    done
  also have "... = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>fempty\<^esub>"
    apply (rule the_lookup_HSem_heap[of _ "(x, z) # \<Delta>" x, simplified (no_asm)])
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply simp_all    
    done
  also have "... =  \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>fempty\<^esub>"
    apply (rule ESem_add_fresh)
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    apply (rule fempty_is_heapExtendJoin_cond'_ESem)
    using `atom x \<sharp> (\<Delta>,z)` by (simp add: fresh_Pair)
  finally show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>fempty\<^esub> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>fempty\<^esub>".
qed

end

