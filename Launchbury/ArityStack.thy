theory ArityStack
imports "Arity" SestoftConf
begin

fun Astack :: "stack \<Rightarrow> Arity"
  where "Astack [] = 0"
      | "Astack (Arg x # S) = inc\<cdot>(Astack S)"
      | "Astack (Alts e1 e2 # S) = 0"
      | "Astack (Upd x # S) = 0"
      | "Astack (Dummy x # S) = 0"

lemma Astack_restr_stack_below:
  "Astack (restr_stack V S) \<sqsubseteq> Astack S"
  by (induction V S rule: restr_stack.induct) auto


end
