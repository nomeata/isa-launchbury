(*<*)
theory EverythingAdequacy
imports CorrectnessOriginal Adequacy "~~/src/HOL/Library/LaTeXsugar" 
begin

(*
notation (latex output) DenotationalUpd.ESem ("\<lbrakk>_\<rbrakk>\<^bsup>u\<^esup>\<^bsub>_\<^esub>"  [60,60] 60)
notation (latex output) "Denotational-PropsUpd.HSem_syn" ("\<lbrace>_\<rbrace>\<^bsup>u\<^esup>_"  [60,60] 60)
*)

translations
  "xs" <= "CONST set xs"
translations
  "xs" <= "CONST asToHeap xs"
translations
  "a" <= "CONST atom a"

abbreviation map_of_syntax :: "'a::type \<Rightarrow> 'b::type \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" ("'(_, _') \<in> _") 
  where "map_of_syntax x e \<Gamma> \<equiv> map_of \<Gamma> x = Some e"

abbreviation delete_syntax :: "heap \<Rightarrow> var \<Rightarrow> heap" ("_\\_") 
  where "delete_syntax \<Gamma> x \<equiv> delete x \<Gamma>"

notation (latex output) domA ("\<^raw:\textrm{\textsf{dom}}> _")
notation (latex output) bn ("\<^raw:\textrm{\textsf{dom}}> _")

declare [[names_short]]
declare [[show_question_marks = false]]


(*>*)
subsection {* Main definitions and theorems *}

text {*
For your convenience, the main definitions and theorems of the present work are assembled in this section. The following 
formulas are mechanically pretty-printed versions of the statements as defined resp.\ proven in Isabelle.
Free variables are all-quantified. Some type conversion functions (like @{term_type set}) are omitted.
The relations @{text \<sharp>} and @{text "\<sharp>*"} come from the Nominal package and express freshness of the
variables on the left with regard to the expressions on the right.

\input{map.tex}
*}

subsubsection {* Expressions *}

text {*
The type @{typ var} of variables is abstract and provided by the Nominal package. All we know about
it is that it is countably infinite.
Expressions of type @{typ exp} are given by the following grammar:
\begin{alignatstar}{2}
@{term e} \Coloneqq {}& @{term "Lam [x]. e"} &\quad& \text{lambda abstraction}\\
\mid {} & @{term "App e x"} && \text{application}\\
\mid {} & @{term "Var x"} && \text{variable} \\
\mid {} & @{term "Let as e"} && \text{recursive let}
\end{alignatstar}
In the introduction we pretty-print expressions to match the notation in \cite{launchbury} and omit
the constructor names @{term Var}, @{term App}, @{text Lam} and @{term Let}. In the actual theories, these are visible.
These expressions are, due to the machinery of the Nominal package, actually alpha-equivalency classes, so @{thm alpha_test} holds provably. This differs from Launchbury's original definition, which expects distinctly-named expressions and performs explicit alpha-renaming in the semantics.

The type @{type heap} is an abbreviation for @{typ "(var \<times> exp) list"}. These are \emph{not} alpha-equivalency classes, i.e.\ we manage the bindings in heaps explicitly.
*}

subsubsection {* The natural semantics *}

text_raw {*
\newlength{\rulelen}
\setlength{\rulelen}{\linewidth}
\newlength{\rulenamelen}
\settowidth{\rulenamelen}{~{\sc Application}}
\addtolength{\rulelen}{-\rulenamelen}
*}

text {*
Launchbury's original semantics, extended with some technical overhead related to name binding,
is defined as follows:\\
%\begin{center}
\parbox[t]{\rulelen}{\centering@{thm[mode=Axiom] Launchbury.reds.Lambda}}~{\sc Lambda}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Application}}~{\sc Application}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Variable}}~{\sc Variable}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Let[where as = "binds"]}}~{\sc Let}
%\end{center}
*}


subsubsection {* The denotational semantics *}

text {*
The value domain of the denotational semantics is the initial solution to
\[
D = [D \to D]_\bot
\]
as introduced in \cite{abramsky}. The type @{typ Value}, together with the bottom value @{term_type "\<bottom>::Value"}, the
injection @{term_type "Fn"} and the projection @{term "DUMMY \<down>Fn DUMMY"}@{text "::"}@{typeof "Fn_project"},
is constructed as a pointed chain-complete partial order from this equation by the HOLCF package.
The type of semantic environments is  @{typ "var \<Rightarrow> Value"}.

The semantics of an expression @{term_type "e :: exp"} in an environment @{term "\<rho>"}@{text "::"}@{typ "var \<Rightarrow> Value"} is 
written \mbox{@{term_type "Rep_cfun (Denotational.ESem e) \<rho>"}} and defined by the following equations:
\begin{alignstar}
@{thm (lhs) Denotational.ESem_simps(1)} & = @{thm (rhs) Denotational.ESem_simps(1)} \\
@{thm (lhs) Denotational.ESem_simps(2)} & = @{thm (rhs) Denotational.ESem_simps(2)} \\
@{thm (lhs) Denotational.ESem_simps(3)} & = @{thm (rhs) Denotational.ESem_simps(3)} \\
@{thm (lhs) Denotational.ESem_simps(4)} & = @{thm (rhs) Denotational.ESem_simps(4)}.
\end{alignstar}
*}

text{*
The expression @{term "Denotational.EvalHeapSem_syn'' \<Gamma> \<rho>"} lifts
maps the evaluation function over a heap, returning a function of type @{typ "var \<Rightarrow> Value"}:
\begin{alignstar}
@{thm (lhs) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  & = @{thm (rhs) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  && \text{if } @{thm (prem 1) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]} \\
@{thm (lhs) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  & = @{thm (rhs) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  && \text{if } @{thm (prem 1) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
\end{alignstar}
*}

text {*
The semantics @{term "Rep_cfun (Denotational.HSem \<Gamma>) \<rho>"}@{text "::"}@{typ "var \<Rightarrow> Value"} of a
heap @{term "\<Gamma> :: heap"}@{text "::"}@{typ heap}
in an environment @{term "\<rho>"}@{text "::"}@{typ "var \<Rightarrow> Value"} is  defined by the recursive equation
\[ @{thm "Denotational.HSem_eq"} \]
where
\begin{alignstar}
@{thm (lhs) override_on_apply_notin} & = @{thm (rhs) override_on_apply_notin}  && \text{if } @{thm (prem 1) override_on_apply_notin} \\
@{thm (lhs) override_on_apply_in} & = @{thm (rhs) override_on_apply_in}  && \text{if } @{thm (prem 1) override_on_apply_in}.
\end{alignstar}

The semantics of the heap in the empty environment @{term "\<bottom>"} is abbreviated as @{abbrev "Denotational.HSem_fempty \<Gamma>"}.
*}

subsubsection {* Correctness and Adequacy *}
text {* The statement of correctness  reads:
If @{thm (prem 1) CorrectnessOriginal.correctness(1)} and, as a side condition,
@{thm (prem 2) CorrectnessOriginal.correctness(1)} holds,
then
\[
@{thm (concl) CorrectnessOriginal.correctness(1)}.
\]
*}
(*
\]
and
\[
@{thm (concl) CorrectnessOriginal.correctness(2)}.
\]
The latter is phrased slightly different than in \cite{launchbury}, which defines a partial relation
@{text "\<le>"} on heaps, by being more explictit on what set of variables the heaps agree.
*)

text {* The statement of adequacy reads:
\[
\text{If }
@{thm (prem 1) adequacy}\text{ then }@{thm (concl) adequacy}.
\]
*}

(*<*)

end
(*>*)
