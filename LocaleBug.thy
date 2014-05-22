theory LocaleBug
imports Nominal2
begin

consts foo :: "bool => int => int"

locale foo =
fixes param :: bool
begin
lemma [eqvt]: "p \<bullet> (foo param x) = (foo param (p \<bullet> x))" sorry
end

interpretation foo True
done
end
