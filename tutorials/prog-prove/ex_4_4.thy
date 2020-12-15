theory ex_4_4
  imports Main
begin
inductive ev::"nat\<Rightarrow>bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  thus False
  proof cases
    assume "ev (Suc 0)"
    thus False by cases
  qed
qed
end