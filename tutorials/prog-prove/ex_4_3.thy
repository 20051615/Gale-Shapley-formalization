theory ex_4_3
  imports Main
begin
inductive ev::"nat\<Rightarrow>bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma assumes "ev(Suc(Suc n))" shows "ev n"
proof -
  from assms show "ev n"
  proof cases
    assume "ev n"
    thus "ev n" .
  qed
qed