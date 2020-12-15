theory ex_2_5
  imports Main
begin
fun sum_upto::"nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = sum_upto n + (Suc n)"

theorem sum_upto[simp]:"sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  by (auto)
end