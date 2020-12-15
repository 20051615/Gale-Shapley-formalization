theory ex_2_9
  imports Main ex_2_2
begin
fun itadd::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 y = y" |
"itadd (Suc x) y = itadd x (Suc y)"

theorem itadd_equiv: "itadd m n = add m n"
  apply (induction m arbitrary:n)
  by (auto)
end