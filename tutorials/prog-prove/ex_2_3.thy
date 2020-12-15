theory ex_2_3
imports Main
begin
fun count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # ys) = (if x = y then 1 else 0) + (count x ys)"

theorem count_bound:"count x xs \<le> length xs"
  apply (induction xs)
  by (auto)
end