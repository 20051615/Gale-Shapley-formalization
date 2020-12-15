theory ex_2_4
  imports Main
begin
fun snoc::"'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y#ys) x = y # (snoc ys x)"

fun reverse::"'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma rev_snoc[simp]: "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
  by (auto)

theorem rev_rev[simp]:"reverse (reverse xs) = xs"
  apply (induction xs)
  by (auto)
end