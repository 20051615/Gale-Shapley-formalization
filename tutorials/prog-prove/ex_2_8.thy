theory ex_2_8
  imports Main
begin
fun intersperse::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # xs) = x # a # (intersperse a xs)"

theorem map_equiv:"map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction a xs rule: intersperse.induct)
  by (auto)
end