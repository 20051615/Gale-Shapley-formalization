theory ex_2_6
  imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents::"'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a # (contents(l) @ contents(r))"

fun sum_tree::"nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + sum_tree(l) + sum_tree(r)"

theorem contents_equiv:"sum_tree t = sum_list(contents t)"
  apply (induction t)
  by (auto)
end