theory ex_3_2
  imports Main
begin
inductive palindrome ::"'a list \<Rightarrow> bool" where
"palindrome []" |
"palindrome [a]" |
"palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem palindrome:"palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule:palindrome.induct)
  by (auto)
end