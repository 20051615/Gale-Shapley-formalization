theory ex_3_4
  imports Main ex_3_3
begin
inductive iter::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "iter r 0 x x" |
step: "\<lbrakk>r x y; iter r n y z\<rbrakk> \<Longrightarrow> iter r (Suc n) x z"

theorem star_iter:"star r x y \<Longrightarrow> (\<exists>n. iter r n x y)"
  apply (induction rule: star.induct)
   apply (metis refl)
  by (auto dest:star.step step)
end
