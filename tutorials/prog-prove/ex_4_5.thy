theory ex_4_5
  imports Main
begin
inductive iter::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "iter r 0 x x" |
step: "\<lbrakk>r x y; iter r n y z\<rbrakk> \<Longrightarrow> iter r (Suc n) x z"

inductive star:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "\<lbrakk>r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  fix x
  show "star r x x" using star.refl .
next
  fix x y z
  assume IH: "star r y z"
         and "r x y"
  thus "star r x z" using star.step by fastforce
qed

end