theory ex_3_3
  imports Main
begin
inductive star:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "\<lbrakk>r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z"

lemma star_trans: "\<lbrakk>star r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (assumption)
  by (metis step)

lemma r_star: "r x y \<Longrightarrow> star r x y"
  by (metis star.intros)

inductive star':: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "\<lbrakk>star' r x y; r y z\<rbrakk> \<Longrightarrow> star' r x z"

lemma star'_trans: "\<lbrakk>star' r y z; star' r x y\<rbrakk> \<Longrightarrow> star' r x z"
  apply (induction rule:star'.induct)
   apply (assumption)
  by (metis step')

lemma r_star': "r x y \<Longrightarrow> star' r x y"
  by (metis star'.intros)

theorem "star r x y = star' r x y"
  apply (rule)
  apply (induction rule:star.induct)
   apply (metis refl')
   apply (metis star'_trans r_star')
  apply (induction rule:star'.induct)
   apply (metis refl)
   apply (metis star_trans r_star)
  done
  
end