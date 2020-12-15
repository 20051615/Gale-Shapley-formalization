theory ex_4_6
  imports Main
begin
fun elems::"'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x # xs) = {x} \<union> (elems xs)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  hence False by simp
  thus ?case by simp
next
  case (Cons a as)
  thus ?case
  proof cases
    assume "x = a"
    hence "a # as = [] @ x # (as) \<and> x \<notin> elems []" by auto
    thus ?thesis by blast
  next
    assume "x \<noteq> a" and "x \<in> elems (a # as)"
    hence "x \<in> elems as" by simp
    hence "\<exists> ys zs. as = ys @ x # zs \<and> x \<notin> elems ys" using Cons.IH by simp
    then obtain ys zs where p:"as = ys @ x # zs \<and> x \<notin> elems ys" by blast
    hence "x \<notin> elems ys" by blast
    hence "x \<notin> elems (a # ys)" using `x \<noteq> a` by simp
    hence "a # as = (a # ys) @ x # zs \<and> x \<notin> elems (a # ys)" using p by simp
    thus ?thesis by blast
  qed
qed
end