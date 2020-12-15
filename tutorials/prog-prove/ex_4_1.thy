theory ex_4_1
  imports Main
begin
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
  from T have "T x y \<or> T y x" by auto
  thus "T x y"
  proof
    show "T x y \<Longrightarrow> T x y" .
  next
    assume "T y x"
    with TA have "A y x" by auto
    with A `A x y` have "x = y" by auto
    with `T y x` show ?thesis by simp
  qed
qed
end