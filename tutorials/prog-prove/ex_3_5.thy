theory ex_3_5
  imports Main
begin
datatype alpha = a | b
inductive S::"alpha list \<Rightarrow> bool" where
"S []" |
"S w \<Longrightarrow> S (a # w @ [b])" |
"\<lbrakk>S x; S y\<rbrakk> \<Longrightarrow> S (x @ y)"
inductive T::"alpha list \<Rightarrow> bool" where
"T []" |
"\<lbrakk>T x; T y\<rbrakk> \<Longrightarrow> T (x @ a # y @ [b])"

theorem S_T: "S w = T w"
proof
  show "S w \<Longrightarrow> T w"
  proof (induction rule:S.induct)
    show "T []" using T.intros(1) .
  next
    fix w assume IH:"T w"
    have "T []" using T.intros(1) .
    with IH T.intros(2) have "T ([] @ a # w @ [b])" by blast
    thus "T (a # w @ [b])" by simp
  next
    fix x y
    assume IH:"T x" "T y"
    have "\<lbrakk>T y; T x\<rbrakk> \<Longrightarrow> T (x @ y)"
    proof (induction rule:T.induct)
      case 1
      with T.intros show ?case by simp
    next
      case 2
      with T.intros(2) show ?case by fastforce
    qed
    thus "T (x @ y)" using IH by simp
  qed
next
  show "T w \<Longrightarrow> S w"
    apply (induction rule: T.induct)
    by (auto intro:S.intros)
qed
end