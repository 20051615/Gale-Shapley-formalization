theory ex_2_2
  imports Main
begin
fun add::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 m = m" | 
"add (Suc n) m = Suc (add n m)"

theorem add_assoc: "add x (add y z) = add (add x y) z"
  apply (induction x)
  by (auto)

lemma add_suc_r[simp]: "add n (Suc m) = Suc (add n m)"
  apply (induction n)
  by (auto)

lemma add_id_r[simp]: "add y 0 = y"
  apply (induction y)
  by (auto)

theorem add_comm: "add x y = add y x"
  apply (induction x)
  by (auto)

fun double::"nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc(Suc(double n))"

theorem double_add: "double m = add m m"
  apply (induction m)
  by (auto)
end