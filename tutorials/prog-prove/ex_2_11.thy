theory ex_2_11
  imports Main
begin
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval::"exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add exp1 exp2) x = (eval exp1 x) + (eval exp2 x)" |
"eval (Mult exp1 exp2) x = (eval exp1 x) * (eval exp2 x)"

fun evalp::"int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0" |
"evalp (c # cs) x = c + x * (evalp cs x)"

fun addp::"int list \<Rightarrow> int list \<Rightarrow> int list" where
"addp [] ys = ys" |
"addp xs [] = xs" |
"addp (x # xs) (y # ys) = (x + y) # (addp xs ys)"

lemma addp: "evalp (addp p1 p2) x = evalp p1 x + evalp p2 x"
  apply (induction p1 p2 rule:addp.induct)
  by (auto simp add:algebra_simps)

fun multp::"int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] ys = []" |
"multp xs [] = []" |
"multp [c] (y # ys) = c * y # (multp [c] ys)" |
"multp (x # xs) ys = addp (multp [x] ys) (multp xs (0 # ys))"

lemma multp: "evalp (multp p1 p2) x = evalp p1 x * evalp p2 x"
  apply (induction p1 p2 rule:multp.induct)
  by (auto simp add:addp algebra_simps)

fun coeffs::"exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add exp1 exp2) = addp (coeffs exp1) (coeffs exp2)" |
"coeffs (Mult exp1 exp2) = multp (coeffs exp1) (coeffs exp2)"

theorem coeffs: "evalp (coeffs e) x = eval e x"
  apply (induction e)
  by (auto simp add:addp multp)

end