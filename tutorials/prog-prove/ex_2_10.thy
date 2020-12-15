theory ex_2_10
  imports Main
begin
datatype tree0 = Tip | Node tree0 tree0

fun nodes::"tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"
fun explode::"nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma explode_size_ind: "nodes(explode (Suc n) t) = Suc(2 * nodes(explode n t))"
  apply(induction n arbitrary:t)
  by(auto)
lemma inv_Suc:"Suc y = k \<Longrightarrow> y = k - 1"
  by(auto)

theorem explode_size[simp]: "nodes(explode n t) = 2 ^ n * Suc(nodes t) - 1"
  apply(rule inv_Suc)
  apply(induction n)
  apply(simp)
  by(auto simp add: explode_size_ind simp del:explode.simps)
end