theory ex_4_2
  imports Main
begin

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  let ?l_zs = "length xs div 2"
  let ?l_ys = "length xs - ?l_zs"
  
  have "?l_ys \<le> length xs" by simp

  let ?ys = "take ?l_ys xs"
  let ?zs = "drop ?l_ys xs"
  have concat:"xs = ?ys @ ?zs" by simp
  hence "length xs = length ?ys + length ?zs" by simp
  moreover from `?l_ys \<le> length xs` have l_ys:"length ?ys = ?l_ys" by simp
  ultimately have l_zs:"length ?zs = ?l_zs" by simp

  have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)"
  proof cases
    assume "?l_ys = ?l_zs"
    with concat l_ys l_zs show ?thesis by auto
  next
    assume "?l_ys \<noteq> ?l_zs"
    hence "?l_ys = ?l_zs + 1" by auto
    with concat l_ys l_zs show ?thesis by auto
  qed
  thus ?thesis by blast
qed
end