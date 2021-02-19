theory find_idx
  imports Main
begin
fun find_idx::"('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
"find_idx _ [] = None" |
"find_idx pred (x # xs) = (if pred x then Some 0 else
                          (case find_idx pred xs of None \<Rightarrow> None |
                                                    Some idx \<Rightarrow> Some (Suc idx)))"

lemma find_idx_bound:"find_idx pred xs = Some idx \<Longrightarrow> idx < length xs"
proof (induction xs arbitrary:idx)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have "pred x \<or> \<not> pred x" by simp
  thus ?case
  proof
    assume "pred x"
    with Cons.prems show ?case by simp
  next
    assume "\<not> pred x"
    moreover with Cons.prems obtain idx' where "find_idx pred xs = Some idx'" by fastforce
    ultimately show ?case using Cons by fastforce
  qed
qed

lemma find_idx_0:"\<exists>x\<in>set xs. pred x \<Longrightarrow> \<exists>idx. find_idx pred xs = Some idx"
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have "pred x \<or> \<not> pred x" by simp
  thus ?case
  proof
    assume "pred x"
    thus ?case by simp
  next
    assume "\<not> pred x"
    moreover with Cons.prems have "\<exists>x\<in>set xs. pred x" by auto
    ultimately obtain idx where "find_idx pred xs = Some idx" using Cons.IH by auto
    thus ?case using `\<not> pred x` by auto
  qed
qed

lemma "(\<exists>x\<in>set xs. pred x) = (\<exists>idx. find_idx pred xs = Some idx)"
proof
  have "\<forall>x\<in>set xs. \<not> pred x \<Longrightarrow> find_idx pred xs = None"
  proof (induction xs)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    from Cons.prems have "\<forall>x\<in>set xs. \<not> pred x" by auto
    moreover from Cons.prems have "\<not> pred x" by auto
    ultimately show ?case using Cons.IH by simp
  qed
  thus "\<exists>idx. find_idx pred xs = Some idx \<Longrightarrow> \<exists>x\<in>set xs. pred x" by fastforce
next
  from find_idx_0 show "\<exists>x\<in>set xs. pred x \<Longrightarrow> \<exists>idx. find_idx pred xs = Some idx" .
qed

lemma find_idx_1:"\<exists>x\<in>set xs. pred x \<Longrightarrow> pred (xs!the(find_idx pred xs))"
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have "pred x \<or> \<not> pred x" by simp
  thus ?case
  proof
    assume "pred x"
    thus ?case by simp
  next
    assume "\<not> pred x"
    moreover with Cons.prems have "\<exists>x\<in>set xs. pred x" by auto
    moreover with find_idx_0 obtain idx where idx:"find_idx pred xs = Some idx" by fastforce
    ultimately have "pred (xs!idx)" using Cons.IH by simp

    from idx `\<not> pred x` have "the (find_idx pred (x # xs)) = idx + 1" by auto
    moreover from `pred (xs!idx)` have "pred ((x # xs)!(idx + 1))" by auto
    ultimately show ?case by auto
  qed
qed

end