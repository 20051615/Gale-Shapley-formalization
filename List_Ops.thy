theory List_Ops
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

lemma find_idx_Some:"(\<exists>x\<in>set xs. pred x) \<longleftrightarrow> (\<exists>idx. find_idx pred xs = Some idx)"
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
  show "\<exists>x\<in>set xs. pred x \<Longrightarrow> \<exists>idx. find_idx pred xs = Some idx"
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
qed

lemma find_idx_None:"find_idx pred xs = None \<longleftrightarrow> (\<forall>x \<in> set xs. \<not>pred x)" using find_idx_Some by (metis option.distinct(1) option.exhaust)

lemma find_idx_Some_is_first:"\<lbrakk>find_idx pred xs = Some idx; idx' < idx\<rbrakk> \<Longrightarrow> \<not> pred (xs!idx')"
proof (induction xs arbitrary:idx idx')
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "pred x"
    hence "idx = 0" using Cons.prems(1) by simp
    hence False using Cons.prems(2) by simp
    thus ?case by simp
  next
    assume "\<not>pred x"
    moreover with Cons.prems(1) obtain idx_1 where idx_1:"find_idx pred xs = Some idx_1" using find_idx.simps by fastforce
    ultimately have "idx = Suc idx_1" using find_idx.simps Cons.prems(1) by fastforce
    show ?case
    proof (cases idx')
      case 0
      with `\<not>pred x` show ?thesis by simp
    next
      case (Suc idx'_1)
      with Cons.prems(2) `idx = Suc idx_1` have "idx'_1 < idx_1" by simp
      with Cons.IH idx_1 have "\<not> pred (xs ! idx'_1)" by simp
      with Suc show ?thesis by simp
    qed
  qed
qed

lemma find_idx_first_is_Some:"\<lbrakk>idx < length xs; \<forall>idx' < idx.\<not> pred (xs!idx'); pred (xs!idx)\<rbrakk> \<Longrightarrow> find_idx pred xs = Some idx"
proof (induction xs arbitrary: idx)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases idx)
    case 0
    with Cons.prems(3) have "pred x" by simp
    thus ?thesis using 0 by simp
  next
    case (Suc idx_1)
    with Cons.prems(2) have "\<forall>idx'<idx_1. \<not> pred (xs!idx')" by (metis add_Suc_shift less_Suc_eq_le less_natE nat_arith.suc1 nat_le_iff_add nth_Cons_Suc)
    moreover from Suc Cons.prems(1) have "idx_1 < length xs" by simp
    moreover from Suc Cons.prems(3) have "pred (xs!idx_1)" by simp
    ultimately have "find_idx pred xs = Some idx_1" using Cons.IH by simp
    moreover from Cons.prems(2) Suc have "\<not> pred x" by auto
    ultimately show ?thesis using Suc by simp
  qed
qed

lemma find_idx:"\<exists>x\<in>set xs. pred x \<Longrightarrow> pred (xs!the(find_idx pred xs))"
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "pred x"
    thus ?case by simp
  next
    assume "\<not> pred x"
    moreover with Cons.prems have "\<exists>x\<in>set xs. pred x" by auto
    moreover with find_idx_Some obtain idx where idx:"find_idx pred xs = Some idx" by metis
    ultimately have "pred (xs!idx)" using Cons.IH by simp

    from idx `\<not> pred x` have "the (find_idx pred (x # xs)) = idx + 1" by auto
    moreover from `pred (xs!idx)` have "pred ((x # xs)!(idx + 1))" by auto
    ultimately show ?case by auto
  qed
qed
end
