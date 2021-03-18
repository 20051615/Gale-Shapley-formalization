theory List_Ops
  imports Main
begin
fun find_idx::"'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
"find_idx _ [] = None" |
"find_idx term (x # xs) = (if term = x then Some 0 else
                          (case find_idx term xs of None \<Rightarrow> None |
                                                    Some idx \<Rightarrow> Some (Suc idx)))"

lemma find_idx_bound:"find_idx term xs = Some idx \<Longrightarrow> idx < length xs"
proof (induction xs arbitrary:idx)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "term = x"
    with Cons.prems show ?case by simp
  next
    assume "term \<noteq> x"
    moreover with Cons.prems obtain idx' where "find_idx term xs = Some idx'" by fastforce
    ultimately show ?case using Cons by fastforce
  qed
qed

lemma find_idx_Some:"term\<in>set xs \<longleftrightarrow> find_idx term xs \<noteq> None"
proof
  have "term \<notin> set xs \<Longrightarrow> find_idx term xs = None"
    apply (induction xs)
    by (auto)
  thus "find_idx term xs \<noteq> None \<Longrightarrow> term\<in>set xs" by meson
next
  show "term\<in>set xs \<Longrightarrow> find_idx term xs \<noteq> None"
    apply (induction xs)
     apply simp
    by force
qed

lemma find_idx_None:"find_idx term xs = None \<longleftrightarrow> term\<notin> set xs" using find_idx_Some by metis 

lemma find_idx_Some_is_first:"\<lbrakk>find_idx term xs = Some idx; idx' < idx\<rbrakk> \<Longrightarrow> xs!idx' \<noteq> term"
proof (induction xs arbitrary:idx idx')
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "term = x"
    hence "idx = 0" using Cons.prems(1) by simp
    hence False using Cons.prems(2) by simp
    thus ?case by simp
  next
    assume "term \<noteq> x"
    moreover with Cons.prems(1) obtain idx_1 where idx_1:"find_idx term xs = Some idx_1" using find_idx.simps by fastforce
    ultimately have "idx = Suc idx_1" using find_idx.simps Cons.prems(1) by fastforce
    show ?case
    proof (cases idx')
      case 0
      with `term \<noteq> x` show ?thesis by simp
    next
      case (Suc idx'_1)
      with Cons.prems(2) `idx = Suc idx_1` have "idx'_1 < idx_1" by simp
      with Cons.IH idx_1 have "xs!idx'_1 \<noteq> term" by simp
      with Suc show ?thesis by simp
    qed
  qed
qed

lemma find_idx_first_is_Some:"\<lbrakk>idx < length xs; \<forall>idx' < idx. xs!idx' \<noteq> term; xs!idx = term\<rbrakk> \<Longrightarrow> find_idx term xs = Some idx"
proof (induction xs arbitrary: idx)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases idx)
    case 0
    with Cons.prems(3) have "term = x" by simp
    thus ?thesis using 0 by simp
  next
    case (Suc idx_1)
    with Cons.prems(2) have "\<forall>idx'<idx_1. xs!idx' \<noteq> term" by (metis add_Suc_shift less_Suc_eq_le less_natE nat_arith.suc1 nat_le_iff_add nth_Cons_Suc)
    moreover from Suc Cons.prems(1) have "idx_1 < length xs" by simp
    moreover from Suc Cons.prems(3) have "xs!idx_1 = term" by simp
    ultimately have "find_idx term xs = Some idx_1" using Cons.IH by simp
    moreover from Cons.prems(2) Suc have "term \<noteq> x" by auto
    ultimately show ?thesis using Suc by simp
  qed
qed

lemma find_idx:"term\<in>set xs \<Longrightarrow> xs!the(find_idx term xs) = term"
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "term = x"
    thus ?case by simp
  next
    assume "term \<noteq> x"
    with Cons.prems have prem:"term\<in>set xs" by auto
    with find_idx_Some have "find_idx term xs \<noteq> None" by metis
    then obtain idx where idx:"find_idx term xs = Some idx" by blast
    hence "xs!idx = term" using Cons.IH prem by simp
    with idx `term \<noteq> x` show ?case by simp
  qed
qed
end
