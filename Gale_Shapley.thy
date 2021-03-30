theory Gale_Shapley
  imports "HOL-Library.Permutation"
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

lemma in_upt:"x < k \<longleftrightarrow> x \<in> set [0 ..< k]" by auto
lemma in_perm_upt: "x < k \<longleftrightarrow> (\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A)"
  using in_upt by (metis perm_refl perm_set_eq)

fun is_perm::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" where "is_perm A B = (mset A = mset B)"
lemma is_perm:"is_perm A B \<longleftrightarrow> A <~~> B" using mset_eq_perm by auto
fun is_valid_pref_matrix::"nat \<Rightarrow> pref_matrix \<Rightarrow> bool" where
"is_valid_pref_matrix N PPrefs = (length PPrefs = N \<and> Ball (set PPrefs) (is_perm [0 ..< N]))"
value "is_valid_pref_matrix 2 [[0, 1], [1, 0]]"
value "is_valid_pref_matrix 2 [[0, 0], [1, 0]]"
lemma length_PPrefs:"is_valid_pref_matrix N PPrefs \<Longrightarrow> length PPrefs = N" by simp
lemma perm_PPref:"\<lbrakk>is_valid_pref_matrix N PPrefs; m < N\<rbrakk> \<Longrightarrow> PPrefs!m <~~> [0 ..< N]" 
  using is_perm nth_mem by fastforce

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
    moreover with Cons.prems obtain idx' where idx':"find_idx term xs = Some idx'" by fastforce
    ultimately show ?case using Cons.IH[OF idx'] Cons.prems by simp
  qed
qed

lemma find_idx_Some:"term \<in> set xs \<longleftrightarrow> find_idx term xs \<noteq> None"
proof
  have "term \<notin> set xs \<Longrightarrow> find_idx term xs = None"
    apply (induction xs)
    by auto
  thus "find_idx term xs \<noteq> None \<Longrightarrow> term \<in> set xs" by meson
next
  show "term \<in> set xs \<Longrightarrow> find_idx term xs \<noteq> None"
    apply (induction xs)
     apply simp
    by fastforce
qed

lemma find_idx_None:"find_idx term xs = None \<longleftrightarrow> term \<notin> set xs" using find_idx_Some by metis 

lemma find_idx_Some_is_first:"\<lbrakk>find_idx term xs = Some idx; idx' < idx\<rbrakk> \<Longrightarrow> xs!idx' \<noteq> term"
proof (induction xs arbitrary:idx idx')
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "term = x"
    thus ?case using Cons.prems by simp
  next
    assume "term \<noteq> x"
    moreover with Cons.prems(1) obtain idx_1
      where idx_1:"find_idx term xs = Some idx_1" by fastforce
    ultimately have idx:"idx = Suc idx_1" using Cons.prems(1) by simp
    show ?case
    proof (cases idx')
      case 0
      with `term \<noteq> x` show ?thesis by simp
    next
      case (Suc idx'_1)
      with Cons.prems(2) idx have "idx'_1 < idx_1" by simp
      from Cons.IH[OF idx_1 this] Suc show ?thesis by simp
    qed
  qed
qed

lemma find_idx_first_is_Some:
"\<lbrakk>idx < length xs; \<forall>idx' < idx. xs!idx' \<noteq> term; xs!idx = term\<rbrakk> \<Longrightarrow> find_idx term xs = Some idx"
proof (induction xs arbitrary: idx)
  case Nil
  from Nil.prems(1) show ?case by simp
next
  case Cons
  thus ?case
    apply (cases idx)
     apply simp
    by fastforce
qed

lemma find_idx:"find_idx term xs = Some idx \<Longrightarrow> xs!idx = term"
proof (induction xs arbitrary:idx)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "term = x"
    thus ?case using Cons.prems by simp
  next
    assume "term \<noteq> x"
    moreover with Cons.prems obtain idx_1 where idx_1:"find_idx term xs = Some idx_1" by fastforce
    ultimately show ?case using Cons.IH[OF idx_1] Cons.prems by fastforce
  qed
qed

fun findFreeMan::"matching \<Rightarrow> man option" where
"findFreeMan engagements = find_idx None engagements"
lemma findFreeMan_bound:"findFreeMan engagements = Some m \<Longrightarrow> m < length engagements"
  using find_idx_bound[of None engagements m] by simp 
lemma findFreeMan_None:"findFreeMan engagements = None \<longleftrightarrow> None \<notin> set engagements"
  using find_idx_None[of None engagements] by simp
lemma findFreeMan:"findFreeMan engagements = Some m \<Longrightarrow> engagements!m = None"
  using find_idx[of None engagements m] by simp

fun findFiance::"matching \<Rightarrow> woman \<Rightarrow> man option" where
"findFiance engagements w = find_idx (Some w) engagements"
lemma findFiance_bound:"findFiance engagements w = Some m \<Longrightarrow> m < length engagements" 
  using find_idx_bound[of "Some w" engagements m] by simp
lemma findFiance_Some:"findFiance engagements w \<noteq> None \<longleftrightarrow> Some w \<in> set engagements"
  using find_idx_Some[of "Some w" engagements] by simp
lemma findFiance_None:"findFiance engagements w = None \<longleftrightarrow> Some w \<notin> set engagements"
  using findFiance_Some by blast
lemma findFiance_Some_is_first:
"\<lbrakk>findFiance engagements w = Some m; m' < m\<rbrakk> \<Longrightarrow> engagements!m' \<noteq> Some w" 
  using find_idx_Some_is_first[of "Some w" engagements m m'] by simp
lemma findFiance_first_is_Some:
"\<lbrakk>m < length engagements; \<forall>m'<m. engagements!m'\<noteq>Some w; engagements!m = Some w\<rbrakk>
   \<Longrightarrow> findFiance engagements w = Some m"
  using find_idx_first_is_Some[of m engagements "Some w"] by simp
lemma findFiance:"findFiance engagements w = Some m \<Longrightarrow> engagements!m = Some w" 
  using find_idx[of "Some w" engagements m] by simp

fun findPerson::"person list \<Rightarrow> person \<Rightarrow> nat option" where
"findPerson ps p = find_idx p ps"
lemma findPerson_Some:"findPerson ps p \<noteq> None \<longleftrightarrow> p \<in> set ps" using find_idx_Some[of p ps] by simp

fun prefers::"person \<Rightarrow> pref_matrix \<Rightarrow> person \<Rightarrow> person \<Rightarrow> bool" where
"prefers p PPrefs p1 p2 = (
case findPerson (PPrefs!p) p1 of None \<Rightarrow> False |
                                 Some idx_1 \<Rightarrow> (
  case findPerson (PPrefs!p) p2 of None \<Rightarrow> False |
                                   Some idx_2 \<Rightarrow> idx_1 < idx_2))"

lemma prefers_trans:
  assumes 12:"prefers p PPrefs p1 p2" and 23:"prefers p PPrefs p2 p3"
  shows "prefers p PPrefs p1 p3"
proof -
  from 12 obtain idx_1 where idx_1:"findPerson (PPrefs!p) p1 = Some idx_1" by fastforce
  from 23 obtain idx_2 where idx_2:"findPerson (PPrefs!p) p2 = Some idx_2" by fastforce
  with 23 obtain idx_3 where idx_3:"findPerson (PPrefs!p) p3 = Some idx_3" by fastforce
  from 12 idx_1 idx_2 have "idx_1 < idx_2" by auto
  moreover from 23 idx_2 idx_3 have "idx_2 < idx_3" by auto
  ultimately show ?thesis using idx_1 idx_3 by fastforce
qed

lemma termination_aid:
  assumes 1:"length engagements = length prop_idxs"
    and 2:"findFreeMan engagements = Some m"
    and 3:"next_prop_idxs = prop_idxs[m:=Suc(prop_idxs!m)]"
    and 4:"sum_list prop_idxs < N * N"
  shows "N * N - sum_list next_prop_idxs < N * N - sum_list prop_idxs"
proof -
  from 1 findFreeMan_bound[OF 2] have m_bound:"m < length prop_idxs" by presburger
  have "m < length xs \<Longrightarrow> sum_list (xs[m:=Suc (xs!m)]) = Suc (sum_list xs)" for m xs
  proof (induction xs arbitrary:m)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    thus ?case
      apply (cases m)
      by (simp_all)
  qed
  from this[OF m_bound] 3 4 show ?thesis by auto
qed

function Gale_Shapley'::
"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix \<Rightarrow>
 matching \<Rightarrow> nat list \<Rightarrow>
 matching" where
"Gale_Shapley' N MPrefs WPrefs 
 engagements prop_idxs 
 = 
(if length engagements \<noteq> length prop_idxs then engagements else
(if sum_list prop_idxs \<ge> N * N then engagements else

(case findFreeMan engagements of None \<Rightarrow> engagements |

 Some m \<Rightarrow> (let w = MPrefs!m!(prop_idxs!m);
   next_prop_idxs = prop_idxs[m:=Suc (prop_idxs!m)] in (
   case findFiance engagements w of
     None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
            (engagements[m:=Some w]) next_prop_idxs
   | Some m' \<Rightarrow> (
     if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
                                  (engagements[m:=Some w, m':=None]) next_prop_idxs
                              else Gale_Shapley' N MPrefs WPrefs
                                   engagements next_prop_idxs))))))"
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(N, _, _, _, prop_idxs). N * N - sum_list prop_idxs)")
  by (auto intro:termination_aid)

fun Gale_Shapley::"pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching" where
"Gale_Shapley MPrefs WPrefs = (let N = length MPrefs in
 Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0))"

function GS'_arg_seq::
"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> nat list \<Rightarrow> (matching \<times> nat list) list" where
"GS'_arg_seq N MPrefs WPrefs engagements prop_idxs = 
(if length engagements \<noteq> length prop_idxs then [(engagements, prop_idxs)] else
(if sum_list prop_idxs \<ge> N * N then [(engagements, prop_idxs)] else

(case findFreeMan engagements of None \<Rightarrow> [(engagements, prop_idxs)] | 

 Some m \<Rightarrow> (let w = MPrefs!m!(prop_idxs!m);
   next_prop_idxs = prop_idxs[m:=Suc (prop_idxs!m)] in (
   case findFiance engagements w of
     None \<Rightarrow> (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
             (engagements[m:=Some w]) next_prop_idxs)
   | Some m' \<Rightarrow> (
     if prefers w WPrefs m m' then (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                   (engagements[m:=Some w, m':=None]) next_prop_idxs)
                              else (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                    engagements next_prop_idxs)))))))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(N, _, _, _, prop_idxs). N * N - sum_list prop_idxs)")
  by (auto intro:termination_aid)

abbreviation is_terminal where
"is_terminal N engagements prop_idxs \<equiv>
 length engagements \<noteq> length prop_idxs \<or>
 sum_list prop_idxs \<ge> N * N \<or>
 findFreeMan engagements = None"

lemma GS'_arg_seq_non_Nil:"GS'_arg_seq N MPrefs WPrefs engagements prop_idxs \<noteq> []"
proof cases
  assume "is_terminal N engagements prop_idxs"
  thus ?thesis by auto
next
  assume "\<not> is_terminal N engagements prop_idxs"
  then obtain m where "findFreeMan engagements = Some m" by blast
  thus ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma GS'_arg_seq_length_gr_0:
"length(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) > 0"
  using GS'_arg_seq_non_Nil by auto

lemma GS'_arg_seq_length_gr_1:
"\<not>is_terminal N engagements prop_idxs \<longleftrightarrow> 
 length(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) > 1"
proof
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show "\<not>is_terminal N engagements prop_idxs \<Longrightarrow> length(?seq) > 1"
  proof -
    assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
    then obtain m where m:"findFreeMan engagements = Some m" by blast
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
      from non_terminal m None have "length ?seq = Suc (length ?seq_tl)" by (simp add:Let_def)
      moreover from GS'_arg_seq_length_gr_0 have "length ?seq_tl > 0" by fast
      ultimately show ?thesis by linarith
    next
      case (Some m')
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs
                                  (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
        from non_terminal m Some change 
        have "length ?seq = Suc (length ?seq_tl)" by (simp add:Let_def)
        moreover from GS'_arg_seq_length_gr_0 have "length ?seq_tl > 0" by fast
        ultimately show ?thesis by linarith
      next
        assume no_change:"\<not>prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from non_terminal m Some no_change
        have "length ?seq = Suc (length ?seq_tl)" by (simp add:Let_def)
        moreover from GS'_arg_seq_length_gr_0 have "length ?seq_tl > 0" by fast
        ultimately show ?thesis by linarith
      qed
    qed
  qed
next
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show "length ?seq > 1 \<Longrightarrow> \<not>is_terminal N engagements prop_idxs"
  proof
    assume "is_terminal N engagements prop_idxs"
    hence "length ?seq = 1" by auto
    moreover assume "length ?seq > 1"
    ultimately show False by auto
  qed
qed

lemma GS'_arg_seq_0 [simp]:
"(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)!0 = (engagements, prop_idxs)"
proof cases
  assume "is_terminal N engagements prop_idxs"
  thus ?thesis by fastforce
next
  assume "\<not> is_terminal N engagements prop_idxs"
  moreover then obtain m where "findFreeMan engagements = Some m" by blast
  ultimately show ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma tl_i_1_eq:"\<lbrakk>i = Suc i_1; seq = x # xs; (seq!i) = X\<rbrakk> \<Longrightarrow> (xs!i_1) = X" by fastforce

lemma i_1_bound:"\<lbrakk>i = Suc i_1; seq = x # xs; i < length seq\<rbrakk> \<Longrightarrow> i_1 < length xs" by simp

lemma GS'_arg_seq_last_eq_terminal:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk>
   \<Longrightarrow> is_terminal N X Y \<longleftrightarrow> (i = length seq - 1)"
proof
  show "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y);
         is_terminal N X Y\<rbrakk> \<Longrightarrow> i = length seq - 1"
  proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq i rule:GS'_arg_seq.induct)
    case (1 N MPrefs WPrefs engagements prop_idxs)
    show ?case
    proof (cases i)
      case 0
      hence "is_terminal N engagements prop_idxs" using "1.prems" by (simp del:GS'_arg_seq.simps)
      hence "length seq = 1" using "1.prems"(1) by fastforce
      thus ?thesis using 0 by simp
    next
      case (Suc i_1)
      hence "length seq > 1" using "1.prems"(2) by auto
      hence non_terminal:"\<not> is_terminal N engagements prop_idxs"
        using "1.prems"(1) GS'_arg_seq_length_gr_1 by blast
      then obtain m where m:"findFreeMan engagements = Some m" by blast
      let ?w = "MPrefs!m!(prop_idxs!m)"
      let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m None 
        have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        moreover from "1.IH"(1)[OF _ _ m _ _ None _ i_1_bound[OF Suc this "1.prems"(2)]
            tl_i_1_eq[OF Suc this "1.prems"(3)] "1.prems"(4)] non_terminal
        have "i_1 = length ?seq_tl - 1" by blast
        moreover have "length ?seq_tl > 0" using GS'_arg_seq_length_gr_0 by blast
        ultimately show ?thesis using Suc by simp
      next
        case (Some m')
        show ?thesis
        proof cases
          assume change:"prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs
                                    (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
          from "1.prems"(1) non_terminal m Some change
          have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
          moreover from "1.IH"(2)[OF _ _ m _ _ Some change _ i_1_bound[OF Suc this "1.prems"(2)]
              tl_i_1_eq[OF Suc this "1.prems"(3)] "1.prems"(4)] non_terminal
          have "i_1 = length ?seq_tl - 1" by blast
          moreover have "length ?seq_tl > 0" using GS'_arg_seq_length_gr_0 by blast
          ultimately show ?thesis using Suc by simp 
        next
          assume no_change:"\<not> prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
          from "1.prems"(1) non_terminal m Some no_change 
          have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
          moreover from "1.IH"(3)[OF _ _ m _ _ Some no_change _ i_1_bound[OF Suc this "1.prems"(2)]
              tl_i_1_eq[OF Suc this "1.prems"(3)] "1.prems"(4)] non_terminal
          have "i_1 = length ?seq_tl - 1" by blast
          moreover have "length ?seq_tl > 0" using GS'_arg_seq_length_gr_0 by blast
          ultimately show ?thesis using Suc by simp
        qed
      qed
    qed
  qed
next
  show "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y);
         i = length seq - 1\<rbrakk> \<Longrightarrow> is_terminal N X Y"
  proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq i rule: GS'_arg_seq.induct)
    case (1 N MPrefs WPrefs engagements prop_idxs)
    show ?case
    proof cases
      assume "is_terminal N engagements prop_idxs"
      moreover hence "i = 0" using "1.prems"(1) "1.prems"(4) by fastforce
      ultimately show ?case using "1.prems"(1) "1.prems"(3) by (simp del:GS'_arg_seq.simps)
    next
      assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
      then obtain m where m:"findFreeMan engagements = Some m" by blast
      from non_terminal "1.prems"(1) GS'_arg_seq_length_gr_1 have "length seq > 1" by presburger
      with "1.prems"(4) have "i \<noteq> 0" by linarith
      then obtain i_1 where i_1:"i = Suc i_1" using not0_implies_Suc by auto 
      let ?w = "MPrefs!m!(prop_idxs!m)"
      let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
      show ?case
      proof (cases "findFiance engagements ?w")
        case None
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m None
        have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        hence "i_1 = length ?seq_tl - 1" using i_1 "1.prems"(4) by simp
        from "1.IH"(1)[OF _ _ m _ _ None _ i_1_bound[OF i_1 seq_tl "1.prems"(2)]
            tl_i_1_eq[OF i_1 seq_tl "1.prems"(3)] this] non_terminal
        show ?thesis by presburger
      next
        case (Some m')
        show ?thesis
        proof cases
          assume change:"prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs 
                                    (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
          from "1.prems"(1) non_terminal m Some change 
          have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
          hence "i_1 = length ?seq_tl - 1" using i_1 "1.prems"(4) by simp
          from "1.IH"(2)[OF _ _ m _ _ Some change _ i_1_bound[OF i_1 seq_tl "1.prems"(2)]
              tl_i_1_eq[OF i_1 seq_tl "1.prems"(3)] this] non_terminal
          show ?thesis by presburger
        next
          assume no_change:"\<not> prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
          from "1.prems"(1) non_terminal m Some no_change
          have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
          hence "i_1 = length ?seq_tl - 1" using i_1 "1.prems"(4) by simp
          from "1.IH"(3)[OF _ _ m _ _ Some no_change _ i_1_bound[OF i_1 seq_tl "1.prems"(2)]
              tl_i_1_eq[OF i_1 seq_tl "1.prems"(3)] this] non_terminal
          show ?thesis by presburger
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_same_endpoint:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk> \<Longrightarrow> Gale_Shapley' N MPrefs WPrefs X Y = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?endpoint = "Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using "1.prems" by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    hence "length seq > 1" using "1.prems"(2) by auto
    hence non_terminal:"\<not>is_terminal N engagements prop_idxs" using "1.prems"(1) GS'_arg_seq_length_gr_1 by blast
    then obtain m where m:"findFreeMan engagements = Some m" by blast
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
      have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m None "1.prems"(1) by (simp add:Let_def)
      hence "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" using Suc "1.prems"(2-3) by simp_all
      thus ?thesis using "1.IH"(1) non_terminal m None by (simp add:Let_def)
    next
      case (Some m')
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
        have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m Some change "1.prems"(1) by (simp add:Let_def)
        hence "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" using Suc "1.prems"(2-3) by simp_all
        thus ?thesis using "1.IH"(2) non_terminal m Some change by (simp add:Let_def)
      next
        assume no_change:"\<not>prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m Some no_change "1.prems"(1) by (simp add:Let_def)
        hence "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" using Suc "1.prems"(2-3) by simp_all
        thus ?thesis using "1.IH"(3) non_terminal m Some no_change by (simp add:Let_def)
      qed
    qed
  qed
qed

theorem GS'_arg_seq_computes_GS':
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs" and X_Y:"seq!(length seq - 1) = (X, Y)"
  shows "X = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
proof -
  from seq GS'_arg_seq_non_Nil have i_bound:"length seq - 1 < length seq" by fastforce
  hence "is_terminal N X Y" using seq X_Y GS'_arg_seq_last_eq_terminal by metis
  hence "X = Gale_Shapley' N MPrefs WPrefs X Y" by force
  also have "... = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs" using seq i_bound X_Y GS'_arg_seq_same_endpoint by blast
  finally show ?thesis .
qed

lemma GS'_arg_seq_step_1:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = None\<rbrakk> \<Longrightarrow> seq!Suc i = (X[m:=Some w], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  have non_terminal:"\<not>is_terminal N engagements prop_idxs"
  proof
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by force
    ultimately show False using "1.prems"(2-4) by simp
  qed
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  let ?next_prop_idxs = "prop_idxs[m_0:=Suc(prop_idxs!m_0)]"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1-3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w]) (Y[m:=Suc(Y!m)])" by (simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w]) ?next_prop_idxs"
      from "1.prems"(1) non_terminal m_0 None have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
      with "1.IH"(1) non_terminal m_0 None "1.prems"(4-7) have "?seq_tl!Suc i_1 = (X[m:=Some w], Y[m:=Suc(Y!m)])" by metis
      with seq_tl Suc show ?thesis by simp
    next
      case (Some m')
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m_0 m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w, m':=None]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(2) non_terminal m_0 Some change "1.prems"(4-7) have "?seq_tl!Suc i_1 = (X[m:=Some w], Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      next
        assume no_change:"\<not>prefers ?w WPrefs m_0 m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some no_change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(3) non_terminal m_0 Some no_change "1.prems"(4-7) have "?seq_tl!Suc i_1 = (X[m:=Some w], Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      qed
    qed
  qed
qed

lemma GS'_arg_seq_step_2:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; prefers w WPrefs m m'\<rbrakk> \<Longrightarrow> seq!Suc i = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  have non_terminal:"\<not>is_terminal N engagements prop_idxs"
  proof
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by auto
    ultimately show False using "1.prems"(2-4) by simp
  qed
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  let ?next_prop_idxs = "prop_idxs[m_0:=Suc(prop_idxs!m_0)]"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1-3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w, m':=None]) (Y[m:=Suc(Y!m)])" by (auto simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w]) ?next_prop_idxs"
      from "1.prems"(1) non_terminal m_0 None have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
      with "1.IH"(1) non_terminal m_0 None "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])" by metis
      with seq_tl Suc show ?thesis by simp
    next
      case (Some m'_0)
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m_0 m'_0"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w, m'_0:=None]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(2) non_terminal m_0 Some change "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      next
        assume no_change:"\<not>prefers ?w WPrefs m_0 m'_0"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some no_change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(3) non_terminal m_0 Some no_change "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      qed
    qed
  qed
qed

lemma GS'_arg_seq_step_3:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; \<not>prefers w WPrefs m m'\<rbrakk> \<Longrightarrow> seq!Suc i = (X, Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  have non_terminal:"\<not>is_terminal N engagements prop_idxs"
  proof
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by auto
    ultimately show False using "1.prems"(2-4) by simp
  qed
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  let ?next_prop_idxs = "prop_idxs[m_0:=Suc(prop_idxs!m_0)]"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1-3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs X (Y[m:=Suc(Y!m)])" by (auto simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w]) ?next_prop_idxs"
      from "1.prems"(1) non_terminal m_0 None have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
      with "1.IH"(1) non_terminal m_0 None "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X, Y[m:=Suc(Y!m)])" by metis
      with seq_tl Suc show ?thesis by simp
    next
      case (Some m'_0)
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m_0 m'_0"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w, m'_0:=None]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(2) non_terminal m_0 Some change "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X, Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      next
        assume no_change:"\<not>prefers ?w WPrefs m_0 m'_0"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from "1.prems"(1) non_terminal m_0 Some no_change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        with "1.prems"(2-3) Suc have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X, Y)" by auto
        with "1.IH"(3) non_terminal m_0 Some no_change "1.prems"(4-8) have "?seq_tl!Suc i_1 = (X, Y[m:=Suc(Y!m)])" by metis
        with seq_tl Suc show ?thesis by simp
      qed
    qed
  qed
qed

lemma GS'_arg_seq_snd_step:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "i < length seq" and "seq!i = (X, Y)"
      and "\<not>is_terminal N X Y" and "findFreeMan X = Some m"
      and "seq!Suc i = (X_next, Y_next)"
    shows "Y_next = Y[m:=Suc(Y!m)]"
proof (cases "findFiance X (MPrefs!m!(Y!m))")
  case None
  with assms GS'_arg_seq_step_1 show ?thesis by (simp del:GS'_arg_seq.simps)
next
  case (Some m')
  show ?thesis
  proof cases
    assume "prefers (MPrefs!m!(Y!m)) WPrefs m m'"
    with assms Some GS'_arg_seq_step_2 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    assume "\<not>prefers (MPrefs!m!(Y!m)) WPrefs m m'"
    with assms Some GS'_arg_seq_step_3 show ?thesis by (simp del:GS'_arg_seq.simps)
  qed
qed

lemma GS'_arg_seq_length_fst:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk> \<Longrightarrow> length X = length engagements"
proof (induction i arbitrary:X Y)
  case 0
  thus ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  from Suc.prems(2) have "i \<noteq> length seq - 1" and i_bound:"i < length seq" by simp_all
  moreover obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  ultimately have non_terminal:"\<not>is_terminal N X_prev Y_prev" using GS'_arg_seq_last_eq_terminal Suc.prems(1) by blast
  then obtain m where m:"findFreeMan X_prev = Some m" by blast
  let ?w = "MPrefs!m!(Y_prev!m)"
  let ?next_prop_idxs = "Y_prev[m:=Suc(Y_prev!m)]"
  have IH:"length X_prev = length engagements" using Suc.IH Suc.prems(1) i_bound seq_i by blast
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    hence "(seq!(Suc i)) = (X_prev[m:=Some ?w], ?next_prop_idxs)" using GS'_arg_seq_step_1 non_terminal m i_bound seq_i Suc.prems(1) by meson
    with IH Suc.prems(3) show ?thesis by fastforce
  next
    case (Some m')
    show ?thesis
    proof cases
      assume "prefers ?w WPrefs m m'"
      hence "(seq!(Suc i)) = (X_prev[m:=Some ?w, m':=None], ?next_prop_idxs)" using GS'_arg_seq_step_2 non_terminal m Some i_bound seq_i Suc.prems(1) by meson
      with IH Suc.prems(3) show ?thesis by fastforce
    next
      assume "\<not>prefers ?w WPrefs m m'"
      hence "(seq!(Suc i)) = (X_prev, ?next_prop_idxs)" using GS'_arg_seq_step_3 non_terminal m Some i_bound seq_i Suc.prems(1) by meson
      with IH Suc.prems(3) show ?thesis by fastforce
    qed
  qed
qed

lemma GS'_arg_seq_length_snd:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk> \<Longrightarrow> length Y = length prop_idxs"
proof (induction i arbitrary: X Y)
  case 0
  thus ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  from Suc.prems(2) have "i \<noteq> length seq - 1" and i_bound:"i < length seq" by simp_all
  moreover obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  ultimately have "\<not>is_terminal N X_prev Y_prev" using GS'_arg_seq_last_eq_terminal Suc.prems(1) by blast
  moreover then obtain m where m:"findFreeMan X_prev = Some m" by blast
  ultimately have "Y = Y_prev[m:=Suc(Y_prev!m)]" using GS'_arg_seq_snd_step Suc.prems(1) i_bound seq_i Suc.prems(3) by metis
  moreover have "length Y_prev = length prop_idxs" using Suc i_bound seq_i by blast
  ultimately show ?case by simp
qed

abbreviation is_distinct where
"is_distinct engagements \<equiv> \<forall>m1 < length engagements. \<forall>m2 < length engagements. 
                           m1 \<noteq> m2 \<longrightarrow> engagements!m1 = None \<or> engagements!m1 \<noteq> engagements!m2"

abbreviation is_bounded where
"is_bounded engagements \<equiv> \<forall>m < length engagements. engagements!m \<noteq> None \<longrightarrow> the (engagements!m) < length engagements"

lemma is_matching_intro:
  assumes noFree:"\<forall>m < length engagements. engagements!m \<noteq> None"
    and "is_distinct engagements"
    and "is_bounded engagements"
  shows "engagements <~~> map Some [0 ..< length engagements]"
proof -
  let ?engagements = "map the engagements"
  let ?N = "length engagements"
  from noFree have engagements:"engagements = map Some ?engagements" by (simp add: nth_equalityI)
  from `is_bounded engagements` noFree have "\<forall>m < length ?engagements. ?engagements!m < ?N" by fastforce
  hence "\<forall>w \<in> set ?engagements. w < ?N" by (metis in_set_conv_nth)
  hence subset:"set ?engagements \<subseteq> set [0 ..< ?N]" using in_upt by blast

  from noFree `is_distinct engagements` have "\<forall>m1 < length engagements. \<forall>m2 < length engagements.
                                               m1 \<noteq> m2 \<longrightarrow> engagements!m1 \<noteq> engagements!m2" by blast
  with noFree have "\<forall>m1 < length engagements. \<forall>m2 < length engagements.
                     m1 \<noteq> m2 \<longrightarrow> the (engagements!m1) \<noteq> the (engagements!m2)" by (metis option.expand)
  hence distinct:"distinct ?engagements" by (simp add: distinct_conv_nth)
  hence "card (set ?engagements) = length ?engagements" by (metis distinct_card)
  also have "... = ?N" by simp
  finally have "card (set ?engagements) = ?N" .
  moreover have "finite (set [0 ..< ?N])" and "card (set [0 ..< ?N]) = ?N" and "distinct [0 ..< ?N]" by simp_all
  ultimately have "mset ?engagements = mset [0 ..< ?N]" using subset distinct by (metis card_subset_eq set_eq_iff_mset_eq_distinct)
  moreover have "mset (xs::nat list) = mset ys \<Longrightarrow> mset (map Some xs) = mset (map Some ys)" for xs ys by simp
  ultimately have "mset (map Some ?engagements) = mset (map Some [0..<?N])" by meson
  thus ?thesis using engagements by (metis mset_eq_perm)
qed

lemma GS'_arg_seq_all_distinct:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; is_distinct engagements; i < length seq; seq!i = (X, Y)\<rbrakk> \<Longrightarrow> is_distinct X"
proof (induction i arbitrary: X Y)
  case 0
  thus ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  from Suc.prems(3) have i_bound:"i < length seq" by linarith
  moreover obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  ultimately have distinct:"is_distinct X_prev" using Suc.prems(1-2) Suc.IH by blast
  from Suc.prems(3) have "i \<noteq> length seq - 1" by linarith
  hence non_terminal:"\<not>is_terminal N X_prev Y_prev" using GS'_arg_seq_last_eq_terminal Suc.prems(1) i_bound seq_i by blast
  then obtain m where m:"findFreeMan X_prev = Some m" by blast
  let ?w = "MPrefs!m!(Y_prev!m)"
  let ?next_prop_idxs = "Y_prev[m:=Suc(Y_prev!m)]"
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    hence "\<forall>m < length X_prev. X_prev!m \<noteq> Some ?w" by (metis nth_mem findFiance_None)
    with distinct have "is_distinct (X_prev[m:=Some ?w])" by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
    moreover have "seq!Suc i = (X_prev[m:=Some ?w], ?next_prop_idxs)" using GS'_arg_seq_step_1 Suc.prems(1) i_bound seq_i non_terminal m None by meson
    ultimately show ?thesis using Suc.prems(4) by simp
  next
    case (Some m')
    show ?thesis
    proof cases
      assume change:"prefers ?w WPrefs m m'"
      from Some findFiance findFiance_bound have "m' < length X_prev \<and> X_prev!m' = Some ?w" by simp
      moreover hence "\<forall>m < length X_prev. m \<noteq> m' \<longrightarrow> X_prev!m \<noteq> Some ?w" using distinct by fastforce
      ultimately have "is_distinct (X_prev[m:=Some ?w, m':=None])" using distinct by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
      moreover have "seq!Suc i = (X_prev[m:=Some ?w, m':= None], ?next_prop_idxs)" using GS'_arg_seq_step_2 Suc.prems(1) i_bound seq_i non_terminal m Some change by meson
      ultimately show ?thesis using Suc.prems(4) by simp
    next
      assume "\<not>prefers ?w WPrefs m m'"
      hence "seq!Suc i = (X_prev, ?next_prop_idxs)" using GS'_arg_seq_step_3 Suc.prems(1) i_bound seq_i non_terminal m Some by meson
      thus ?thesis using distinct Suc.prems(4) by simp
    qed
  qed
qed

fun married_better::"woman \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> matching \<Rightarrow> bool" where
"married_better w WPrefs eng_1 eng_2 = (case findFiance eng_1 w of None \<Rightarrow> True | Some m_1 \<Rightarrow> (
                                          case findFiance eng_2 w of None \<Rightarrow> False | Some m_2 \<Rightarrow> (
                                            m_1 = m_2 \<or> prefers w WPrefs m_2 m_1)))"

lemma married_better_refl: "married_better w WPrefs eng eng"
  apply (cases "findFiance eng w")
  by simp_all

lemma married_better_imp:"\<lbrakk>findFiance eng_1 w = Some m_1; married_better w WPrefs eng_1 eng_2\<rbrakk> 
                            \<Longrightarrow> \<exists>m_2. findFiance eng_2 w = Some m_2 
                                    \<and> (m_1 = m_2 \<or> prefers w WPrefs m_2 m_1)"
  apply (cases "findFiance eng_2 w")
  by simp_all

lemma married_better_trans:
  assumes 12:"married_better w WPrefs eng_1 eng_2" and 23:"married_better w WPrefs eng_2 eng_3"
  shows "married_better w WPrefs eng_1 eng_3"
proof (cases "findFiance eng_1 w")
  case None
  thus ?thesis by simp
next
  case (Some m_1)
  from married_better_imp[OF this 12] obtain m_2
    where m_2:"findFiance eng_2 w = Some m_2" 
      and 12:"m_1 = m_2 \<or> prefers w WPrefs m_2 m_1" by blast
  from married_better_imp[OF m_2 23] obtain m_3
    where m_3:"findFiance eng_3 w = Some m_3"
      and 23:"m_2 = m_3 \<or> prefers w WPrefs m_3 m_2" by blast
  from 12 show ?thesis
  proof
    assume "m_1 = m_2"
    with 23 show ?thesis using Some m_3 by simp
  next
    assume 12:"prefers w WPrefs m_2 m_1"
    from 23 show ?thesis
      apply (rule)
      using Some m_3 12 prefers_trans[OF _ 12] by (simp_all)
  qed
qed

lemma GS'_arg_seq_all_w_marry_better:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; is_distinct engagements; i < length seq; seq!i = (X_pre, Y_pre); j < length seq; seq!j = (X_post, Y_post); i \<le> j\<rbrakk> \<Longrightarrow> married_better w WPrefs X_pre X_post"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i j X_pre Y_pre rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    with "1.prems" have "length seq = 1" by auto
    with "1.prems"(3-6) married_better_refl show ?case by auto
  next
    assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
    then obtain m where m:"findFreeMan engagements = Some m" by auto
    from non_terminal "1.prems"(1) have l_seq:"1 < length seq" using GS'_arg_seq_length_gr_1 by presburger
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
    show ?case
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
      from None "1.prems"(1) have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
      have "seq!1 = (engagements[m:=Some ?w], ?next_prop_idxs)" using seq_tl by (simp del:GS'_arg_seq.simps)
      hence distinct:"is_distinct (engagements[m:=Some ?w])" using GS'_arg_seq_all_distinct "1.prems"(1-2) l_seq by blast
      show ?thesis
      proof (cases i)
        case (Suc i_1)
        with `i\<le>j` obtain j_1 where j_1:"j = Suc j_1" using Suc_le_D by auto
        from Suc seq_tl "1.prems"(3-4) have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X_pre, Y_pre)" by auto
        moreover from j_1 seq_tl "1.prems"(5-6) have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
        moreover from "1.prems"(7) Suc j_1 have "i_1 \<le> j_1" by fastforce
        ultimately show ?thesis using "1.IH"(1) non_terminal m None distinct by blast
      next
        case 0
        show ?thesis
        proof (cases j)
          case 0
          thus ?thesis using married_better_refl `i=0` "1.prems"(4-6) by simp
        next
          case (Suc j_1)
          have "0 \<le> j_1" by fast
          moreover from Suc "1.prems"(5-6) seq_tl have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
          moreover from GS'_arg_seq_length_gr_0 have "0 < length ?seq_tl" by fast
          moreover have "?seq_tl!0 = (engagements[m:=Some ?w], ?next_prop_idxs)" by (simp del:GS'_arg_seq.simps)
          ultimately have "married_better w WPrefs (engagements[m:=Some ?w]) X_post" using "1.IH"(1) non_terminal m None distinct by blast
          moreover have "married_better w WPrefs engagements (engagements[m:=Some ?w])"
          proof cases
            assume "w = ?w"
            moreover from None have "married_better ?w WPrefs engagements (engagements [m:=Some ?w])" by simp
            ultimately show ?thesis by simp
          next
            assume "w \<noteq> ?w"
            show ?thesis
            proof (cases "findFiance engagements w")
              case None
              thus ?thesis by simp
            next
              case (Some m_w)
              hence "\<forall>m'<m_w. engagements!m' \<noteq> Some w" using findFiance_Some_is_first by auto
              hence false_front:"\<forall>m'<m_w. (engagements[m:=Some ?w])!m' \<noteq> Some w" using `w \<noteq> ?w` by (metis findFreeMan_bound m nth_list_update option.inject)
              from Some findFiance have Some_idx:"engagements!m_w = Some w" by simp
              moreover from m findFreeMan have "engagements!m = None" by simp
              ultimately have "m \<noteq> m_w" by auto
              hence "engagements[m:=Some ?w]!m_w = Some w" using Some_idx by simp
              moreover from Some findFiance_bound have "m_w < length (engagements[m:=Some ?w])" by simp
              ultimately have "findFiance (engagements[m:=Some ?w]) w = Some m_w" using findFiance_first_is_Some false_front by simp
              with Some show ?thesis by simp
            qed
          qed
          moreover have "X_pre = engagements" using "1.prems"(1) "1.prems"(4) `i=0` by (simp del:GS'_arg_seq.simps)
          ultimately show ?thesis using married_better_trans by blast
        qed
      qed
    next
      case (Some m')
      with findFiance have "engagements!m' = Some ?w" by simp
      moreover from m findFreeMan have "engagements!m = None" by simp
      ultimately have "m' \<noteq> m" by auto
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
        from Some change "1.prems"(1) have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        hence "seq!1 = (engagements[m:=Some ?w, m':=None], ?next_prop_idxs)" by (simp del:GS'_arg_seq.simps)
        with seq_tl have distinct:"is_distinct (engagements[m:=Some ?w, m':=None])" using GS'_arg_seq_all_distinct "1.prems"(1-2) l_seq by blast
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with `i\<le>j` obtain j_1 where j_1:"j = Suc j_1" using Suc_le_D by auto
          from Suc seq_tl "1.prems"(3-4) have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X_pre, Y_pre)" by auto
          moreover from j_1 seq_tl "1.prems"(5-6) have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
          moreover from "1.prems"(7) Suc j_1 have "i_1 \<le> j_1" by fastforce
          ultimately show ?thesis using "1.IH"(2) non_terminal m Some change distinct by blast
        next
          case 0
          show ?thesis
          proof (cases j)
            case 0
            thus ?thesis using married_better_refl `i=0` "1.prems"(4-6) by simp
          next
            case (Suc j_1)
            have "0 \<le> j_1" by fast
            moreover from Suc "1.prems"(5-6) seq_tl have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
            moreover from GS'_arg_seq_length_gr_0 have "0 < length ?seq_tl" by fast
            moreover have "?seq_tl!0 = (engagements[m:=Some ?w, m':=None], ?next_prop_idxs)" by (simp del:GS'_arg_seq.simps)
            ultimately have "married_better w WPrefs (engagements[m:=Some ?w, m':=None]) X_post" using "1.IH"(2) non_terminal m Some change distinct by blast
            moreover have "married_better w WPrefs engagements (engagements[m:=Some ?w, m':=None])"
            proof cases
              assume "w = ?w"
              from findFiance_bound have "m' < length engagements" using Some by simp
              moreover from `w = ?w` `engagements!m' = Some ?w` have "engagements!m' = Some w" by simp
              ultimately have "\<forall>m''. (m'' \<noteq> m' \<and> m'' < length engagements) \<longrightarrow> engagements!m'' \<noteq> Some w" using "1.prems"(2) by (metis option.discI)
              with `w = ?w` have "\<forall>m''. (m'' \<noteq> m \<and> m'' < length (engagements[m:=Some ?w, m':=None])) \<longrightarrow> (engagements[m:=Some ?w, m':=None])!m'' \<noteq> Some w" by (metis (full_types) length_list_update nth_list_update nth_list_update_neq option.discI)
              moreover from findFreeMan_bound m have m_bound:"m < length (engagements[m:=Some ?w, m':=None])" by simp
              ultimately have "\<forall>m''<m. (engagements[m:=Some ?w, m':=None])!m'' \<noteq> Some w" by simp
              moreover have "(engagements[m:=Some ?w, m':=None])!m = Some w" using `w = ?w` `m' \<noteq> m` m_bound by auto
              ultimately have "findFiance (engagements[m:=Some ?w, m':=None]) w = Some m" using m_bound findFiance_first_is_Some by simp
              moreover from `w = ?w` Some have "findFiance engagements w = Some m'" by simp
              moreover from `w = ?w` change have "prefers w WPrefs m m'" by simp
              ultimately show ?thesis using `m' \<noteq> m` by simp
            next
              assume "w \<noteq> ?w"
              show ?thesis
              proof (cases "findFiance engagements w")
                case None
                thus ?thesis by simp
              next
                case (Some m_w)
                hence "engagements!m_w = Some w" and "m_w < length engagements" using findFiance findFiance_bound by auto
                with `engagements!m = None` `engagements!m' = Some ?w` `w \<noteq> ?w` have "m \<noteq> m_w" and "m' \<noteq> m_w" by auto
                from "1.prems"(2) `engagements!m_w = Some w` `m_w < length engagements` have "\<forall>m''.(m''\<noteq>m_w \<and> m'' < length engagements) \<longrightarrow> engagements!m'' \<noteq> Some w" by (metis option.discI)
                hence "\<forall>m''.(m''\<noteq>m_w \<and> m'' < length (engagements[m:=Some ?w, m':=None])) \<longrightarrow> engagements!m'' \<noteq> Some w" by simp
                hence "\<forall>m''.(m''\<noteq>m_w \<and> m'' < length (engagements[m:=Some ?w, m':=None])) \<longrightarrow> (engagements[m:=Some ?w, m':=None])!m'' \<noteq> Some w" using `w \<noteq> ?w` by (metis (full_types) length_list_update nth_list_update_eq nth_list_update_neq option.discI option.inject)
                hence "\<forall>m''<m_w. (engagements[m:=Some ?w, m':=None])!m'' \<noteq> Some w" using `m_w < length engagements` by simp
                moreover from `m' \<noteq> m_w` `m \<noteq> m_w` `m_w < length engagements` `engagements!m_w = Some w` have "(engagements[m:=Some ?w, m':=None])!m_w = Some w" by simp
                ultimately have "findFiance (engagements[m:=Some ?w, m':=None]) w = Some m_w" using `m_w < length engagements` findFiance_first_is_Some by simp
                with Some show ?thesis by simp
              qed
            qed
            moreover have "X_pre = engagements" using "1.prems"(1) "1.prems"(4) `i=0` by (simp del:GS'_arg_seq.simps)
            ultimately show ?thesis using married_better_trans by blast
          qed
        qed
      next
        assume no_change:"\<not>prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from Some no_change "1.prems"(1) have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with `i\<le>j` obtain j_1 where j_1:"j = Suc j_1" using Suc_le_D by auto
          from Suc seq_tl "1.prems"(3-4) have "i_1 < length ?seq_tl" and "?seq_tl!i_1 = (X_pre, Y_pre)" by auto
          moreover from j_1 seq_tl "1.prems"(5-6) have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
          moreover from "1.prems"(7) Suc j_1 have "i_1 \<le> j_1" by fastforce
          ultimately show ?thesis using "1.IH"(3) non_terminal m Some no_change "1.prems"(2) by blast
        next
          case 0
          show ?thesis
          proof (cases j)
            case 0
            thus ?thesis using `i=0` "1.prems"(4-6) married_better_refl by force
          next
            case (Suc j_1)
            have "0 \<le> j_1" by fast
            moreover from Suc "1.prems"(5-6) seq_tl have "j_1 < length ?seq_tl" and "?seq_tl!j_1 = (X_post, Y_post)" by auto
            moreover from GS'_arg_seq_length_gr_0 have "0 < length ?seq_tl" by fast
            moreover have "?seq_tl!0 = (engagements, ?next_prop_idxs)" by (simp del:GS'_arg_seq.simps)
            moreover have "X_pre = engagements" using "1.prems"(1) "1.prems"(4) `i=0` by (simp del:GS'_arg_seq.simps)
            ultimately show ?thesis using "1.IH"(3) non_terminal m Some no_change "1.prems"(2) by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_prev_prop_idx_same_or_1_less:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "Suc i < length seq" and seq_Suc_i:"seq!Suc i = (X, Y)" and seq_i:"seq!i = (X_prev, Y_prev)"
      and k_1:"k = Suc k_1" and "Y!m = k"
    shows "Y_prev!m = k \<or> (Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)"
proof -
  have "i \<noteq> length seq - 1" and i_bound:"i < length seq" using assms(2) by simp_all
  hence non_terminal:"\<not> is_terminal N X_prev Y_prev" using GS'_arg_seq_last_eq_terminal seq seq_i by blast
  then obtain m_prev where m_prev:"findFreeMan X_prev = Some m_prev" by blast
  let ?w = "MPrefs!m_prev!(Y_prev!m_prev)"
  let ?next_prop_idxs = "Y_prev[m_prev:=Suc(Y_prev!m_prev)]"
  show ?thesis
  proof (rule ccontr)
    assume asm:"\<not>(Y_prev!m = k \<or> (Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m))"
    have "Y = ?next_prop_idxs" using GS'_arg_seq_snd_step seq i_bound seq_i non_terminal m_prev seq_Suc_i by meson
    hence is_k:"?next_prop_idxs!m = k" using `Y!m=k` by simp
    show False
    proof cases
      assume "m = m_prev"
      with asm m_prev have "Y_prev!m \<noteq> k_1" by blast
      moreover from m_prev findFreeMan_bound non_terminal `m=m_prev` have "m < length Y_prev" by metis
      ultimately show False using `m=m_prev` is_k k_1 by simp
    next
      assume "m \<noteq> m_prev"
      with asm is_k show False by simp
    qed
  qed
qed

lemma GS'_arg_seq_exists_prev_prop_idx:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0)"
      and "i < length seq" and "seq!i = (X, Y)" 
      and k_1:"k = Suc k_1" and "m < N" and "Y!m = k"
    shows "\<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m"
proof (rule ccontr)
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    with seq assms(3-6) show False by (auto simp del:GS'_arg_seq.simps)
  qed
  assume asm:"\<not> (\<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)"
  have "\<lbrakk>j < i; seq!j = (X_prev, Y_prev)\<rbrakk> \<Longrightarrow> Y_prev!m = k" for j X_prev Y_prev
  proof (induction "i-1 - j" arbitrary: j X_prev Y_prev)
    case 0
    hence "i = Suc j" by fastforce
    hence "Y_prev!m = k \<or> (Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)" using GS'_arg_seq_prev_prop_idx_same_or_1_less assms "0.prems"(2) by blast
    with asm "0.prems" show ?case by blast
  next
    case (Suc d)
    from Suc.hyps(2) have "Suc j < i" by linarith
    moreover from Suc.hyps(2) have "d = i - 1 - Suc j" by auto
    moreover obtain X' Y' where seq_Suc_j:"seq!Suc j = (X', Y')" by fastforce
    ultimately have "Y'!m = k" using Suc.hyps(1) by blast
    moreover from `Suc j < i` assms(2) have "Suc j < length seq" by auto
    ultimately have "Y_prev!m = k \<or> (Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)" using GS'_arg_seq_prev_prop_idx_same_or_1_less seq seq_Suc_j Suc.prems(2) k_1 by blast
    with asm Suc.prems show ?case by blast
  qed
  moreover have "0 < i \<and> seq!0 = (engagements, replicate N 0)" using `i\<noteq>0` seq by (simp del:GS'_arg_seq.simps)
  ultimately have "(replicate N 0)!m = k" by blast
  thus False using k_1 `m < N` by simp
qed

lemma GS'_arg_seq_all_prev_prop_idxs_exist: "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0); i < length seq; seq!i = (X, prop_idxs); m < N; prop_idxs!m = k; prop_idx < k\<rbrakk> \<Longrightarrow> \<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = prop_idx \<and> findFreeMan X_prev = Some m"
proof (induction "k-1 - prop_idx" arbitrary: prop_idx)
  case 0
  from "0.hyps" `prop_idx < k` have "k = Suc prop_idx" by auto
  thus ?case using GS'_arg_seq_exists_prev_prop_idx "0.prems"(1-5) by blast
next
  case (Suc d)
  from Suc.hyps(2) have "Suc prop_idx < k" and "d = k-1 - Suc prop_idx" by simp_all
  then obtain j X_prev Y_prev where seq_j:"j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = Suc prop_idx \<and> findFreeMan X_prev = Some m" using Suc.hyps(1) Suc.prems(1-5) by blast
  hence j_bound:"j < length seq" using Suc.prems(2) by linarith
  then obtain j' X_pp Y_pp where "j' < j \<and> seq!j' = (X_pp, Y_pp) \<and> Y_pp!m = prop_idx \<and> findFreeMan X_pp = Some m" using GS'_arg_seq_exists_prev_prop_idx Suc.prems(1) j_bound seq_j `m<N` by blast
  moreover hence "j' < i" using seq_j by linarith
  ultimately show ?case by auto
qed

lemma GS'_arg_seq_married_once_proposed_to:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "Suc i < length seq" and seq_i:"seq!i = (X, Y)" and "seq!Suc i = (X_next, Y_next)"
      and m:"findFreeMan X = Some m" and w:"w = MPrefs!m!(Y!m)"
    shows "findFiance X_next w \<noteq> None"
proof -
  from findFreeMan_bound m have m_bound:"m < length X" by blast
  from assms(2) have i_bound:"i < length seq" and "i \<noteq> length seq - 1" by simp_all
  hence non_terminal:"\<not>is_terminal N X Y" using GS'_arg_seq_last_eq_terminal seq seq_i by blast
  show ?thesis
  proof (cases "findFiance X w")
    case None
    hence "X_next = X[m:=Some w]" using GS'_arg_seq_step_1 assms i_bound non_terminal by auto
    with m_bound have "Some w \<in> set X_next" by (simp add:set_update_memI)
    thus ?thesis using findFiance_None by simp
  next
    case (Some m')
    show ?thesis
    proof cases
      assume "prefers w WPrefs m m'"
      hence "X_next = X[m:=Some w, m':=None]" using GS'_arg_seq_step_2 assms i_bound non_terminal Some by auto
      moreover from Some m findFreeMan findFiance have "m \<noteq> m'" by fastforce
      ultimately have "Some w \<in> set X_next" using m_bound by (simp add: list_update_swap set_update_memI)
      thus ?thesis using findFiance_None by simp
    next
      assume "\<not>prefers w WPrefs m m'"
      hence "X_next = X" using GS'_arg_seq_step_3 assms i_bound non_terminal Some by auto
      thus ?thesis using Some by simp
    qed
  qed
qed

lemma GS'_arg_seq_any_man_done_proposing_means_done:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)" and "m < N" and "prop_idxs!m = N"
    shows "findFreeMan engagements = None"
proof -
  let ?Some_Ns = "map Some [0 ..< N]"
  from perm_PPref[OF assms(2) `m<N`] have MPref:"MPrefs!m <~~> [0 ..< N]" .
  have "\<forall>prop_idx < length (MPrefs!m). findFiance engagements (MPrefs!m!prop_idx) \<noteq> None"
    apply (rule)
  proof
    fix prop_idx
    let ?w = "MPrefs!m!prop_idx"
    assume "prop_idx < length (MPrefs!m)"
    also have "... = length [0 ..< N]" using MPref perm_length by blast
    also have "... = N" by simp
    finally have "prop_idx < N" .
    then obtain j X_prev Y_prev where j:"j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = prop_idx \<and> findFreeMan X_prev = Some m" using GS'_arg_seq_all_prev_prop_idxs_exist seq assms(3-6) by blast
    moreover hence Suc_j_bound:"Suc j < length seq" using assms(3) by linarith
    moreover obtain X' Y' where seq_Suc_j:"seq!Suc j = (X', Y')" by fastforce
    ultimately have "findFiance X' ?w \<noteq> None" using GS'_arg_seq_married_once_proposed_to seq by blast
    moreover have "married_better ?w WPrefs X' engagements"
    proof -
      from j have "Suc j \<le> i" by linarith
      moreover have "is_distinct (replicate N None)" by simp
      ultimately show ?thesis using GS'_arg_seq_all_w_marry_better seq assms(3-4) Suc_j_bound seq_Suc_j by blast
    qed
    ultimately show "findFiance engagements ?w \<noteq> None" using married_better_imp by blast
  qed
  hence "\<forall>w \<in> set [0 ..< N]. findFiance engagements w \<noteq> None" by (metis in_set_conv_nth MPref perm_set_eq)
  hence "set ?Some_Ns \<subseteq> set engagements" using findFiance_Some by auto
  moreover have "card (set ?Some_Ns) = N"
  proof -
    have "distinct (xs::nat list) \<Longrightarrow> distinct (map Some xs)" for xs
      apply (induction xs)
      by auto
    moreover have "distinct [0 ..< N]" by simp
    ultimately have "distinct ?Some_Ns" by blast
    moreover have "length ?Some_Ns = N" by simp
    ultimately show ?thesis by (metis distinct_card)
  qed
  moreover have "card (set engagements) \<le> N"
  proof -
    have "card (set engagements) \<le> length engagements" by (simp add:card_length)
    also have "... = length (replicate N (None::woman option))" using GS'_arg_seq_length_fst[OF seq assms(3-4)] . 
    also have "... = N" by simp
    finally show ?thesis .
  qed
  moreover have "finite (set engagements)" by simp
  ultimately have "set ?Some_Ns = set engagements" by (metis card_seteq)
  with findFreeMan_None show ?thesis by auto
qed

lemma GS'_arg_seq_prop_idx_bound:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)" and "m < N"
    shows "prop_idxs!m \<le> N"
proof (rule ccontr)
  assume "\<not>prop_idxs!m \<le> N"
  then obtain k where "prop_idxs!m = k" and "N < k" by simp
  from GS'_arg_seq_all_prev_prop_idxs_exist[OF seq assms(3-5) this] obtain j X_prev Y_prev where
    j:"j < i \<and> seq!j = (X_prev, Y_prev) \<and> Y_prev!m = N \<and> findFreeMan X_prev = Some m" by blast
  hence "j < length seq" using assms(3) by linarith
  from GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1-2) this _ `m<N`] j
  show False by simp
qed

lemma GS'_arg_seq_prop_idx_bound_non_terminal:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)"
      and "m < N" and "\<not>is_terminal N engagements prop_idxs"
    shows "prop_idxs!m < N"
proof (rule ccontr)
  assume "\<not>prop_idxs!m < N"
  with GS'_arg_seq_prop_idx_bound[OF assms(1-5)]
  have "prop_idxs!m = N" by linarith
  with GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1-5)] assms(6)
  show False by blast
qed

lemma GS'_arg_seq_N_imp_prev_bump:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and seq_i:"seq!i = (engagements, prop_idxs)"
      and "m < N" and "prop_idxs!m = N"
    shows "\<exists>i_1 N_1 X_prev Y_prev. i = Suc i_1 \<and> N = Suc N_1 \<and> seq!i_1 = (X_prev, Y_prev) \<and> Y_prev!m = N_1 \<and> findFreeMan X_prev = Some m"
proof -
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    with seq seq_i assms(6) have "(replicate N 0)!m = N" by (simp del:GS'_arg_seq.simps)
    with `m<N` show False by fastforce
  qed
  then obtain i_1 where i_1:"i = Suc i_1" using not0_implies_Suc by blast
  from i_1 assms(3) have i_1_bound:"i_1 < length seq" by linarith
  obtain X_prev Y_prev where seq_i_1:"seq!i_1 = (X_prev, Y_prev)" by fastforce
  obtain N_1 where N_1:"N = Suc N_1" using `m<N` by (metis Nat.lessE)

  from i_1 GS'_arg_seq_any_man_done_proposing_means_done[OF assms]
    GS'_arg_seq_last_eq_terminal[OF seq assms(3-4)]
    GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1-2) i_1_bound seq_i_1 `m<N`]
    GS'_arg_seq_last_eq_terminal[OF seq i_1_bound seq_i_1]
  have "Y_prev!m \<noteq> N" by force
  with GS'_arg_seq_prev_prop_idx_same_or_1_less[OF seq _ _ seq_i_1 N_1 assms(6)] i_1 assms(3-4) N_1 seq_i_1
  show ?thesis by blast
qed

theorem GS'_arg_seq_never_reaches_NxN:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)"
    shows "sum_list prop_idxs < N * N"
proof (rule ccontr)
  assume asm:"\<not> sum_list prop_idxs < N * N"
  obtain N_1 where N_1:"N = Suc N_1" using `N \<ge> 2` numeral_eq_Suc Suc_le_D by fastforce
  have l_prop_idxs:"length prop_idxs = N" using GS'_arg_seq_length_snd[OF seq assms(4-5)] by simp
  have sum_bound:"\<forall>m < length prop_idxs. prop_idxs!m \<le> N \<Longrightarrow> sum_list prop_idxs \<le> length prop_idxs * N" for prop_idxs N
    apply (induction prop_idxs)
     apply simp
    by fastforce
  have "\<exists>m < N. prop_idxs!m \<ge> N"
  proof (rule ccontr)
    assume "\<not>(\<exists>m < N. prop_idxs!m \<ge> N)"
    hence "\<forall>m < length prop_idxs. prop_idxs!m \<le> N_1" using l_prop_idxs N_1 by auto
    from sum_bound[OF this] have "sum_list prop_idxs \<le> N * N_1" using l_prop_idxs by blast
    thus False using asm N_1 by simp
  qed
  then obtain m where "m < N \<and> prop_idxs!m \<ge> N" by blast
  with GS'_arg_seq_prop_idx_bound[OF assms(1-2) assms(4-5)]
  have m:"m < N \<and> prop_idxs!m = N" by fastforce
  with GS'_arg_seq_N_imp_prev_bump[OF assms(1-2) assms(4-5)] N_1
  obtain i_1 X_prev Y_prev where i_1:"i = Suc i_1 \<and> seq!i_1 = (X_prev, Y_prev) 
            \<and> Y_prev!m = N_1 \<and> findFreeMan X_prev = Some m" by blast
  hence i_1_bound:"i_1 < length seq" using assms(4) by linarith

  let ?prop_idxs' = "prop_idxs[m:=N_1]"
  have "\<lbrakk>m' < N; m' \<noteq> m\<rbrakk> \<Longrightarrow> prop_idxs!m' \<le> N_1" for m'
  proof (rule ccontr)
    assume "\<not> prop_idxs!m' \<le> N_1" and "m' < N" and "m' \<noteq> m"
    hence "prop_idxs!m' \<ge> N" using N_1 by force
    with GS'_arg_seq_prop_idx_bound[OF assms(1-2) assms(4-5) `m'<N`]
    have "prop_idxs!m' = N" by fastforce
    from GS'_arg_seq_N_imp_prev_bump[OF assms(1-2) assms(4-5) `m'<N` this]
      GS'_arg_seq_N_imp_prev_bump[OF assms(1-2) assms(4-5)] m `m'\<noteq>m`
    show False by auto
  qed
  moreover from m l_prop_idxs have m_bound:"m < length prop_idxs" by presburger
  moreover have "N_1 \<le> N_1" by simp
  ultimately have "\<forall>m' < N. ?prop_idxs'!m' \<le> N_1" by (metis nth_list_update)
  with l_prop_idxs have "\<forall>m' < length ?prop_idxs'. ?prop_idxs'!m' \<le> N_1" by auto
  from sum_bound[OF this] l_prop_idxs have "sum_list ?prop_idxs' \<le> N * N_1" by fastforce
  moreover have "sum_list ?prop_idxs' = sum_list prop_idxs + N_1 - N" using sum_list_update[OF m_bound] m by presburger
  ultimately have "sum_list prop_idxs \<le> Suc (N * N_1)" using N_1 by linarith
  also have "... < N * N" using N_1 `N\<ge>2` by fastforce
  finally show False using asm by simp
qed

lemma GS'_arg_seq_all_bounded:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0); is_valid_pref_matrix N MPrefs; i < length seq; seq!i = (engagements, prop_idxs)\<rbrakk> \<Longrightarrow> is_bounded engagements"
proof (induction i arbitrary:engagements prop_idxs)
  case 0
  hence "engagements = (replicate N None)" by (simp del:GS'_arg_seq.simps)
  thus ?case by simp
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  from Suc.prems(3) have i_bound:"i < length seq" and "i \<noteq> length seq - 1" by simp_all
  hence non_terminal:"\<not>is_terminal N X_prev Y_prev" using GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) i_bound seq_i] by meson
  then obtain m where m:"findFreeMan X_prev = Some m" by blast
  let ?w = "MPrefs!m!(Y_prev!m)"
  from findFreeMan_bound[OF m] GS'_arg_seq_length_fst[OF Suc.prems(1) i_bound seq_i]
  have "m < N" by simp
  from perm_PPref[OF Suc.prems(2) this] have perm:"MPrefs!m <~~> [0 ..< N]" .
  from perm_length[OF this] have "length (MPrefs!m) = N" by fastforce
  with GS'_arg_seq_prop_idx_bound_non_terminal[OF Suc.prems(1-2) i_bound seq_i `m<N` non_terminal]
  have "?w \<in> set (MPrefs!m)" by simp
  with perm in_perm_upt have "?w < N" by blast
  from GS'_arg_seq_length_fst[OF Suc.prems(1) i_bound seq_i] have l_prev:"length X_prev = N" by fastforce
  from GS'_arg_seq_length_fst[OF Suc.prems(1) Suc.prems(3-4)] have l:"length engagements = N" by fastforce
  from Suc.IH[OF Suc.prems(1-2) i_bound seq_i] have IH:"is_bounded X_prev" .
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    from GS'_arg_seq_step_1[OF Suc.prems(1) i_bound seq_i non_terminal m _ None] Suc.prems(4)
    have "engagements = X_prev[m:=Some ?w]" by simp
    with `?w<N` `m<N` IH l l_prev show ?thesis by (metis nth_list_update option.sel)
  next
    case (Some m')
    show ?thesis
    proof cases
      assume "prefers ?w WPrefs m m'"
      from GS'_arg_seq_step_2[OF Suc.prems(1) i_bound seq_i non_terminal m _ Some this] Suc.prems(4)
      have "engagements = X_prev[m:=Some ?w, m':=None]" by simp
      thus ?thesis using IH findFiance_bound[OF Some] `?w<N` `m<N` l l_prev by (metis length_list_update nth_list_update option.sel)
    next
      assume "\<not>prefers ?w WPrefs m m'"
      from GS'_arg_seq_step_3[OF Suc.prems(1) i_bound seq_i non_terminal m _ Some this] Suc.prems(4)
      show ?thesis using IH by simp
    qed
  qed
qed

theorem is_matching:
  assumes "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
  shows "(Gale_Shapley MPrefs WPrefs) <~~> map Some [0..<N]"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  let ?i = "length ?seq - 1"
  from GS'_arg_seq_length_gr_0 have i_bound:"?i < length ?seq"
    using diff_less zero_less_one by blast
  obtain X Y where seq_i:"?seq!?i = (X, Y)" by fastforce

  from GS'_arg_seq_length_fst[OF _ i_bound seq_i]
  have l:"length X = N" by fastforce

  from length_PPrefs[OF assms(1)]
  have "Gale_Shapley MPrefs WPrefs
     = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by simp
  also have "... = X" using GS'_arg_seq_computes_GS'[OF _ seq_i] by blast
  finally have result:"Gale_Shapley MPrefs WPrefs = X" .

  have "\<forall>m < length X. X!m \<noteq> None"
  proof -
    from GS'_arg_seq_last_eq_terminal[OF _ i_bound seq_i]
    have "is_terminal N X Y" by metis
    moreover have "length X = length Y"
      using GS'_arg_seq_length_snd[OF _ i_bound seq_i] l by fastforce
    moreover have "sum_list Y < N * N"
      using GS'_arg_seq_never_reaches_NxN[OF _ assms i_bound seq_i] by simp
    ultimately have "findFreeMan X = None" by simp
    with findFreeMan_None show ?thesis by (metis nth_mem)
  qed
  moreover have "is_distinct X"
  proof -
    have "is_distinct (replicate N None)" by simp
    from GS'_arg_seq_all_distinct[OF _ this i_bound seq_i] show ?thesis by blast
  qed
  moreover have "is_bounded X" using GS'_arg_seq_all_bounded[OF _ assms(1) i_bound seq_i] by simp
  ultimately show ?thesis using is_matching_intro result l by blast
qed
end
