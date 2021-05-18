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
lemma perm_PPref:"\<lbrakk>is_valid_pref_matrix N PPrefs; p < N\<rbrakk> \<Longrightarrow> PPrefs!p <~~> [0 ..< N]" 
  using is_perm nth_mem by fastforce
lemma length_PPref:"\<lbrakk>is_valid_pref_matrix N PPrefs; p < N\<rbrakk> \<Longrightarrow> length (PPrefs!p) = N" 
  using perm_length[OF perm_PPref[of N PPrefs p]] by simp
lemma PPref_inject:
  assumes "is_valid_pref_matrix N PPrefs" and "p < N" and "idx1 < N" and "idx2 < N" 
      and "PPrefs!p!idx1 = PPrefs!p!idx2"
    shows "idx1 = idx2"
proof -
  from length_PPref[OF assms(1,2)] assms(3,4) 
  have "idx1 < length (PPrefs!p)" and "idx2 < length (PPrefs!p)" by simp_all
  moreover from perm_distinct_iff[OF perm_PPref[OF assms(1,2)]] have "distinct (PPrefs!p)" by simp
  ultimately show ?thesis using nth_eq_iff_index_eq assms(5) by blast
qed

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
  proof (cases "term = x")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    with Cons.prems obtain idx' where "find_idx term xs = Some idx'" by fastforce
    with Cons.IH[OF this] False Cons.prems show ?thesis by simp
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
  from Nil.prems(1) show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "term = x")
    case True
    thus ?thesis using Cons.prems by simp
  next
    case False
    with Cons.prems(1) obtain idx_1 where idx_1:"find_idx term xs = Some idx_1" by fastforce
    with Cons.prems(1) False have idx:"idx = Suc idx_1" by simp
    show ?thesis
    proof (cases idx')
      case 0
      with False show ?thesis by simp
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
  proof (cases "term = x")
    case True
    thus ?thesis using Cons.prems by simp
  next
    case False
    with Cons.prems obtain idx_1 where "find_idx term xs = Some idx_1" by fastforce
    with Cons.IH[OF this] Cons.prems False show ?thesis by fastforce
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

fun prefers::"person \<Rightarrow> pref_matrix \<Rightarrow> person \<Rightarrow> person \<Rightarrow> bool" where
"prefers p PPrefs p1 p2 = (
case find_idx p1 (PPrefs!p) of None \<Rightarrow> False |
                               Some idx_1 \<Rightarrow> (
  case find_idx p2 (PPrefs!p) of None \<Rightarrow> False |
                                 Some idx_2 \<Rightarrow> idx_1 < idx_2))"

lemma prefers_non_refl:"\<not>prefers p PPrefs p' p'"
  apply (cases "find_idx p' (PPrefs!p)")
  by auto

lemma prefers_trans:
  assumes 12:"prefers p PPrefs p1 p2" and 23:"prefers p PPrefs p2 p3"
  shows "prefers p PPrefs p1 p3"
proof -
  from 12 obtain idx_1 where idx_1:"find_idx p1 (PPrefs!p) = Some idx_1" by fastforce
  from 23 obtain idx_2 where idx_2:"find_idx p2 (PPrefs!p) = Some idx_2" by fastforce
  with 23 obtain idx_3 where idx_3:"find_idx p3 (PPrefs!p) = Some idx_3" by fastforce
  from 12 idx_1 idx_2 have "idx_1 < idx_2" by auto
  moreover from 23 idx_2 idx_3 have "idx_2 < idx_3" by auto
  ultimately show ?thesis using idx_1 idx_3 by fastforce
qed

lemma termination_aid:
  assumes "length engagements = length prop_idxs"
      and "findFreeMan engagements = Some m"
      and "next_prop_idxs = prop_idxs[m:=Suc(prop_idxs!m)]"
      and "sum_list prop_idxs < N * N"
    shows "N * N - sum_list next_prop_idxs < N * N - sum_list prop_idxs"
proof -
  from assms(1) findFreeMan_bound[OF assms(2)] have m_bound:"m < length prop_idxs" by presburger
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
  from this[OF m_bound] assms(3,4) show ?thesis by auto
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
proof (cases "is_terminal N engagements prop_idxs")
  case True
  thus ?thesis by auto
next
  case False
  then obtain m where "findFreeMan engagements = Some m" by blast
  thus ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma GS'_arg_seq_length_gr_0:
"length(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) > 0" using GS'_arg_seq_non_Nil by auto

lemma GS'_arg_seq_length_gr_1:
"\<not>is_terminal N engagements prop_idxs \<longleftrightarrow>
 length(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) > 1"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show ?thesis
  proof
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
        proof (cases "prefers ?w WPrefs m m'")
          case True
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs
                                    (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
          from non_terminal m Some True 
          have "length ?seq = Suc (length ?seq_tl)" by (simp add:Let_def)
          moreover from GS'_arg_seq_length_gr_0 have "length ?seq_tl > 0" by fast
          ultimately show ?thesis by linarith
        next
          case False
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
          from non_terminal m Some False
          have "length ?seq = Suc (length ?seq_tl)" by (simp add:Let_def)
          moreover from GS'_arg_seq_length_gr_0 have "length ?seq_tl > 0" by fast
          ultimately show ?thesis by linarith
        qed
      qed
    qed
  next
    show "length ?seq > 1 \<Longrightarrow> \<not>is_terminal N engagements prop_idxs"
    proof
      assume "is_terminal N engagements prop_idxs"
      hence "length ?seq = 1" by auto
      moreover assume "length ?seq > 1"
      ultimately show False by auto
    qed
  qed
qed

lemma GS'_arg_seq_0 [simp]:
"(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)!0 = (engagements, prop_idxs)"
proof (cases "is_terminal N engagements prop_idxs")
  case True
  thus ?thesis by fastforce
next
  case False
  moreover then obtain m where "findFreeMan engagements = Some m" by blast
  ultimately show ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma tl_i_1_eq:"\<lbrakk>i = Suc i_1; seq = x#xs; (seq!i) = X\<rbrakk> \<Longrightarrow> (xs!i_1) = X" by simp
lemma i_1_bound:"\<lbrakk>i = Suc i_1; seq = x#xs; i < length seq\<rbrakk> \<Longrightarrow> i_1 < length xs" by simp
lemma Suc_i_1_bound:"\<lbrakk>i = Suc i_1; seq = x#xs; Suc i < length seq\<rbrakk> \<Longrightarrow> Suc i_1 < length xs" by simp

lemma GS'_arg_seq_last_eq_terminal:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk>
   \<Longrightarrow> is_terminal N X Y \<longleftrightarrow> length seq = Suc i"
proof
  show "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y);
         is_terminal N X Y\<rbrakk> \<Longrightarrow> length seq = Suc i"
  proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq i rule:GS'_arg_seq.induct)
    case (1 N MPrefs WPrefs engagements prop_idxs)
    show ?case
    proof (cases i)
      case 0
      moreover hence "is_terminal N engagements prop_idxs"
        using "1.prems"(1,3,4) by (simp del:GS'_arg_seq.simps)
      ultimately show ?thesis using "1.prems"(1) by auto
    next
      case (Suc i_1)
      hence "length seq > 1" using "1.prems"(2) by auto
      hence non_terminal:"\<not> is_terminal N engagements prop_idxs"
        using "1.prems"(1) GS'_arg_seq_length_gr_1 by blast
      then obtain m where m:"findFreeMan engagements = Some m" by blast
      let ?w = "MPrefs!m!(prop_idxs!m)"
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        with "1.IH"(1)[OF _ _ m refl refl None refl i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4)] "1.prems"(1) non_terminal m Suc
        show ?thesis by (simp add:Let_def)
      next
        case (Some m')
        show ?thesis
        proof (cases "prefers ?w WPrefs m m'")
          case True
          with "1.IH"(2)[OF _ _ m refl refl Some True refl i_1_bound[OF Suc _ "1.prems"(2)]
              tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4)] "1.prems"(1) non_terminal m Some Suc
          show ?thesis by (simp add:Let_def) 
        next
          case False
          with "1.IH"(3)[OF _ _ m refl refl Some this refl i_1_bound[OF Suc _ "1.prems"(2)]
              tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4)] "1.prems"(1) non_terminal m Some Suc
          show ?thesis by (simp add:Let_def)
        qed
      qed
    qed
  qed
next
  show "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y);
         length seq = Suc i\<rbrakk> \<Longrightarrow> is_terminal N X Y"
  proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq i rule: GS'_arg_seq.induct)
    case (1 N MPrefs WPrefs engagements prop_idxs)
    show ?case
    proof (cases i)
      case 0
      with "1.prems"(4) have "\<not> length seq > 1" by presburger
      with "1.prems"(1) GS'_arg_seq_length_gr_1
      have "is_terminal N engagements prop_idxs" by presburger
      with "1.prems"(1,3) 0 show ?thesis by (simp del:GS'_arg_seq.simps)
    next
      case (Suc i_1)
      with "1.prems"(4) have "length seq > 1" by fastforce
      with "1.prems"(1) GS'_arg_seq_length_gr_1 
      have non_terminal:"\<not> is_terminal N engagements prop_idxs" by presburger
      then obtain m where m:"findFreeMan engagements = Some m" by blast
      let ?w = "MPrefs!m!(prop_idxs!m)"
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        with "1.IH"(1)[OF _ _ m refl refl None refl i_1_bound[OF Suc _ "1.prems"(2)] 
            tl_i_1_eq[OF Suc _ "1.prems"(3)]] Suc "1.prems"(4,1) non_terminal m 
        show ?thesis by (simp add:Let_def)
      next
        case (Some m')
        show ?thesis
        proof (cases "prefers ?w WPrefs m m'")
          case True
          with "1.IH"(2)[OF _ _ m refl refl Some True refl i_1_bound[OF Suc _ "1.prems"(2)]
              tl_i_1_eq[OF Suc _ "1.prems"(3)]] Suc "1.prems"(4,1) non_terminal m Some
          show ?thesis by (simp add:Let_def)
        next
          case False
          with "1.IH"(3)[OF _ _ m refl refl Some this refl i_1_bound[OF Suc _ "1.prems"(2)]
              tl_i_1_eq[OF Suc _ "1.prems"(3)]] Suc "1.prems"(4,1) non_terminal m Some
          show ?thesis by (simp add:Let_def)
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_same_endpoint:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk>
   \<Longrightarrow> Gale_Shapley' N MPrefs WPrefs X Y = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using "1.prems"(1,3) by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    hence "length seq > 1" using "1.prems"(2) by auto
    with "1.prems"(1) GS'_arg_seq_length_gr_1 
    have non_terminal:"\<not>is_terminal N engagements prop_idxs" by blast
    then obtain m where m:"findFreeMan engagements = Some m" by blast
    let ?w = "MPrefs!m!(prop_idxs!m)"
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      with "1.IH"(1)[OF _ _ m refl refl None refl i_1_bound[OF Suc _ "1.prems"(2)] 
          tl_i_1_eq[OF Suc _ "1.prems"(3)]] "1.prems"(1) non_terminal m
      show ?thesis by (simp add:Let_def)
    next
      case (Some m')
      show ?thesis
      proof (cases "prefers ?w WPrefs m m'")
        case True
        with "1.IH"(2)[OF _ _ m refl refl Some True refl i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)]] "1.prems"(1) non_terminal m Some
        show ?thesis by (simp add:Let_def)
      next
        case False
        with "1.IH"(3)[OF _ _ m refl refl Some this refl i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)]] "1.prems"(1) non_terminal m Some
        show ?thesis by (simp add:Let_def)
      qed
    qed
  qed
qed

theorem GS'_arg_seq_computes_GS':
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "length seq = Suc i" and "seq!i = (X, Y)"
    shows "X = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
proof -
  from assms(2) have i_bound:"i < length seq" by linarith
  from GS'_arg_seq_last_eq_terminal[OF assms(1) this assms(3)] assms(2)
  have "is_terminal N X Y" by presburger
  hence "X = Gale_Shapley' N MPrefs WPrefs X Y" by fastforce
  also have "... = Gale_Shapley' N MPrefs WPrefs engagements prop_idxs" 
    using GS'_arg_seq_same_endpoint[OF assms(1) i_bound assms(3)] by blast
  finally show ?thesis .
qed

lemma GS'_arg_seq_step_1:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; Suc i < length seq; seq!i = (X, Y); 
  findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = None\<rbrakk>
   \<Longrightarrow> seq!Suc i = (X[m:=Some w], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  from "1.prems"(2) have "length seq > 1" by linarith
  with "1.prems"(1) GS'_arg_seq_length_gr_1
  have non_terminal:"\<not>is_terminal N engagements prop_idxs" by presburger
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1,3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems"(1,4-6) non_terminal
    have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w]) (Y[m:=Suc(Y!m)])" 
      by (simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      with "1.IH"(1)[OF _ _ m_0 refl refl None refl Suc_i_1_bound[OF Suc _ "1.prems"(2)] 
          tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-6)] "1.prems"(1) non_terminal m_0 Suc 
      show ?thesis by (simp add:Let_def)
    next
      case (Some m')
      show ?thesis
      proof (cases "prefers ?w WPrefs m_0 m'")
        case True
        with "1.IH"(2)[OF _ _ m_0 refl refl Some True refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-6)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      next
        case False
        with "1.IH"(3)[OF _ _ m_0 refl refl Some this refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-6)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      qed
    qed
  qed
qed

lemma GS'_arg_seq_step_2:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; Suc i < length seq; seq!i = (X, Y); 
  findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; prefers w WPrefs m m'\<rbrakk>
   \<Longrightarrow> seq!Suc i = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  from "1.prems"(2) have "length seq > 1" by linarith
  with "1.prems"(1) GS'_arg_seq_length_gr_1
  have non_terminal:"\<not>is_terminal N engagements prop_idxs" by presburger
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1,3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems"(1,4-7) non_terminal
    have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w, m':=None]) (Y[m:=Suc(Y!m)])" 
      by (auto simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      with "1.IH"(1)[OF _ _ m_0 refl refl None refl Suc_i_1_bound[OF Suc _ "1.prems"(2)] 
          tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Suc 
      show ?thesis by (simp add:Let_def)
    next
      case (Some m')
      show ?thesis
      proof (cases "prefers ?w WPrefs m_0 m'")
        case True
        with "1.IH"(2)[OF _ _ m_0 refl refl Some True refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      next
        case False
        with "1.IH"(3)[OF _ _ m_0 refl refl Some this refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      qed
    qed
  qed
qed

lemma GS'_arg_seq_step_3:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; Suc i < length seq; seq!i = (X, Y); 
  findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; \<not>prefers w WPrefs m m'\<rbrakk>
   \<Longrightarrow> seq!Suc i = (X, Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  from "1.prems"(2) have "length seq > 1" by linarith
  with "1.prems"(1) GS'_arg_seq_length_gr_1
  have non_terminal:"\<not>is_terminal N engagements prop_idxs" by presburger
  then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by blast
  let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1,3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems"(1,4-7) non_terminal
    have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs X (Y[m:=Suc(Y!m)])" by (auto simp add:Let_def)
    with 0 show ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Suc i_1)
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      with "1.IH"(1)[OF _ _ m_0 refl refl None refl Suc_i_1_bound[OF Suc _ "1.prems"(2)] 
          tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Suc 
      show ?thesis by (simp add:Let_def)
    next
      case (Some m')
      show ?thesis
      proof (cases "prefers ?w WPrefs m_0 m'")
        case True
        with "1.IH"(2)[OF _ _ m_0 refl refl Some True refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      next
        case False
        with "1.IH"(3)[OF _ _ m_0 refl refl Some this refl Suc_i_1_bound[OF Suc _ "1.prems"(2)]
            tl_i_1_eq[OF Suc _ "1.prems"(3)] "1.prems"(4-7)] "1.prems"(1) non_terminal m_0 Some Suc
        show ?thesis by (simp add:Let_def)
      qed
    qed
  qed
qed

lemma GS'_arg_seq_snd_step:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "Suc i < length seq" and "seq!i = (X, Y)"
      and "findFreeMan X = Some m"
      and "seq!Suc i = (X_next, Y_next)"
    shows "Y_next = Y[m:=Suc(Y!m)]"
proof (cases "findFiance X (MPrefs!m!(Y!m))")
  case None
  from GS'_arg_seq_step_1[OF assms(1-4) refl None] assms(5) show ?thesis by auto
next
  case (Some m')
  show ?thesis
  proof (cases "prefers (MPrefs!m!(Y!m)) WPrefs m m'")
    case True
    from GS'_arg_seq_step_2[OF assms(1-4) refl Some True] assms(5) show ?thesis by auto
  next
    case False
    from GS'_arg_seq_step_3[OF assms(1-4) refl Some this] assms(5) show ?thesis by auto
  qed
qed

lemma GS'_arg_seq_length_fst:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk>
   \<Longrightarrow> length X = length engagements"
proof (induction i arbitrary:X Y)
  case 0
  from "0.prems"(1,3) show ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] this] Suc.prems(2)
  obtain m where m:"findFreeMan X_prev = Some m" by auto
  from Suc.IH[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] seq_i]
  have IH:"length X_prev = length engagements" .
  let ?w = "MPrefs!m!(Y_prev!m)"
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    from GS'_arg_seq_step_1[OF Suc.prems(1-2) seq_i m refl None] IH Suc.prems(3)
    show ?thesis by auto
  next
    case (Some m')
    show ?thesis
    proof (cases "prefers ?w WPrefs m m'")
      case True
      from GS'_arg_seq_step_2[OF Suc.prems(1-2) seq_i m refl Some True] IH Suc.prems(3)
      show ?thesis by auto
    next
      case False
      from GS'_arg_seq_step_3[OF Suc.prems(1-2) seq_i m refl Some this] IH Suc.prems(3)
      show ?thesis by auto
    qed
  qed
qed

lemma GS'_arg_seq_length_snd:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y)\<rbrakk>
   \<Longrightarrow> length Y = length prop_idxs"
proof (induction i arbitrary: X Y)
  case 0
  from "0.prems"(1,3) show ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] this] Suc.prems(2)
  obtain m where "findFreeMan X_prev = Some m" by auto
  from GS'_arg_seq_snd_step[OF Suc.prems(1-2) seq_i this Suc.prems(3)] 
    Suc.IH[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] seq_i] show ?case by auto
qed

abbreviation is_distinct where
"is_distinct engagements \<equiv> \<forall>m1 < length engagements. \<forall>m2 < length engagements. 
                           m1 \<noteq> m2 \<longrightarrow> engagements!m1 = None \<or> engagements!m1 \<noteq> engagements!m2"

abbreviation is_bounded where
"is_bounded engagements \<equiv> \<forall>m < length engagements. 
                          engagements!m \<noteq> None \<longrightarrow> the (engagements!m) < length engagements"

lemma is_matching_intro:
  assumes noFree:"\<forall>m < length engagements. engagements!m \<noteq> None"
      and "is_distinct engagements" and "is_bounded engagements"
    shows "engagements <~~> map Some [0 ..< length engagements]"
proof -
  let ?engagements = "map the engagements"
  let ?N = "length engagements"
  from assms(3) noFree have "\<forall>m < length ?engagements. ?engagements!m < ?N" by fastforce
  hence "\<forall>w \<in> set ?engagements. w < ?N" by (metis in_set_conv_nth)
  hence subset:"set ?engagements \<subseteq> set [0 ..< ?N]" using in_upt by blast

  from noFree assms(2) have "\<forall>m1 < length engagements. \<forall>m2 < length engagements.
                             m1 \<noteq> m2 \<longrightarrow> engagements!m1 \<noteq> engagements!m2" by blast
  hence "\<forall>m1 < length engagements. \<forall>m2 < length engagements.
         m1 \<noteq> m2 \<longrightarrow> the (engagements!m1) \<noteq> the (engagements!m2)"
    using noFree by (metis option.expand)
  hence distinct:"distinct ?engagements" by (simp add: distinct_conv_nth)
  hence "card (set ?engagements) = length ?engagements" by (metis distinct_card)
  also have "... = ?N" by simp
  finally have "card (set ?engagements) = ?N" .
  moreover have "finite (set [0 ..< ?N])"
            and "card (set [0 ..< ?N]) = ?N" and "distinct [0 ..< ?N]" by simp_all
  ultimately have "mset ?engagements = mset [0 ..< ?N]"
    using subset distinct by (metis card_subset_eq set_eq_iff_mset_eq_distinct)
  moreover have "mset (xs::nat list) = mset ys
             \<Longrightarrow> mset (map Some xs) = mset (map Some ys)" for xs ys by simp
  ultimately have "mset (map Some ?engagements) = mset (map Some [0..<?N])" by meson
  moreover from noFree have "engagements = map Some ?engagements" by (simp add:nth_equalityI)
  ultimately show ?thesis by (metis mset_eq_perm)
qed

lemma GS'_arg_seq_all_distinct:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; is_distinct engagements;
  i < length seq; seq!i = (X, Y)\<rbrakk> \<Longrightarrow> is_distinct X"
proof (induction i arbitrary: X Y)
  case 0
  from "0.prems"(1-2,4) show ?case by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  from Suc.IH[OF Suc.prems(1-2) Suc_lessD[OF Suc.prems(3)] this] have IH:"is_distinct X_prev" .
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) Suc_lessD[OF Suc.prems(3)] seq_i] Suc.prems(3)
  obtain m where m:"findFreeMan X_prev = Some m" by auto
  let ?w = "MPrefs!m!(Y_prev!m)"
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    hence "\<forall>m < length X_prev. X_prev!m \<noteq> Some ?w" by (metis nth_mem findFiance_None)
    with IH have "is_distinct (X_prev[m:=Some ?w])" 
      by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
    with GS'_arg_seq_step_1[OF Suc.prems(1,3) seq_i m refl None] Suc.prems(4) show ?thesis by simp
  next
    case (Some m')
    show ?thesis
    proof (cases "prefers ?w WPrefs m m'")
      case True
      from findFiance[OF Some] findFiance_bound[OF Some] IH
      have "\<forall>m < length X_prev. m \<noteq> m' \<longrightarrow> X_prev!m \<noteq> Some ?w" by fastforce
      hence "is_distinct (X_prev[m:=Some ?w, m':=None])" 
        using IH by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
      with GS'_arg_seq_step_2[OF Suc.prems(1,3) seq_i m refl Some True] Suc.prems(4) 
      show ?thesis by simp
    next
      case False
      from GS'_arg_seq_step_3[OF Suc.prems(1,3) seq_i m refl Some this] Suc.prems(4) IH
      show ?thesis by simp
    qed
  qed
qed

fun married_better::"woman \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> matching \<Rightarrow> bool" where
"married_better w WPrefs eng_1 eng_2 = (case findFiance eng_1 w of None \<Rightarrow> True | Some m_1 \<Rightarrow> (
                                          case findFiance eng_2 w of None \<Rightarrow> False | Some m_2 \<Rightarrow> (
                                            m_1 = m_2 \<or> prefers w WPrefs m_2 m_1)))"

lemma married_better_refl:"married_better w WPrefs eng eng"
  apply (cases "findFiance eng w")
  by simp_all

lemma married_better_imp:
"\<lbrakk>findFiance eng_1 w = Some m_1; married_better w WPrefs eng_1 eng_2\<rbrakk>
   \<Longrightarrow> \<exists>m_2. findFiance eng_2 w = Some m_2 \<and> (m_1 = m_2 \<or> prefers w WPrefs m_2 m_1)"
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
    where "findFiance eng_2 w = Some m_2" 
      and 12:"m_1 = m_2 \<or> prefers w WPrefs m_2 m_1" by blast
  from married_better_imp[OF this(1) 23] obtain m_3
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
      using Some m_3 12 prefers_trans[OF _ 12] by simp_all
  qed
qed

lemma GS'_arg_seq_findFiance_1:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs" 
      and "Suc i < length seq" and "seq!i = (X, Y)" and "seq!Suc i = (X_next, Y_next)"
      and "findFreeMan X = Some m" and "w = MPrefs!m!(Y!m)"
      and "findFiance X w = None"
    shows "findFiance X_next w = Some m"
proof -
  from findFreeMan_bound[OF assms(5)] have m_bound:"m < length X" .

  from assms(7) findFiance_None have "\<forall>m<length X. X!m \<noteq> Some w" by (metis nth_mem)
  with m_bound have "\<forall>m'<m. X!m' \<noteq> Some w" by fastforce
  moreover have "X[m:=Some w]!m = Some w" using m_bound by simp
  ultimately have "findFiance (X[m:=Some w]) w = Some m" 
    using findFiance_first_is_Some m_bound by simp
  with GS'_arg_seq_step_1[OF assms(1-3,5-7)] assms(4) show ?thesis by simp
qed

lemma GS'_arg_seq_findFiance_2:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs" and "is_distinct engagements"
      and "Suc i < length seq" and "seq!i = (X, Y)" and "seq!Suc i = (X_next, Y_next)"
      and "findFreeMan X = Some m" and "w = MPrefs!m!(Y!m)"
      and "findFiance X w = Some m'" and "prefers w WPrefs m m'"
    shows "findFiance X_next w = Some m"
proof -
  from findFiance[OF assms(8)] findFreeMan[OF assms(6)] have "m' \<noteq> m" by fastforce
  from findFiance[OF assms(8)] findFiance_bound[OF assms(8)] 
    GS'_arg_seq_all_distinct[OF assms(1,2) Suc_lessD[OF assms(3)] assms(4)]
  have "\<forall>m''. (m''\<noteq>m' \<and> m''<length X) \<longrightarrow> X!m'' \<noteq> Some w" by fastforce
  hence "\<forall>m''<length X. X[m':=None]!m'' \<noteq> Some w" 
    using findFiance_bound[OF assms(8)] by (simp add:nth_list_update)
  hence "\<forall>m''<m. X[m:=Some w, m':=None]!m'' \<noteq> Some w" 
    using `m'\<noteq>m` findFreeMan_bound[OF assms(6)] by (simp add:list_update_swap)
  hence "findFiance (X[m:=Some w, m':=None]) w = Some m"
    using `m'\<noteq>m` findFreeMan_bound[OF assms(6)] findFiance_first_is_Some by simp
  with GS'_arg_seq_step_2[OF assms(1,3,4,6-9)] assms(5) show ?thesis by simp
qed

lemma GS'_arg_seq_all_w_marry_better:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; is_distinct engagements; 
  i < length seq; seq!i = (X_pre, Y_pre); j < length seq; seq!j = (X_post, Y_post);
  i \<le> j\<rbrakk> \<Longrightarrow> married_better w WPrefs X_pre X_post"
proof (induction "j - i" arbitrary:j X_post Y_post)
  case 0
  from "0.hyps" "0.prems"(7) have "i = j" by simp
  with "0.prems"(4,6) married_better_refl show ?case by auto
next
  case (Suc d)
  from Suc.hyps(2) obtain j_1 where j_1:"j = Suc j_1" using not0_implies_Suc by fastforce
  obtain X_po_prev Y_po_prev where seq_j_1:"seq!j_1 = (X_po_prev, Y_po_prev)" by fastforce
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) Suc_lessD this] j_1 Suc.prems(5)
  obtain m where m:"findFreeMan X_po_prev = Some m" by auto
  let ?w = "MPrefs!m!(Y_po_prev!m)"
  from Suc.hyps(2) j_1 have "d = j_1 - i" and "i \<le> j_1" by simp_all
  from Suc.hyps(1)[OF this(1) Suc.prems(1-4) Suc_lessD seq_j_1 this(2)] j_1 Suc.prems(5)
  have "married_better w WPrefs X_pre X_po_prev" by blast
  moreover have "married_better w WPrefs X_po_prev X_post"
  proof (cases "findFiance X_po_prev w")
    case None
    thus ?thesis by simp
  next
    fix m_w
    assume m_w:"findFiance X_po_prev w = Some m_w"
    from findFreeMan[OF m] findFiance[OF m_w] have "m \<noteq> m_w" by fastforce
    show ?thesis
    proof (cases "findFiance X_po_prev ?w")
      case None
      with m_w findFiance_Some_is_first[OF m_w] findFreeMan_bound[OF m] 
      have "\<forall>m'<m_w. (X_po_prev[m:=Some ?w])!m' \<noteq> Some w" by (auto simp add:nth_list_update)
      hence "findFiance (X_po_prev[m:=Some ?w]) w = Some m_w" 
        using `m\<noteq>m_w` findFiance[OF m_w] findFiance_bound[OF m_w] findFiance_first_is_Some by simp
      with GS'_arg_seq_step_1[OF Suc.prems(1) _ seq_j_1 m refl None] Suc.prems(5,6) j_1
      have "findFiance X_post w = Some m_w" by simp
      with m_w show ?thesis by simp
    next
      case (Some m')
      show ?thesis
      proof (cases "prefers ?w WPrefs m m'")
        case True
        show "married_better w WPrefs X_po_prev X_post"
        proof cases
          assume "w = ?w"
          moreover from GS'_arg_seq_findFiance_2[OF Suc.prems(1,2) _ seq_j_1 _ m refl Some True] 
            j_1 Suc.prems(5,6) have "findFiance X_post ?w = Some m" by blast
          ultimately show ?thesis using Some True by simp
        next
          let ?X_post = "X_po_prev[m:=Some ?w, m':=None]"
          assume "w \<noteq> ?w"
          with findFiance_Some_is_first[OF m_w] findFreeMan_bound[OF m] findFiance_bound[OF Some]
          have "\<forall>m''<m_w. ?X_post!m'' \<noteq> Some w" by (simp add:nth_list_update)
          moreover have "?X_post!m_w = Some w"
          proof -
            from findFiance[OF Some] findFiance[OF m_w] `w\<noteq>?w` have "m' \<noteq> m_w" by fastforce
            with `m\<noteq>m_w` findFiance[OF m_w] show ?thesis by simp
          qed
          ultimately have "findFiance ?X_post w = Some m_w"
            using findFiance_bound[OF m_w] findFiance_first_is_Some by simp
          with GS'_arg_seq_step_2[OF Suc.prems(1) _ seq_j_1 m refl Some True] 
            Suc.prems(5,6) j_1 m_w show ?thesis by fastforce
        qed
      next
        case False
        from GS'_arg_seq_step_3[OF Suc.prems(1) _ seq_j_1 m refl Some this] Suc.prems(5,6) j_1
        have "X_post = X_po_prev" by simp
        thus ?thesis using married_better_refl by simp
      qed
    qed
  qed
  ultimately show ?case using married_better_trans by blast
qed

lemma GS'_arg_seq_prev_prop_idx_same_or_1_less:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "Suc i < length seq" and "seq!Suc i = (X, Y)" and "seq!i = (X_prev, Y_prev)"
      and "k = Suc k_1" and "Y!m = k"
    shows "Y_prev!m = k \<or> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m"
proof -
  from GS'_arg_seq_last_eq_terminal[OF assms(1) Suc_lessD[OF assms(2)] assms(4)] assms(2)
  have non_terminal:"\<not> is_terminal N X_prev Y_prev" by simp
  then obtain m_prev where m_prev:"findFreeMan X_prev = Some m_prev" by blast
  from GS'_arg_seq_snd_step[OF assms(1-2,4) this assms(3)] assms(6) 
  have is_k:"Y_prev[m_prev:=Suc(Y_prev!m_prev)]!m = k" by blast
  show ?thesis
  proof (rule ccontr)
    assume asm:"\<not>(Y_prev!m = k \<or> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)"
    show False
    proof (cases "m = m_prev")
      case True
      with asm m_prev have "Y_prev!m \<noteq> k_1" by blast
      moreover from findFreeMan_bound[OF m_prev] non_terminal have "m_prev < length Y_prev" by argo
      ultimately show False using True is_k assms(5) by simp
    next
      case False
      with asm is_k show False by simp
    qed
  qed
qed

lemma GS'_arg_seq_exists_prev_prop_idx:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0)"
      and "i < length seq" and "seq!i = (X, Y)" 
      and "k = Suc k_1" and "m < N" and "Y!m = k"
    shows "\<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev)
                           \<and> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m"
proof (rule ccontr)
  assume asm:"\<not> (\<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev) 
                                 \<and> Y_prev!m = k_1 \<and> findFreeMan X_prev = Some m)"
  have "0 < i \<and> seq!0 = (engagements, replicate N 0)"
  proof
    show "0 < i"
    proof (rule ccontr)
      assume "\<not>0 < i"
      with assms(1,3-6) show False by (auto simp del:GS'_arg_seq.simps)
    qed
  next
    show "seq!0 = (engagements, replicate N 0)" using assms(1) by (simp del:GS'_arg_seq.simps)
  qed
  moreover have "\<lbrakk>j < i; seq!j = (X_prev, Y_prev)\<rbrakk> \<Longrightarrow> Y_prev!m = k" for j X_prev Y_prev
  proof (induction "i-1 - j" arbitrary: j X_prev Y_prev)
    case 0
    from "0.hyps" "0.prems"(1) have "i = Suc j" by auto
    with GS'_arg_seq_prev_prop_idx_same_or_1_less[OF assms(1) _ _ "0.prems"(2) assms(4,6)]
      assms(2,3) asm "0.prems" show ?case by blast
  next
    case (Suc d)
    obtain X' Y' where X_Y:"seq!Suc j = (X', Y')" by fastforce
    from Suc.hyps(2) have "d = i-1 - Suc j" and "Suc j < i" by simp_all
    from GS'_arg_seq_prev_prop_idx_same_or_1_less[OF assms(1) 
        order.strict_trans[OF this(2) assms(2)] X_Y Suc.prems(2) assms(4) Suc.hyps(1)[OF this X_Y]]
      asm Suc.prems show ?case by blast
  qed
  ultimately have "(replicate N 0)!m = k" by blast
  thus False using assms(4-5) by simp
qed

lemma GS'_arg_seq_all_prev_prop_idxs_exist:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0); 
  i < length seq; seq!i = (X, prop_idxs); m < N; prop_idxs!m = k; 
  prop_idx < k\<rbrakk> \<Longrightarrow> \<exists>j X_prev Y_prev. j < i \<and> seq!j = (X_prev, Y_prev) 
                                   \<and> Y_prev!m = prop_idx \<and> findFreeMan X_prev = Some m"
proof (induction "k-1 - prop_idx" arbitrary: prop_idx)
  case 0
  from "0.hyps" "0.prems"(6) have "k = Suc prop_idx" by fastforce
  from GS'_arg_seq_exists_prev_prop_idx[OF "0.prems"(1-3) this "0.prems"(4,5)] show ?case .
next
  case (Suc d)
  from Suc.hyps(2) have "d = k-1 - Suc prop_idx" and "Suc prop_idx < k" by simp_all
  from Suc.hyps(1)[OF this(1) Suc.prems(1-5) this(2)] obtain j X_prev Y_prev
    where "j < i" and "seq!j = (X_prev, Y_prev)" and "Y_prev!m = Suc prop_idx" by blast
  from GS'_arg_seq_exists_prev_prop_idx[OF Suc.prems(1) order.strict_trans[OF this(1) Suc.prems(2)]
      this(2) refl Suc.prems(4) this(3)] order.strict_trans[OF _ this(1)] show ?case by blast
qed

lemma GS'_arg_seq_married_once_proposed_to:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs" and "is_distinct engagements"
      and "Suc i < length seq" and "seq!i = (X, Y)" and "seq!Suc i = (X_next, Y_next)"
      and m:"findFreeMan X = Some m" and "w = MPrefs!m!(Y!m)"
    shows "\<exists>m'. findFiance X_next w = Some m' \<and> (m' = m \<or> m' \<noteq> m \<and> \<not>prefers w WPrefs m m')"
proof (cases "findFiance X w")
  case None
  from GS'_arg_seq_findFiance_1[OF assms(1,3-7) None] show ?thesis by blast
next
  case (Some m')
  show ?thesis
  proof (cases "prefers w WPrefs m m'")
    case True
    from GS'_arg_seq_findFiance_2[OF assms(1-7) Some True] show ?thesis by blast
  next
    case False
    with GS'_arg_seq_step_3[OF assms(1,3,4,6,7) Some this] assms(5) Some show ?thesis by fastforce
  qed
qed

lemma GS'_arg_seq_any_man_done_proposing_means_done:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)" and "m < N" and "prop_idxs!m = N"
    shows "findFreeMan engagements = None"
proof -
  let ?Some_Ns = "map Some [0 ..< N]"
  have distinct:"is_distinct (replicate N None)" by simp
  have "\<forall>prop_idx < length (MPrefs!m). findFiance engagements (MPrefs!m!prop_idx) \<noteq> None"
    apply (rule)
  proof
    fix prop_idx
    let ?w = "MPrefs!m!prop_idx"
    assume "prop_idx < length (MPrefs!m)"
    also have "... = N" using perm_length[OF perm_PPref[OF assms(2,5)]] by simp
    finally have "prop_idx < N" .
    from GS'_arg_seq_all_prev_prop_idxs_exist[OF assms(1,3-6) this] obtain j X_prev Y_prev X' Y'
      where "j < i" and "seq!j = (X_prev, Y_prev)" and X_Y:"seq!Suc j = (X', Y')" 
        and "findFreeMan X_prev = Some m" and "Y_prev!m = prop_idx" by fastforce
    from GS'_arg_seq_married_once_proposed_to[OF assms(1) distinct 
        less_trans_Suc[OF this(1) assms(3)] this(2-4)] this(5) 
    have "findFiance X' ?w \<noteq> None" by fastforce
    moreover have "married_better ?w WPrefs X' engagements" 
      using GS'_arg_seq_all_w_marry_better[OF assms(1) distinct less_trans_Suc[OF `j<i` assms(3)] 
          X_Y assms(3,4) Suc_leI[OF `j<i`]] by fast
    ultimately show "findFiance engagements ?w \<noteq> None" using married_better_imp by blast
  qed
  hence "\<forall>w \<in> set [0 ..< N]. findFiance engagements w \<noteq> None" 
    using perm_set_eq[OF perm_PPref[OF assms(2,5)]] by (metis in_set_conv_nth)
  hence "set ?Some_Ns \<subseteq> set engagements" using findFiance_Some by auto
  moreover have "card (set ?Some_Ns) = N"
  proof -
    have "distinct (xs::nat list) \<Longrightarrow> distinct (map Some xs)" for xs
      apply (induction xs)
      by auto
    hence "distinct ?Some_Ns" by simp
    from distinct_card[OF this] show ?thesis by simp
  qed
  moreover have "card (set engagements) \<le> N" and "finite (set engagements)"
    using card_length[of engagements] GS'_arg_seq_length_fst[OF assms(1,3,4)] by simp_all
  ultimately have "set ?Some_Ns = set engagements" by (metis card_seteq)
  with findFreeMan_None show ?thesis by auto
qed

lemma GS'_arg_seq_prop_idx_bound:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)" and "m < N"
    shows "prop_idxs!m \<le> N"
proof (rule ccontr)
  assume "\<not>prop_idxs!m \<le> N"
  then obtain k where "prop_idxs!m = k" and "N < k" by simp
  from GS'_arg_seq_all_prev_prop_idxs_exist[OF assms(1,3-5) this] obtain j X_prev Y_prev 
    where "j < i" and "seq!j = (X_prev, Y_prev)" 
      and "Y_prev!m = N" and "findFreeMan X_prev = Some m" by blast
  from GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1,2) 
      order.strict_trans[OF this(1) assms(3)] this(2) `m<N` this(3)] this(4) show False by simp
qed

lemma GS'_arg_seq_prop_idx_bound_non_terminal:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)"
      and "m < N" and "\<not>is_terminal N engagements prop_idxs"
    shows "prop_idxs!m < N"
proof (rule ccontr)
  assume "\<not>prop_idxs!m < N"
  with GS'_arg_seq_prop_idx_bound[OF assms(1-5)] have "prop_idxs!m = N" by linarith
  from GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1-5) this] assms(6) 
  show False by blast
qed

lemma GS'_arg_seq_N_imp_prev_bump:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)"
      and "m < N" and "prop_idxs!m = N"
    shows "\<exists>i_1 N_1 X_prev Y_prev. i = Suc i_1 \<and> N = Suc N_1 \<and> seq!i_1 = (X_prev, Y_prev)
                                 \<and> Y_prev!m = N_1 \<and> findFreeMan X_prev = Some m"
proof -
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    with assms(1,4,6) have "(replicate N 0)!m = N" by (simp del:GS'_arg_seq.simps)
    with `m<N` show False by fastforce
  qed
  moreover have "N \<noteq> 0" using `m<N` by linarith
  ultimately obtain i_1 N_1 X_prev Y_prev where i_1:"i = Suc i_1" and N_1:"N = Suc N_1"
    and seq_i_1:"seq!i_1 = (X_prev, Y_prev)" using not0_implies_Suc by fastforce
  from i_1 assms(3,4) have "Suc i_1 < length seq" and "seq!Suc i_1 = (engagements, prop_idxs)" 
    by simp_all
  from GS'_arg_seq_prev_prop_idx_same_or_1_less[OF assms(1) this seq_i_1 N_1 assms(6)]
    GS'_arg_seq_any_man_done_proposing_means_done[OF assms(1,2) 
      Suc_lessD[OF this(1)] seq_i_1 `m<N`] GS'_arg_seq_last_eq_terminal[OF assms(1)
      Suc_lessD[OF this(1)] seq_i_1] this(1) 
  have "Y_prev!m = N_1 \<and> findFreeMan X_prev = Some m" by force
  with i_1 N_1 seq_i_1 show ?thesis by blast
qed

theorem GS'_arg_seq_never_reaches_NxN:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
      and "i < length seq" and "seq!i = (engagements, prop_idxs)"
    shows "sum_list prop_idxs < N * N"
proof (rule ccontr)
  assume asm:"\<not> sum_list prop_idxs < N * N"
  obtain N_1 where N_1:"N = Suc N_1" using `N \<ge> 2` numeral_eq_Suc Suc_le_D by fastforce
  have l_prop_idxs:"length prop_idxs = N" using GS'_arg_seq_length_snd[OF assms(1,4-5)] by simp
  have sum_bound:"\<forall>m < length prop_idxs. prop_idxs!m \<le> N 
              \<Longrightarrow> sum_list prop_idxs \<le> length prop_idxs * N" for prop_idxs N
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
  with GS'_arg_seq_prop_idx_bound[OF assms(1,2,4,5)] 
  obtain m where "m < N" and m:"prop_idxs!m = N" by fastforce
  let ?prop_idxs' = "prop_idxs[m:=N_1]"
  have "\<lbrakk>m' < N; m' \<noteq> m\<rbrakk> \<Longrightarrow> prop_idxs!m' \<le> N_1" for m'
  proof (rule ccontr)
    assume "\<not> prop_idxs!m' \<le> N_1" and "m' < N" and "m' \<noteq> m"
    from GS'_arg_seq_prop_idx_bound[OF assms(1,2,4,5) this(2)] this(1) N_1
    have "prop_idxs!m' = N" by linarith
    from GS'_arg_seq_N_imp_prev_bump[OF assms(1,2,4,5) `m'<N` this]
      GS'_arg_seq_N_imp_prev_bump[OF assms(1,2,4,5) `m<N` m]  `m'\<noteq>m`
    show False by auto
  qed
  moreover from `m<N` l_prop_idxs have m_bound:"m < length prop_idxs" by simp
  ultimately have "\<forall>m'<length ?prop_idxs'. ?prop_idxs'!m' \<le> N_1" 
    using l_prop_idxs by (simp add:nth_list_update)
  from sum_bound[OF this] l_prop_idxs have "sum_list ?prop_idxs' \<le> N * N_1" by simp
  moreover have "sum_list ?prop_idxs' = sum_list prop_idxs + N_1 - N" 
    using sum_list_update[OF m_bound] m by presburger
  ultimately have "sum_list prop_idxs \<le> Suc (N * N_1)" using N_1 by linarith
  also have "... < N * N" using N_1 `N\<ge>2` by fastforce
  finally show False using asm by simp
qed

lemma GS'_arg_seq_all_bounded:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0);
  is_valid_pref_matrix N MPrefs; i < length seq; seq!i = (engagements, prop_idxs)\<rbrakk>
   \<Longrightarrow> is_bounded engagements"
proof (induction i arbitrary:engagements prop_idxs)
  case 0
  from "0.prems"(1,4) have "engagements = (replicate N None)" by (simp del:GS'_arg_seq.simps)
  thus ?case by simp
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  from Suc_lessD[OF Suc.prems(3)] have i_bound:"i < length seq" .
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) this seq_i] Suc.prems(3)
  have non_terminal:"\<not>is_terminal N X_prev Y_prev" by auto 
  then obtain m where m:"findFreeMan X_prev = Some m" by blast
  let ?w = "MPrefs!m!(Y_prev!m)"
  from findFreeMan_bound[OF m] GS'_arg_seq_length_fst[OF Suc.prems(1) i_bound seq_i]
  have "m < N" by simp
  from perm_length[OF perm_PPref[OF Suc.prems(2) this]] have "length (MPrefs!m) = N" by simp
  with GS'_arg_seq_prop_idx_bound_non_terminal[OF Suc.prems(1,2) i_bound seq_i `m<N` non_terminal]
  have "?w \<in> set (MPrefs!m)" by simp
  with perm_PPref[OF Suc.prems(2) `m<N`] in_perm_upt have "?w < N" by blast
  from GS'_arg_seq_length_fst[OF Suc.prems(1) i_bound seq_i] have l:"length X_prev = N" by simp
  from Suc.IH[OF Suc.prems(1,2) i_bound seq_i] have IH:"is_bounded X_prev" .
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    from GS'_arg_seq_step_1[OF Suc.prems(1,3) seq_i m refl None] Suc.prems(4)
      `?w<N` `m<N` l IH show ?thesis by (simp add:nth_list_update)
  next
    case (Some m')
    show ?thesis
    proof (cases "prefers ?w WPrefs m m'")
      case True
      from GS'_arg_seq_step_2[OF Suc.prems(1,3) seq_i m refl Some True] Suc.prems(4) 
        `?w<N` `m<N` l findFiance_bound[OF Some] IH show ?thesis by (simp add:nth_list_update)
    next
      case False
      from GS'_arg_seq_step_3[OF Suc.prems(1,3) seq_i m refl Some this] Suc.prems(4)
      show ?thesis using IH by simp
    qed
  qed
qed

theorem is_matching:
  assumes "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
  shows "(Gale_Shapley MPrefs WPrefs) <~~> map Some [0..<N]"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  from GS'_arg_seq_length_gr_0 obtain i where i:"length ?seq = Suc i" 
    using not0_implies_Suc by blast
  hence i_bound:"i < length ?seq" by simp
  obtain X Y where seq_i:"?seq!i = (X, Y)" by fastforce

  from GS'_arg_seq_length_fst[OF refl i_bound seq_i] have l:"length X = N" by fastforce

  from length_PPrefs[OF assms(1)] have "Gale_Shapley MPrefs WPrefs 
                 = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by simp
  also have "... = X" using GS'_arg_seq_computes_GS'[OF refl i seq_i] by presburger
  finally have result:"Gale_Shapley MPrefs WPrefs = X" .

  have "\<forall>m < length X. X!m \<noteq> None"
  proof -
    from GS'_arg_seq_last_eq_terminal[OF refl i_bound seq_i] i have "is_terminal N X Y" by argo
    moreover have "length X = length Y" 
      using GS'_arg_seq_length_snd[OF refl i_bound seq_i] l by fastforce
    moreover have "sum_list Y < N * N" 
      using GS'_arg_seq_never_reaches_NxN[OF refl assms i_bound seq_i] .
    ultimately have "findFreeMan X = None" by simp
    with findFreeMan_None show ?thesis by (metis nth_mem)
  qed
  moreover have "is_distinct X" using GS'_arg_seq_all_distinct[OF refl _ i_bound seq_i] by simp
  moreover have "is_bounded X" using GS'_arg_seq_all_bounded[OF refl assms(1) i_bound seq_i] .
  ultimately show ?thesis using is_matching_intro[of X] result l by fast
qed

abbreviation unstable where
"unstable MPrefs WPrefs engagements \<equiv> 
 \<exists>m1 m2 w1 w2. m1 < length engagements \<and> m2 < length engagements 
             \<and> engagements!m1 = Some w1 \<and> engagements!m2 = Some w2
             \<and> prefers w1 WPrefs m2 m1 \<and> prefers m2 MPrefs w1 w2"

lemma prefers_total_antisym:
  assumes "is_valid_pref_matrix N PPrefs" and "p < N" and "p1 < N" and "p2 < N" and "p1 \<noteq> p2"
  shows "(prefers p PPrefs p1 p2 \<or> prefers p PPrefs p2 p1)
       \<and> (prefers p PPrefs p1 p2 \<longleftrightarrow> \<not>prefers p PPrefs p2 p1)"
proof -
  from assms(3,4) in_upt[where ?k=N] perm_set_eq[OF perm_PPref[OF assms(1,2)]]
  have "p1 \<in> set (PPrefs!p) \<and> p2 \<in> set (PPrefs!p)" by blast
  with find_idx_Some[where ?xs="PPrefs!p"] obtain idx_1 idx_2 
    where "find_idx p1 (PPrefs!p) = Some idx_1" and "find_idx p2 (PPrefs!p) = Some idx_2" by blast
  moreover from `p1\<noteq>p2` find_idx[OF this(1)] find_idx[OF this(2)] 
  have "idx_1 \<noteq> idx_2" by blast
  ultimately show ?thesis by fastforce
qed

lemma GS'_arg_seq_be_brave:
"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) prop_idxs; i < length seq; seq!i = (X, Y);
  \<nexists>j X' Y'. j < i \<and> seq!j = (X', Y') \<and> findFreeMan X' = Some m \<and> MPrefs!m!(Y'!m) = w; m < N\<rbrakk>
   \<Longrightarrow> X!m \<noteq> Some w"
proof (induction i arbitrary:X Y)
  case 0
  from "0.prems"(1,3,5) show ?case by (auto simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  obtain X_prev Y_prev where seq_i:"seq!i = (X_prev, Y_prev)" by fastforce
  have "\<nexists>j X' Y'. j < i \<and> seq!j = (X', Y') \<and> findFreeMan X' = Some m \<and> MPrefs!m!(Y'!m) = w"
    using Suc.prems(4) less_SucI by blast 
  from Suc.IH[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] seq_i this Suc.prems(5)] 
  have IH:"X_prev!m \<noteq> Some w" .
  have prem:"\<not>(findFreeMan X_prev = Some m \<and> MPrefs!m!(Y_prev!m) = w)" 
    using Suc.prems(4) seq_i by blast
  from GS'_arg_seq_last_eq_terminal[OF Suc.prems(1) Suc_lessD[OF Suc.prems(2)] seq_i] Suc.prems(2)
  have "\<not>is_terminal N X_prev Y_prev" by simp
  then obtain m_prev where m_prev:"findFreeMan X_prev = Some m_prev" by blast
  let ?w = "MPrefs!m_prev!(Y_prev!m_prev)"
  show ?case
  proof (cases "findFiance X_prev ?w")
    case None
    from GS'_arg_seq_step_1[OF Suc.prems(1,2) seq_i m_prev refl None] Suc.prems(3)
    have X:"X = X_prev[m_prev:=Some ?w]" by simp
    show ?thesis
    proof (cases "m = m_prev")
      case True
      with m_prev prem X findFreeMan_bound[OF m_prev] show ?thesis by simp
    next
      case False
      with IH X show ?thesis by simp
    qed
  next
    case (Some m')
    show ?thesis
    proof (cases "prefers ?w WPrefs m_prev m'")
      case True
      from GS'_arg_seq_step_2[OF Suc.prems(1,2) seq_i m_prev refl Some True] Suc.prems(3)
      have X:"X = X_prev[m_prev:=Some ?w, m':=None]" by simp
      show ?thesis
      proof cases
        assume "m = m_prev"
        moreover hence "Some ?w \<noteq> Some w" using prem m_prev by blast
        moreover from findFreeMan[OF m_prev] findFiance[OF Some] have "m_prev \<noteq> m'" by auto
        ultimately show ?thesis using X findFreeMan_bound[OF m_prev] by simp
      next
        assume "m \<noteq> m_prev"
        show ?thesis
        proof cases
          assume "m = m'"
          with findFiance_bound[OF Some] X show ?thesis by simp
        next
          assume "m \<noteq> m'"
          with `m\<noteq>m_prev` IH X show ?thesis by auto
        qed
      qed
    next
      case False
      from GS'_arg_seq_step_3[OF Suc.prems(1,2) seq_i m_prev refl Some this] Suc.prems(3) IH
      show ?thesis by simp
    qed
  qed
qed

theorem GS'_arg_seq_all_stable:
  assumes "seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)" 
      and "is_valid_pref_matrix N MPrefs" and "is_valid_pref_matrix N WPrefs"
      and "i < length seq" and "seq!i = (X, Y)"
    shows "\<not> unstable MPrefs WPrefs X"
proof
  assume "unstable MPrefs WPrefs X"
  moreover from GS'_arg_seq_length_fst[OF assms(1,4,5)] have "length X = N" by simp
  ultimately obtain m1 m2 w1 w2 where "m1 < N" and "m2 < N" 
    and "X!m1 = Some w1" and "X!m2 = Some w2" 
    and w1_m2:"prefers w1 WPrefs m2 m1" and m2_w1:"prefers m2 MPrefs w1 w2" by blast
  from GS'_arg_seq_be_brave[OF assms(1,4,5) _ `m2<N`] this(4) obtain j_m2_w2 X_m2_w2 Y_m2_w2
    where "j_m2_w2 < i" and seq_m2_w2:"seq!j_m2_w2 = (X_m2_w2, Y_m2_w2)" 
      and Y_m2_w2:"w2 = MPrefs!m2!(Y_m2_w2!m2)" by metis
  from GS'_arg_seq_last_eq_terminal[OF assms(1) order.strict_trans[OF this(1) assms(4)] this(2)]
    assms(4) this(1) have "\<not>is_terminal N X_m2_w2 Y_m2_w2" by simp
  from GS'_arg_seq_prop_idx_bound_non_terminal[OF assms(1,2) 
      order.strict_trans[OF `j_m2_w2<i` assms(4)] seq_m2_w2 `m2<N` this] have "Y_m2_w2!m2 < N" .
  obtain idx_m2_w1 where idx_m2_w1:"find_idx w1 (MPrefs!m2) = Some idx_m2_w1"
    using m2_w1 by fastforce
  then obtain idx_m2_w2 where idx_m2_w2:"find_idx w2 (MPrefs!m2) = Some idx_m2_w2" 
    using m2_w1 by fastforce
  from length_PPref[OF assms(2) `m2<N`] find_idx_bound[OF this] have "idx_m2_w2 < N" by simp
  from PPref_inject[OF assms(2) `m2<N` `Y_m2_w2!m2<N` this] Y_m2_w2 find_idx[OF idx_m2_w2]
  have "Y_m2_w2!m2 = idx_m2_w2" by presburger
  moreover from m2_w1 idx_m2_w1 idx_m2_w2 have "idx_m2_w1 < idx_m2_w2" by simp
  ultimately obtain j_m2_w1 X_m2_w1 Y_m2_w1 where "j_m2_w1 < j_m2_w2" 
    and "seq!j_m2_w1 = (X_m2_w1, Y_m2_w1)" and "Y_m2_w1!m2 = idx_m2_w1" 
    and "findFreeMan X_m2_w1 = Some m2" using GS'_arg_seq_all_prev_prop_idxs_exist[OF assms(1)
        order.strict_trans[OF `j_m2_w2<i` assms(4)] seq_m2_w2 `m2<N`] by blast
  moreover have distinct:"is_distinct (replicate N None)" by simp
  moreover from order.strict_trans[OF `j_m2_w1<j_m2_w2` `j_m2_w2<i`] assms(4) 
  have "Suc j_m2_w1 < length seq" by fastforce 
  moreover obtain X_m2_w1_Suc Y_m2_w1_Suc 
    where seq_m2_w1_Suc:"seq!Suc j_m2_w1 = (X_m2_w1_Suc, Y_m2_w1_Suc)" by fastforce
  ultimately obtain m' where m':"findFiance X_m2_w1_Suc w1 = Some m'" 
    and cases_1:"(m' = m2 \<or> m' \<noteq> m2 \<and> \<not> prefers w1 WPrefs m2 m')"
    using GS'_arg_seq_married_once_proposed_to[OF assms(1)] find_idx[OF idx_m2_w1] by blast
  from married_better_imp[OF this(1) GS'_arg_seq_all_w_marry_better[OF assms(1) distinct 
        `Suc j_m2_w1<length seq` seq_m2_w1_Suc assms(4,5) Suc_leI[OF 
          order.strict_trans[OF `j_m2_w1<j_m2_w2` `j_m2_w2<i`]]]] 
  obtain m1' where "findFiance X w1 = Some m1'" and "m' = m1' \<or> prefers w1 WPrefs m1' m'" by blast
  from GS'_arg_seq_all_distinct[OF assms(1) distinct assms(4,5)] findFiance[OF this(1)] 
    `X!m1=Some w1` findFiance_bound[OF this(1)] `m1<N` `length X=N` this(2)
  have cases_2:"m' = m1 \<or> prefers w1 WPrefs m1 m'" by fastforce
  from findFiance_bound[OF m'] GS'_arg_seq_length_fst[OF assms(1) `Suc j_m2_w1<length seq` 
      seq_m2_w1_Suc] have "m' < N" by simp
  from find_idx[OF idx_m2_w1] find_idx_bound[OF idx_m2_w1] 
    perm_set_eq[OF perm_PPref[OF assms(2) `m2<N`]] in_upt have "w1 < N" by (metis nth_mem)
  from cases_1 show False
  proof
    assume "m' = m2"
    from cases_2 show False
    proof
      assume "m' = m1"
      with `m'=m2` w1_m2 show False using prefers_non_refl by blast
    next
      assume "prefers w1 WPrefs m1 m'"
      with `m'=m2` prefers_total_antisym[OF assms(3) `w1<N` `m1<N` `m2<N`] w1_m2 prefers_non_refl
      show False by blast
    qed
  next
    assume "m' \<noteq> m2 \<and> \<not> prefers w1 WPrefs m2 m'"
    with prefers_total_antisym[OF assms(3) `w1<N` `m2<N` `m'<N`] 
    have w1_m':"prefers w1 WPrefs m' m2" by blast
    from cases_2 show False
    proof
      assume "m' = m1"
      with prefers_trans[OF w1_m' w1_m2] prefers_non_refl show False by fast
    next
      assume "prefers w1 WPrefs m1 m'"
      from prefers_trans[OF this w1_m'] prefers_total_antisym[OF assms(3) `w1<N` `m1<N` `m2<N`] 
        w1_m2 prefers_non_refl show False by blast
    qed
  qed
qed

theorem stable:
  assumes "is_valid_pref_matrix N MPrefs" and "is_valid_pref_matrix N WPrefs"
  shows "\<not> unstable MPrefs WPrefs (Gale_Shapley MPrefs WPrefs)"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  from GS'_arg_seq_length_gr_0 obtain i where i:"length ?seq = Suc i" 
    using not0_implies_Suc by blast
  hence i_bound:"i < length ?seq" by simp
  obtain X Y where seq_i:"?seq!i = (X, Y)" by fastforce

  from length_PPrefs[OF assms(1)] have "Gale_Shapley MPrefs WPrefs 
                 = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by simp
  also have "... = X" using GS'_arg_seq_computes_GS'[OF refl i seq_i] by presburger
  finally show ?thesis using GS'_arg_seq_all_stable[OF refl assms i_bound seq_i] by simp
qed
end
