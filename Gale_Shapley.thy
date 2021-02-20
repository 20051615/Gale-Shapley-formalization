theory Gale_Shapley
  imports "HOL-Library.Permutation" List_Ops
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

fun is_perm::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_perm A B = (mset A = mset B)"
lemma is_perm:"is_perm A B \<Longrightarrow> A <~~> B" by (metis is_perm.simps mset_eq_perm)

fun is_valid_pref_matrix::"pref_matrix \<Rightarrow> bool" where
"is_valid_pref_matrix PPrefs = Ball (set PPrefs) (\<lambda>PPref. is_perm PPref [0 ..< length PPrefs])"

fun findFreeMan::"matching \<Rightarrow> man option" where
"findFreeMan engagements = find_idx (\<lambda>wo. wo = None) engagements"
lemma findFreeMan_bound:"findFreeMan engagements = Some m \<Longrightarrow> m < length engagements" by (auto intro:find_idx_bound)

fun findFiance::"matching \<Rightarrow> woman \<Rightarrow> man option" where
"findFiance engagements w = find_idx (\<lambda>wo. wo = Some w) engagements"

fun findPerson::"person list \<Rightarrow> person \<Rightarrow> nat option" where
"findPerson ps p = find_idx (\<lambda>p'. p' = p) ps"
lemma findPerson_0:"p \<in> set ps \<Longrightarrow> \<exists>idx. findPerson ps p = Some idx" by (auto intro:find_idx_0)
lemma findPerson_1:"p \<in> set ps \<Longrightarrow> ps!(the (findPerson ps p)) = p" by (auto intro:find_idx_1)

fun prefers::"person \<Rightarrow> pref_matrix \<Rightarrow> person \<Rightarrow> person \<Rightarrow> bool" where
"prefers p PPrefs p1 p2 = (let PPref = PPrefs!p in (
  case findPerson PPref p1 of None \<Rightarrow> False |
                            Some idx_1 \<Rightarrow> (
    case findPerson PPref p2 of None \<Rightarrow> False |
                              Some idx_2 \<Rightarrow> idx_1 < idx_2
  )
))"

lemma termination_aid:
  assumes 1:"length engagements = length prop_idxs"
    and 2:"findFreeMan engagements = Some m"
    and 3:"next_prop_idxs = prop_idxs[m:=Suc(prop_idxs!m)]"
    and 4:"sum_list prop_idxs < N * N"
  shows "N * N - sum_list next_prop_idxs < N * N - sum_list prop_idxs"
proof -
  from 1 2 findFreeMan_bound have "m < length prop_idxs" by metis
  moreover have "m < length xs \<Longrightarrow> sum_list (xs[m:=Suc (xs!m)]) = Suc (sum_list xs)" for m xs
  proof (induction xs arbitrary:m)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases m)
      case 0
      thus ?thesis by simp
    next
      case (Suc m_1)
      with Cons.prems have m_1:"m_1 < length xs" by auto
      with Cons.IH have "sum_list (xs[m_1:=Suc (xs!m_1)]) = Suc (sum_list xs)" by simp
      moreover from m_1 Cons.prems Suc have "(x # xs) [m:=Suc ((x#xs)!m)] = x # xs [m_1:=Suc (xs!m_1)]" by simp
      ultimately show ?thesis by fastforce
    qed
  qed
  ultimately have "sum_list next_prop_idxs = Suc (sum_list prop_idxs)" using 3 by metis
  with 4 show ?thesis by auto
qed

function Gale_Shapley'::"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix
 \<Rightarrow> matching \<Rightarrow> nat list \<Rightarrow>
 matching" where
"Gale_Shapley' N MPrefs WPrefs 
 engagements prop_idxs 
 = 
(if length engagements \<noteq> length prop_idxs then engagements else
(if sum_list prop_idxs \<ge> N * N then engagements else

(case findFreeMan engagements of None \<Rightarrow> engagements |

 Some m \<Rightarrow> (let w = (MPrefs!m)!(prop_idxs!m);
   next_prop_idxs = prop_idxs[m:=Suc (prop_idxs!m)] in (
   case findFiance engagements w of
     None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
       (engagements[m:=Some w]) next_prop_idxs
   | Some m' \<Rightarrow> (
     if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
       (engagements[m:=Some w, m':=None]) next_prop_idxs
     else Gale_Shapley' N MPrefs WPrefs
       engagements next_prop_idxs
   )
 ))
)
))"
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(N, _, _, _, prop_idxs). N * N - sum_list prop_idxs)")
  by (auto intro:termination_aid)

fun Gale_Shapley::"pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching" where
"Gale_Shapley MPrefs WPrefs = (let N = length MPrefs in
 Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0))"

lemma in_upt:"x < k \<longleftrightarrow> x \<in> set [0 ..< k]"
proof
  show "x < k \<Longrightarrow> x \<in> set [0 ..< k]"
  proof (induction k)
    case 0
    thus ?case by simp
  next
    case (Suc k_1)
    hence "x < k_1 \<or> x = k_1" by auto
    thus ?case
    proof
      assume "x < k_1"
      with Suc(1) have "x \<in> set [0..<k_1]" .
      thus ?case by auto
    next
      assume "x = k_1"
      thus ?case by auto
    qed
  qed
next
  show "x \<in> set [0 ..< k] \<Longrightarrow> x < k"
  proof (induction k)
    case 0
    thus ?case by simp
  next
    case (Suc k_1)
    hence "x \<in> set [0..<k_1] \<or> x = k_1" by auto
    thus ?case
    proof
      assume "x \<in> set [0..<k_1]"
      thus ?case using Suc(1) by simp
    next
      assume "x = k_1"
      thus ?case by simp
    qed
  qed
qed

lemma is_matching_intro:
  assumes noFree:"\<forall> wo \<in> set engagements. wo \<noteq> None"
    and distinct:"\<forall> m1 < length engagements.
                  \<forall> m2 < length engagements. 
                  m1 \<noteq> m2 \<longrightarrow> engagements!m1 = None \<or> engagements!m1 \<noteq> engagements!m2"
    and bounded:"\<forall> wo \<in> set engagements. wo \<noteq> None \<longrightarrow> the wo < length engagements"
  shows "engagements <~~> map Some [0 ..< length engagements]"
proof -
  let ?engagements = "map the engagements"
  let ?N = "length engagements"
  from noFree have "\<forall> wo \<in> set engagements. wo = Some (the wo)" using option.exhaust_sel by blast
  hence engagements:"engagements = map Some ?engagements" by (simp add: nth_equalityI)

  from bounded noFree have bounded_the:"\<forall> w \<in> set ?engagements. w < ?N" by simp
  from noFree have "\<forall> m < length engagements. engagements!m \<noteq> None" by simp
  moreover with distinct have "\<forall> m1 < length engagements.
                               \<forall> m2 < length engagements.
                               m1 \<noteq> m2 \<longrightarrow> engagements!m1 \<noteq> engagements!m2" by blast
  ultimately have "\<forall> m1 < length engagements.
                   \<forall> m2 < length engagements.
                   m1 \<noteq> m2 \<longrightarrow> the (engagements!m1) \<noteq> the (engagements!m2)" by (meson option.expand)
  hence "\<forall> m1 < length ?engagements.
         \<forall> m2 < length ?engagements.
         m1 \<noteq> m2 \<longrightarrow> ?engagements!m1 \<noteq> ?engagements!m2" by simp
  hence "distinct ?engagements" by (metis distinct_conv_nth)
  hence "card (set ?engagements) = length ?engagements" by (metis distinct_card)
  hence "card (set ?engagements) = ?N" by simp
  moreover from bounded_the in_upt have "set ?engagements \<subseteq> set [0 ..< ?N]" by blast
  moreover have "finite (set [0 ..< ?N])" by simp
  moreover have "card (set [0 ..< ?N]) = ?N" by simp
  ultimately have "set ?engagements = set [0 ..< ?N]" by (metis card_subset_eq)
  moreover have "distinct [0 ..< ?N]" by simp
  ultimately have "mset ?engagements = mset [0 ..< ?N]" using `distinct ?engagements` by (metis set_eq_iff_mset_eq_distinct)
  moreover have "mset xs = mset ys \<Longrightarrow> mset (map Some xs) = mset (map Some ys)" for xs ys by simp
  ultimately have "mset (map Some ?engagements) = mset (map Some [0..<?N])" by metis
  thus ?thesis by (metis engagements mset_eq_perm)
qed
end