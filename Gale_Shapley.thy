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
lemma findFiance_bound:"findFiance engagements w = Some m' \<Longrightarrow> m' < length engagements" by (auto intro:find_idx_bound)
lemma findFiance_None:"findFiance engagements w = None \<Longrightarrow> \<forall>wo\<in>set engagements. wo \<noteq> Some w"
proof -
  have "find_idx pred xs = None \<Longrightarrow> \<forall>x\<in>set xs. \<not>pred x" for pred xs using find_idx_None by metis
  thus "findFiance engagements w = None \<Longrightarrow> \<forall>wo\<in>set engagements. wo\<noteq>Some w" by auto
qed
lemma findFiance:"findFiance engagements w = Some m' \<Longrightarrow> engagements!m' = Some w"
proof -
  from find_idx_Some find_idx have "\<exists>idx. find_idx pred xs = Some idx \<Longrightarrow> pred (xs ! the (find_idx pred xs))" for pred xs by metis
  thus "findFiance engagements w = Some m' \<Longrightarrow> engagements!m' = Some w" using findFiance.elims by force
qed

fun findPerson::"person list \<Rightarrow> person \<Rightarrow> nat option" where
"findPerson ps p = find_idx (\<lambda>p'. p' = p) ps"
lemma findPerson_Some:"p \<in> set ps \<Longrightarrow> \<exists>idx. findPerson ps p = Some idx"
proof -
  from find_idx_Some have "\<exists>x\<in>set xs. pred x \<Longrightarrow> \<exists>idx. find_idx pred xs = Some idx" for pred xs by metis
  thus "p \<in> set ps \<Longrightarrow> \<exists>idx. findPerson ps p = Some idx" by fastforce
qed
lemma findPerson:"p \<in> set ps \<Longrightarrow> ps!(the (findPerson ps p)) = p" by (auto intro:find_idx)

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
      with Suc.IH have "x \<in> set [0..<k_1]" .
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
      thus ?case using Suc.IH by simp
    next
      assume "x = k_1"
      thus ?case by simp
    qed
  qed
qed

lemma in_perm_upt: "(\<exists>A. (A <~~> [0 ..< k] \<and> x \<in> set A)) \<longleftrightarrow> x < k"
proof
  show "\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A \<Longrightarrow> x < k"
  proof -
    assume "\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A"
    then obtain A where "A <~~> [0..<k]" and "x \<in> set A" by blast
    hence "x \<in> set [0 ..< k]" using perm_set_eq by blast
    thus "x < k" using in_upt by metis
  qed
next
  have "x < k \<Longrightarrow> [0 ..< k] <~~> [0 ..< k] \<and> x \<in> set [0 ..< k]" using in_upt by blast
  thus "x < k \<Longrightarrow> \<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A" by blast
qed

abbreviation is_distinct where
"is_distinct engagements \<equiv> \<forall> m1 < length engagements.
                           \<forall> m2 < length engagements. 
                           m1 \<noteq> m2 \<longrightarrow> engagements!m1 = None \<or> engagements!m1 \<noteq> engagements!m2"

lemma is_matching_intro:
  assumes noFree:"\<forall> wo \<in> set engagements. wo \<noteq> None"
    and distinct:"is_distinct engagements"
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

lemma distinct:"is_distinct engagements \<Longrightarrow> is_distinct (Gale_Shapley' N MPrefs WPrefs engagements prop_idxs)"
proof (induction N MPrefs WPrefs engagements prop_idxs rule:Gale_Shapley'.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?GS' = "Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
  have "length engagements \<noteq> length prop_idxs \<or> length engagements = length prop_idxs" by blast
  thus ?case
  proof
    assume "length engagements \<noteq> length prop_idxs"
    thus ?case using "1.prems" by simp
  next
    assume 0:"length engagements = length prop_idxs"
    have "sum_list prop_idxs \<ge> N * N \<or> sum_list prop_idxs < N * N" by auto
    thus ?case
    proof
      assume "sum_list prop_idxs \<ge> N * N"
      thus ?case using 0 "1.prems" by simp
    next
      assume 1:"sum_list prop_idxs < N * N"
      have "findFreeMan engagements = None \<or> (\<exists>m. findFreeMan engagements = Some m)" using option.exhaust_sel by auto
      thus ?case
      proof
        assume "findFreeMan engagements = None"
        thus ?case using 0 1 "1.prems" by simp
      next
        assume "\<exists>m. findFreeMan engagements = Some m"
        then obtain m where m:"findFreeMan engagements = Some m" by blast
        obtain next_prop_idxs where next_prop_idxs:"next_prop_idxs = prop_idxs[m:=Suc(prop_idxs!m)]" by blast
        moreover obtain w where w:"w = (MPrefs!m)!(prop_idxs!m)" by blast
        moreover have "?GS' = (let w = (MPrefs!m)!(prop_idxs!m);
                                next_prop_idxs = prop_idxs[m:=Suc(prop_idxs!m)] in
                            (case findFiance engagements w of
                             None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
                                    (engagements[m:=Some w]) next_prop_idxs
                           | Some m' \<Rightarrow> (
                             if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
                                                           (engagements[m:=Some w, m':=None]) next_prop_idxs
                                                      else Gale_Shapley' N MPrefs WPrefs
                                                            engagements next_prop_idxs)))" using 0 1 m by simp
        ultimately have GS_m:"?GS' = (case findFiance engagements w of
                             None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
                                    (engagements[m:=Some w]) next_prop_idxs
                           | Some m' \<Rightarrow> (
                             if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
                                                           (engagements[m:=Some w, m':=None]) next_prop_idxs
                                                      else Gale_Shapley' N MPrefs WPrefs
                                                            engagements next_prop_idxs))" by meson
        have "findFiance engagements w = None \<or> (\<exists>m'. findFiance engagements w = Some m')" using option.exhaust_sel by auto
        thus ?case
        proof
          assume w_single:"findFiance engagements w = None"
          hence GS:"?GS' = Gale_Shapley' N MPrefs WPrefs (engagements[m:=Some w]) next_prop_idxs" using GS_m by simp
          from w_single have "\<forall> m < length engagements. engagements!m \<noteq> Some w" using findFiance_None by auto
          with "1.prems" have "is_distinct (engagements[m:=Some w])" by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
          thus ?case using "1.IH"(1) 0 1 m w next_prop_idxs w_single GS by auto
        next
          assume "\<exists>m'. findFiance engagements w = Some m'"
          then obtain m' where m':"findFiance engagements w = Some m'" by auto
          hence GS_m':"?GS' = (if prefers w WPrefs m m'
                               then Gale_Shapley' N MPrefs WPrefs (engagements[m:=Some w, m':=None]) next_prop_idxs
                               else Gale_Shapley' N MPrefs WPrefs engagements next_prop_idxs)" using GS_m by simp
          have "prefers w WPrefs m m' \<or> \<not> prefers w WPrefs m m'" by simp
          thus ?case
          proof
            assume change:"prefers w WPrefs m m'"
            hence GS:"?GS' = Gale_Shapley' N MPrefs WPrefs (engagements[m:=Some w, m':=None]) next_prop_idxs" using GS_m' by simp
            from m' findFiance findFiance_bound have "m' < length engagements \<and> engagements!m' = Some w" by simp
            moreover hence "\<forall>m < length engagements. m \<noteq> m' \<longrightarrow> engagements!m \<noteq> Some w" using "1.prems" by fastforce
            ultimately have "is_distinct (engagements[m:=Some w, m':=None])" using "1.prems" by (metis length_list_update nth_list_update nth_list_update_neq)
            thus ?case using "1.IH"(2) 0 1 m w next_prop_idxs m' change GS by auto
          next
            assume "\<not> prefers w WPrefs m m'"
            moreover hence "?GS' = Gale_Shapley' N MPrefs WPrefs engagements next_prop_idxs" using GS_m' by simp
            ultimately show ?case using "1.IH"(3) 0 1 m w next_prop_idxs m' "1.prems" by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma "is_distinct (Gale_Shapley MPrefs WPrefs)"
proof -
  obtain N where "N = length MPrefs" by blast
  hence "Gale_Shapley MPrefs WPrefs = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by (meson Gale_Shapley.simps)
  moreover have "is_distinct (replicate N None)" by simp
  ultimately show ?thesis using distinct by metis
qed
end
