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
  thus "findFiance engagements w = Some m' \<Longrightarrow> engagements!m' = Some w" using findFiance.elims by fastforce
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

 Some m \<Rightarrow> (let w = MPrefs!m!(prop_idxs!m);
   next_prop_idxs = prop_idxs[m:=Suc (prop_idxs!m)] in (
   case findFiance engagements w of
     None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
       (engagements[m:=Some w]) next_prop_idxs
   | Some m' \<Rightarrow> (
     if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
       (engagements[m:=Some w, m':=None]) next_prop_idxs
     else Gale_Shapley' N MPrefs WPrefs
       engagements next_prop_idxs
))))))"
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(N, _, _, _, prop_idxs). N * N - sum_list prop_idxs)")
  by (auto intro:termination_aid)

fun Gale_Shapley::"pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching" where
"Gale_Shapley MPrefs WPrefs = (let N = length MPrefs in
 Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0))"

function GS'_arg_seq::"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> nat list \<Rightarrow> (matching \<times> nat list) list" where
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
       engagements next_prop_idxs)
))))))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(N, _, _, _, prop_idxs). N * N - sum_list prop_idxs)")
  by (auto intro:termination_aid)

lemma GS'_arg_seq_non_Nil:"GS'_arg_seq N MPrefs WPrefs engagements prop_idxs \<noteq> []"
proof cases
  assume 0:"length engagements = length prop_idxs"
  show ?thesis
  proof cases
    assume 1:"sum_list prop_idxs < N * N"
    show ?thesis
    proof (cases "findFreeMan engagements")
      case None
      thus ?thesis by simp
    next
      case (Some m)
      hence m:"findFreeMan engagements = Some m" .
      let ?w = "MPrefs!m!(prop_idxs!m)"
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        thus ?thesis using m by (simp add:Let_def)
      next
        case (Some m')
        thus ?thesis using m by (simp add:Let_def)
      qed
    qed
  next
    assume "\<not>sum_list prop_idxs < N * N"
    thus ?thesis by simp
  qed
next
  assume "length engagements \<noteq> length prop_idxs"
  thus ?thesis by simp
qed

abbreviation is_terminal where
"is_terminal N engagements prop_idxs \<equiv> length engagements \<noteq> length prop_idxs \<or> sum_list prop_idxs \<ge> N * N \<or> findFreeMan engagements = None"

lemma GS'_arg_seq_last_is_terminal:"(X, Y) = last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) \<Longrightarrow> is_terminal N X Y"
proof (induction "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs" arbitrary:engagements prop_idxs)
  case Nil
  from Nil.hyps GS'_arg_seq_non_Nil have False by metis
  thus ?case by simp
next
  case (Cons hd tl)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    moreover hence "(X, Y) = (engagements, prop_idxs)" using Cons.prems by auto
    ultimately show ?case by simp
  next
    assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
    then obtain m where m:"findFreeMan engagements = Some m" by auto
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc (prop_idxs!m)]"
    let ?GS'_arg_seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
    from non_terminal m have GS_arg_seq:"?GS'_arg_seq = (case findFiance engagements ?w of
                              None \<Rightarrow> (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                 (engagements[m:=Some ?w]) ?next_prop_idxs)
                            | Some m' \<Rightarrow> (
                              if prefers ?w WPrefs m m' then (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                                       (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)
                                                       else (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                                        engagements ?next_prop_idxs)))" by (simp add:Let_def)
    show ?case
    proof (cases "findFiance engagements ?w")
      case None
      hence "tl = GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs" using Cons.hyps(2) GS_arg_seq by simp
      moreover with Cons.prems Cons.hyps(2) GS'_arg_seq_non_Nil have "(X, Y) = last tl" by (metis last.simps)
      ultimately show ?thesis using Cons.hyps(1) by metis
    next
      case (Some m')
      show ?thesis
      proof cases
        assume "prefers ?w WPrefs m m'"
        hence "tl = GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs" using Cons.hyps(2) GS_arg_seq Some by simp
        moreover with Cons.prems Cons.hyps(2) GS'_arg_seq_non_Nil have "(X, Y) = last tl" by (metis last.simps)
        ultimately show ?thesis using Cons.hyps(1) by metis
      next
        assume "\<not> prefers ?w WPrefs m m'"
        hence "tl = GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs" using Cons.hyps(2) GS_arg_seq Some by simp
        moreover with Cons.prems Cons.hyps(2) GS'_arg_seq_non_Nil have "(X, Y) = last tl" by (metis last.simps)
        ultimately show ?thesis using Cons.hyps(1) by metis
      qed
    qed
  qed
qed

lemma GS'_arg_seq_same_endpoint:"(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs) \<Longrightarrow> (Gale_Shapley' N MPrefs WPrefs engagements prop_idxs) = (Gale_Shapley' N MPrefs WPrefs X Y)"
proof (induction N MPrefs WPrefs engagements prop_idxs rule:Gale_Shapley'.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume not_init:"(X, Y) \<noteq> (engagements, prop_idxs)"
    let ?GS' = "Gale_Shapley' N MPrefs WPrefs engagements prop_idxs"
    let ?GS'_arg_seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
    show ?case
    proof cases
      assume 0:"length engagements = length prop_idxs"
      show ?case
      proof cases
        assume 1:"sum_list prop_idxs < N * N"
        show ?case
        proof (cases "findFreeMan engagements")
          case (Some m)
          hence m:"findFreeMan engagements = Some m" .
          let ?w = "MPrefs!m!(prop_idxs!m)"
          let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
          have GS:"?GS' = (case findFiance engagements ?w of
                               None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
                                      (engagements[m:=Some ?w]) ?next_prop_idxs
                             | Some m' \<Rightarrow> (
                               if prefers ?w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
                                                             (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs
                                                        else Gale_Shapley' N MPrefs WPrefs
                                                              engagements ?next_prop_idxs))" using 0 1 m by (simp add:Let_def)
          have GS_arg_seq:"?GS'_arg_seq = (case findFiance engagements ?w of
                              None \<Rightarrow> (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                 (engagements[m:=Some ?w]) ?next_prop_idxs)
                            | Some m' \<Rightarrow> (
                              if prefers ?w WPrefs m m' then (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                                       (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)
                                                       else (engagements, prop_idxs) # (GS'_arg_seq N MPrefs WPrefs
                                                                                        engagements ?next_prop_idxs)))" using 0 1 m by (simp add:Let_def)
          show ?thesis
          proof (cases "findFiance engagements ?w")
            case None
            moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs)" using not_init "1.prems" GS_arg_seq by auto
            ultimately show ?thesis using "1.IH"(1) GS 0 1 m by simp
          next
            case (Some m')
            show ?thesis
            proof cases
              assume "prefers ?w WPrefs m m'"
              moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)" using not_init "1.prems" GS_arg_seq Some by auto
              ultimately show ?thesis using "1.IH"(2) GS 0 1 m Some by simp
            next
              assume "\<not> prefers ?w WPrefs m m'"
              moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs)" using not_init "1.prems" GS_arg_seq Some by auto
              ultimately show ?thesis using "1.IH"(3) GS 0 1 m Some by simp
            qed
          qed
        next
          case None
          thus ?thesis using 0 1 "1.prems" by simp
        qed
      next
        assume "\<not>sum_list prop_idxs < N * N"
        thus ?case using 0 "1.prems" by simp
      qed
    next
      assume "length engagements \<noteq> length prop_idxs"
      thus ?case using "1.prems" by simp
    qed
  next
    assume "\<not>(X, Y) \<noteq> (engagements, prop_idxs)"
    thus ?case by simp
  qed
qed

lemma GS'_arg_seq_computes_GS':"Gale_Shapley' N MPrefs WPrefs engagements prop_idxs = fst (last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
proof -
  let ?X = "fst(last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
  let ?Y = "snd(last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
  from GS'_arg_seq_last_is_terminal have "is_terminal N ?X ?Y" by simp
  moreover from GS'_arg_seq_non_Nil GS'_arg_seq_same_endpoint have "Gale_Shapley' N MPrefs WPrefs engagements prop_idxs = Gale_Shapley' N MPrefs WPrefs ?X ?Y" by auto
  ultimately show ?thesis by auto
qed

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
  show ?case
  proof cases
    assume 0:"length engagements = length prop_idxs"
    show ?case
    proof cases
      assume 1:"sum_list prop_idxs < N * N"
      show ?case
      proof (cases "findFreeMan engagements")
        case (Some m)
        hence m:"findFreeMan engagements = Some m" .
        let ?w = "MPrefs!m!(prop_idxs!m)"
        let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
        have GS:"?GS' = (case findFiance engagements ?w of
                             None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
                                    (engagements[m:=Some ?w]) ?next_prop_idxs
                           | Some m' \<Rightarrow> (
                             if prefers ?w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
                                                           (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs
                                                       else Gale_Shapley' N MPrefs WPrefs
                                                            engagements ?next_prop_idxs))" using 0 1 m by (simp add:Let_def)
        show ?thesis
        proof (cases "findFiance engagements ?w")
          case None
          hence "\<forall> m < length engagements. engagements!m \<noteq> Some ?w" using findFiance_None by simp
          with "1.prems" have "is_distinct (engagements[m:=Some ?w])" by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
          thus ?thesis using "1.IH"(1) 0 1 m None GS by simp
        next
          case (Some m')
          show ?thesis
          proof cases
            from Some findFiance findFiance_bound have "m' < length engagements \<and> engagements!m' = Some ?w" by simp
            moreover hence "\<forall>m < length engagements. m \<noteq> m' \<longrightarrow> engagements!m \<noteq> Some ?w" using "1.prems" by fastforce
            ultimately have "is_distinct (engagements[m:=Some ?w, m':=None])" using "1.prems" by (metis length_list_update nth_list_update nth_list_update_neq)
            moreover assume "prefers ?w WPrefs m m'"
            ultimately show ?thesis using "1.IH"(2) 0 1 m Some GS by simp
          next
            assume "\<not> prefers ?w WPrefs m m'"
            thus ?thesis using "1.IH"(3) 0 1 m Some GS "1.prems" by simp
          qed
        qed
      next
        case None
        thus ?thesis using 0 1 "1.prems" by simp
      qed
    next
      assume "\<not>sum_list prop_idxs < N * N"
      thus ?case using 0 "1.prems" by simp
    qed
  next
    assume "length engagements \<noteq> length prop_idxs"
    thus ?case using "1.prems" by simp
  qed
qed

lemma "is_distinct (Gale_Shapley MPrefs WPrefs)"
proof -
  let ?N = "length MPrefs"
  have "Gale_Shapley MPrefs WPrefs = Gale_Shapley' ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0)" by (simp add:Let_def)
  moreover have "is_distinct (replicate ?N None)" by simp
  ultimately show ?thesis using distinct by metis
qed
end
