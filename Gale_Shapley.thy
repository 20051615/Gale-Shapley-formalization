theory Gale_Shapley
  imports "HOL-Library.Permutation" List_Ops
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

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

lemma in_perm_upt: "x < k \<longleftrightarrow> (\<forall>A. A <~~> [0 ..< k] \<longrightarrow> x \<in> set A)"
proof
  assume "x < k"
  show "\<forall>A. A <~~> [0 ..< k] \<longrightarrow> x \<in> set A"
  proof
    fix A
    show "A <~~> [0 ..< k] \<longrightarrow> x \<in> set A"
    proof
      assume "A <~~> [0 ..< k]"
      hence "set A = set [0 ..< k]" by (metis perm_set_eq)
      with `x < k` in_upt show "x \<in> set A" by metis
    qed
  qed
next
  assume "\<forall>A. A <~~> [0 ..< k] \<longrightarrow> x \<in> set A"
  moreover have "[0 ..< k] <~~> [0 ..< k]" by auto
  ultimately have "x \<in> set [0 ..< k]" by blast
  thus "x < k" using in_upt by metis
qed

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
"prefers p PPrefs p1 p2 = (
  case findPerson (PPrefs!p) p1 of None \<Rightarrow> False |
                                   Some idx_1 \<Rightarrow> (
    case findPerson (PPrefs!p) p2 of None \<Rightarrow> False |
                                     Some idx_2 \<Rightarrow> idx_1 \<le> idx_2))"

lemma prefers_trans:
  assumes 0:"prefers p PPrefs p1 p2"
      and 1:"prefers p PPrefs p2 p3"
    shows "prefers p PPrefs p1 p3"
proof (cases "findPerson (PPrefs!p) p1")
  case None
  hence False using 0 by simp
  thus ?thesis by simp
next
  case (Some idx_1)
  then obtain idx_1 where idx_1:"findPerson (PPrefs!p) p1 = Some idx_1" by blast
  show ?thesis
  proof (cases "findPerson (PPrefs!p) p2")
    case None
    hence False using 0 idx_1 by simp
    thus ?thesis by simp
  next
    case (Some idx_2)
    then obtain idx_2 where idx_2:"findPerson (PPrefs!p) p2 = Some idx_2" by blast
    hence "idx_1 \<le> idx_2" using 0 idx_1 by simp
    show ?thesis
    proof (cases "findPerson (PPrefs!p) p3")
      case None
      hence False using 1 idx_2 by simp
      thus ?thesis by simp
    next
      case (Some idx_3)
      hence "idx_2 \<le> idx_3" using 1 idx_2 by simp
      with `idx_1 \<le> idx_2` have "idx_1 \<le> idx_3" by simp
      with idx_1 Some show ?thesis by simp
    qed
  qed
qed

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

abbreviation is_terminal where
"is_terminal N engagements prop_idxs \<equiv> length engagements \<noteq> length prop_idxs \<or> sum_list prop_idxs \<ge> N * N \<or> findFreeMan engagements = None"

lemma GS'_arg_seq_non_Nil:"GS'_arg_seq N MPrefs WPrefs engagements prop_idxs \<noteq> []"
proof cases
  assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
  then obtain m where m:"findFreeMan engagements = Some m" by auto
  let ?w = "MPrefs!m!(prop_idxs!m)"
  show ?thesis
  proof (cases "findFiance engagements ?w")
    case None
    thus ?thesis using m by (simp add:Let_def)
  next
    case (Some m')
    thus ?thesis using m by (simp add:Let_def)
  qed
next
  assume "\<not>\<not>is_terminal N engagements prop_idxs"
  thus ?thesis by auto
qed

lemma GS'_arg_seq_first_is_start:
  assumes asm:"(X, Y) # xys = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  shows "(X, Y) = (engagements, prop_idxs)"
proof cases
  assume "is_terminal N engagements prop_idxs"
  with asm have "(X, Y) # xys = (engagements, prop_idxs) # []" by auto
  thus ?thesis by simp
next
  assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
  then obtain m where m:"findFreeMan engagements = Some m" by auto
  let ?w = "MPrefs!m!(prop_idxs!m)"
  let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
  show ?thesis
  proof (cases "findFiance engagements ?w")
    case None
    thus ?thesis using non_terminal m asm by (simp add:Let_def)
  next
    case (Some m')
    show ?thesis
    proof cases
      assume "prefers ?w WPrefs m m'"
      thus ?thesis using non_terminal m Some asm by (simp add:Let_def)
    next
      assume "\<not> prefers ?w WPrefs m m'"
      thus ?thesis using non_terminal m Some asm by (simp add:Let_def)
    qed
  qed
qed

lemma GS'_arg_seq_first_is_start_idx:"(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)!0 = (engagements, prop_idxs)" using GS'_arg_seq_first_is_start GS'_arg_seq_non_Nil by (metis list.exhaust nth_Cons_0 surj_pair)

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
    show ?case
    proof (cases "findFiance engagements ?w")
      case None
      hence "tl = GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs" using Cons.hyps(2) non_terminal m by (simp add:Let_def)
      moreover with Cons.prems Cons.hyps(2) GS'_arg_seq_non_Nil have "(X, Y) = last tl" by (metis last.simps)
      ultimately show ?thesis using Cons.hyps(1) by metis
    next
      case (Some m')
      show ?thesis
      proof cases
        assume "prefers ?w WPrefs m m'"
        hence "tl = GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs" using Cons.hyps(2) non_terminal m Some by (simp add:Let_def)
        moreover with Cons.prems Cons.hyps(2) GS'_arg_seq_non_Nil have "(X, Y) = last tl" by (metis last.simps)
        ultimately show ?thesis using Cons.hyps(1) by metis
      next
        assume "\<not> prefers ?w WPrefs m m'"
        hence "tl = GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs" using Cons.hyps(2) non_terminal m Some by (simp add:Let_def)
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
    show ?case
    proof cases
      assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
      then obtain m where m:"findFreeMan engagements = Some m" by auto
      let ?w = "MPrefs!m!(prop_idxs!m)"
      let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs)" using not_init "1.prems" non_terminal m by (auto simp add:Let_def)
        ultimately show ?thesis using "1.IH"(1) non_terminal m by simp
      next
        case (Some m')
        show ?thesis
        proof cases
          assume "prefers ?w WPrefs m m'"
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)" using not_init "1.prems" non_terminal m Some by (auto simp add:Let_def)
          ultimately show ?thesis using "1.IH"(2) non_terminal m Some by simp
        next
          assume "\<not> prefers ?w WPrefs m m'"
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs)" using not_init "1.prems" non_terminal m Some by (auto simp add:Let_def)
          ultimately show ?thesis using "1.IH"(3) non_terminal m Some by simp
        qed
      qed
    next
      assume "\<not>\<not> is_terminal N engagements prop_idxs"
      thus ?thesis using "1.prems" by auto
    qed
  next
    assume "\<not>(X, Y) \<noteq> (engagements, prop_idxs)"
    thus ?case by simp
  qed
qed

theorem GS'_arg_seq_computes_GS':"Gale_Shapley' N MPrefs WPrefs engagements prop_idxs = fst (last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
proof -
  let ?X = "fst(last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
  let ?Y = "snd(last (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs))"
  from GS'_arg_seq_last_is_terminal have "is_terminal N ?X ?Y" by simp
  moreover from GS'_arg_seq_non_Nil GS'_arg_seq_same_endpoint have "Gale_Shapley' N MPrefs WPrefs engagements prop_idxs = Gale_Shapley' N MPrefs WPrefs ?X ?Y" by auto
  ultimately show ?thesis by auto
qed

abbreviation is_distinct where
"is_distinct engagements \<equiv> \<forall> m1 < length engagements.
                           \<forall> m2 < length engagements. 
                           m1 \<noteq> m2 \<longrightarrow> engagements!m1 = None \<or> engagements!m1 \<noteq> engagements!m2"

abbreviation is_bounded where
"is_bounded engagements \<equiv> \<forall> wo \<in> set engagements. wo \<noteq> None \<longrightarrow> the wo < length engagements"

lemma is_matching_intro:
  assumes noFree:"\<forall> wo \<in> set engagements. wo \<noteq> None"
    and "is_distinct engagements"
    and "is_bounded engagements"
  shows "engagements <~~> map Some [0 ..< length engagements]"
proof -
  let ?engagements = "map the engagements"
  let ?N = "length engagements"
  from noFree have "\<forall> wo \<in> set engagements. wo = Some (the wo)" using option.exhaust_sel by blast
  hence engagements:"engagements = map Some ?engagements" by (simp add: nth_equalityI)

  from `is_bounded engagements` noFree have bounded_the:"\<forall> w \<in> set ?engagements. w < ?N" by simp
  from noFree have "\<forall> m < length engagements. engagements!m \<noteq> None" by simp
  moreover with `is_distinct engagements` have "\<forall> m1 < length engagements. \<forall> m2 < length engagements.
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

lemma GS'_arg_seq_all_distinct:"\<lbrakk>is_distinct engagements; (X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)\<rbrakk> \<Longrightarrow> is_distinct X"
proof (induction N MPrefs WPrefs engagements prop_idxs rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    hence "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs = [(engagements, prop_idxs)]" by auto
    hence "(X, Y) = (engagements, prop_idxs)" using "1.prems"(2) by simp
    thus ?case using "1.prems"(1) by simp
  next
    assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
    then obtain m where m:"findFreeMan engagements = Some m" by auto
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc (prop_idxs!m)]"
    show ?case
    proof cases
      assume "(X, Y) = (engagements, prop_idxs)"
      thus ?case using "1.prems"(1) by simp
    next
      assume not_init:"(X, Y) \<noteq> (engagements, prop_idxs)"
      show ?case
      proof (cases "findFiance engagements ?w")
        case None
        hence "\<forall> m < length engagements. engagements!m \<noteq> Some ?w" using findFiance_None by simp
        with "1.prems" have "is_distinct (engagements[m:=Some ?w])" by (metis (full_types) length_list_update nth_list_update nth_list_update_neq)
        moreover from "1.prems"(2) not_init non_terminal m None have "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs)" by (auto simp add:Let_def)
        ultimately show ?thesis using "1.IH"(1) non_terminal m None by simp
      next
        case (Some m')
        show ?thesis
        proof cases
          from Some findFiance findFiance_bound have "m' < length engagements \<and> engagements!m' = Some ?w" by simp
          moreover hence "\<forall>m < length engagements. m \<noteq> m' \<longrightarrow> engagements!m \<noteq> Some ?w" using "1.prems"(1) by fastforce
          ultimately have "is_distinct (engagements[m:=Some ?w, m':=None])" using "1.prems"(1) by (metis length_list_update nth_list_update nth_list_update_neq)
          moreover assume "prefers ?w WPrefs m m'"
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)" using non_terminal m Some not_init "1.prems"(2) by (auto simp add:Let_def)
          ultimately show ?thesis using "1.IH"(2) non_terminal m Some by metis
        next
          assume "\<not> prefers ?w WPrefs m m'"
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs)" using non_terminal m Some not_init "1.prems"(2) by (auto simp add:Let_def)
          ultimately show ?thesis using "1.IH"(3) non_terminal m Some "1.prems"(1) by metis
        qed
      qed
    qed
  qed
qed

lemma "is_distinct (Gale_Shapley MPrefs WPrefs)"
proof -
  let ?N = "length MPrefs"
  have "Gale_Shapley MPrefs WPrefs = Gale_Shapley' ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0)" by (simp add:Let_def)
  hence "Gale_Shapley MPrefs WPrefs = fst (last (GS'_arg_seq ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0)))" using GS'_arg_seq_computes_GS' by metis
  then obtain Y where "(Gale_Shapley MPrefs WPrefs, Y) \<in> set (GS'_arg_seq ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0))" using GS'_arg_seq_non_Nil by (metis eq_fst_iff last_in_set)
  moreover have "is_distinct (replicate ?N None)" by simp
  ultimately show ?thesis using GS'_arg_seq_all_distinct by blast
qed

fun married_better::"woman \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> matching \<Rightarrow> bool" where
"married_better w WPrefs eng_1 eng_2 = (if findFiance eng_1 w = None then 
                                          True
                                        else (
                                          let m_1 = the (findFiance eng_1 w) in (
                                          if findFiance eng_2 w = None then
                                            False
                                          else (
                                            let m_2 = the (findFiance eng_2 w) in
                                            prefers w WPrefs m_2 m_1))))"

lemma married_better_trans:
  assumes 0:"married_better w WPrefs eng_1 eng_2"
      and 1:"married_better w WPrefs eng_2 eng_3"
    shows "married_better w WPrefs eng_1 eng_3"
proof -
  let ?m_1 = "the (findFiance eng_1 w)"
  let ?m_2 = "the (findFiance eng_2 w)"
  let ?m_3 = "the (findFiance eng_3 w)"
  from 0 have "findFiance eng_1 w = None \<or> (findFiance eng_2 w \<noteq> None \<and> prefers w WPrefs ?m_2 ?m_1)" by (metis married_better.simps)
  thus ?thesis
  proof
    assume "findFiance eng_1 w = None"
    thus ?thesis by (metis married_better.simps)
  next
    assume asm:"findFiance eng_2 w \<noteq> None \<and> prefers w WPrefs ?m_2 ?m_1"
    moreover with 1 have "prefers w WPrefs ?m_3 ?m_2" by (metis married_better.simps)
    ultimately have "prefers w WPrefs ?m_3 ?m_1" using prefers_trans by metis
    moreover from asm 1 have "findFiance eng_3 w \<noteq> None" by (metis married_better.simps)
    ultimately show ?thesis by (metis married_better.simps)
  qed
qed

lemma GS'_arg_seq_all_w_marry_better:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; w < N; i < length seq; j < length seq; i < j\<rbrakk> \<Longrightarrow> married_better w WPrefs (fst(seq!i)) (fst(seq!j))"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i j rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    hence "?seq = [(engagements, prop_idxs)]" by auto
    hence "length seq = 1" using "1.prems"(1) by simp
    hence False using "1.prems" by auto
    thus ?case by simp
  next
    assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
    then obtain m where m:"findFreeMan engagements = Some m" by auto
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
    show ?case
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
      from None have seq_tl:"?seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
      hence length:"length seq = Suc (length ?seq_tl)" using "1.prems"(1) by simp
      moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc (j_1)" by (metis Nat.lessE)
      ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
      show ?thesis
      proof (cases i)
        case (Suc i_1)
        with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
        with "1.IH"(1) "1.prems"(2) `j_1 < length ?seq_tl` non_terminal m None have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
        thus ?thesis using seq_tl Suc j_1 `seq = ?seq` by simp
      next
        case 0
        with seq_tl `seq = ?seq` have "fst(seq!i) = engagements" by simp
        have "fst(?seq_tl!0) = (engagements [m:=Some ?w])" by (metis GS'_arg_seq_first_is_start_idx fstI)
        moreover from GS'_arg_seq_non_Nil have "0 < length ?seq_tl" by blast
        ultimately have "married_better w WPrefs (engagements [m:=Some ?w]) (fst(?seq_tl!j_1))" using "1.IH"(1) non_terminal m None `j_1 < length ?seq_tl` "1.prems"(2)



(* first prove that prop_idxs is always well_behaved with all terms < N throughout argument sequence *)
(* this is probably very non-trivial *)
(* only then can show bounded, etc. *)
(* essentially have to show that, when a man has proposed to all, he is necessarily never free again... *)
(* from this, bounded AND noFree becomes trivial *)
end
