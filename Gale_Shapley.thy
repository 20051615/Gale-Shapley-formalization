theory Gale_Shapley
  imports "HOL-Library.Permutation" List_Ops
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

lemma in_upt:"x < k \<longleftrightarrow> x \<in> set [0 ..< k]" by simp
lemma in_perm_upt: "x < k \<longleftrightarrow> (\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A)" using in_upt perm_refl perm_set_eq by metis

fun is_perm::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" where "is_perm A B = (mset A = mset B)"
lemma is_perm:"is_perm A B \<longleftrightarrow> A <~~> B" using mset_eq_perm by auto
fun is_valid_pref_matrix::"nat \<Rightarrow> pref_matrix \<Rightarrow> bool" where
"is_valid_pref_matrix N PPrefs = (if length PPrefs \<noteq> N then False else Ball (set PPrefs) (is_perm [0 ..< N]))"
lemma length_PPrefs:"is_valid_pref_matrix N PPrefs \<Longrightarrow> length PPrefs = N" using is_valid_pref_matrix.simps by metis
lemma perm_PPref:"\<lbrakk>is_valid_pref_matrix N PPrefs; m < N\<rbrakk> \<Longrightarrow> PPrefs!m <~~> [0 ..< N]"  using is_valid_pref_matrix.simps nth_mem is_perm perm_sym by metis

fun findFreeMan::"matching \<Rightarrow> man option" where
"findFreeMan engagements = find_idx None engagements"
lemma findFreeMan_bound:"findFreeMan engagements = Some m \<Longrightarrow> m < length engagements" using find_idx_bound by simp
lemma findFreeMan_None:"findFreeMan engagements = None \<longleftrightarrow> None \<notin> set engagements" using find_idx_None by fastforce
lemma findFreeMan:"findFreeMan engagements = Some m \<Longrightarrow> engagements!m = None" using find_idx find_idx_Some by fastforce

fun findFiance::"matching \<Rightarrow> woman \<Rightarrow> man option" where
"findFiance engagements w = find_idx (Some w) engagements"
lemma findFiance_bound:"findFiance engagements w = Some m \<Longrightarrow> m < length engagements" using find_idx_bound by simp
lemma findFiance_Some:"findFiance engagements w \<noteq> None \<longleftrightarrow> Some w \<in> set engagements" using find_idx_Some by fastforce
lemma findFiance_None:"findFiance engagements w = None \<longleftrightarrow> Some w \<notin> set engagements" using findFiance_Some by blast
lemma findFiance_Some_is_first:"\<lbrakk>findFiance engagements w = Some m; m' < m\<rbrakk> \<Longrightarrow> engagements!m' \<noteq> Some w" using find_idx_Some_is_first by fastforce
lemma findFiance_first_is_Some:"\<lbrakk>m < length engagements; \<forall>m'<m. engagements!m'\<noteq>Some w; engagements!m = Some w\<rbrakk> \<Longrightarrow> findFiance engagements w = Some m" using find_idx_first_is_Some by force
lemma findFiance:"findFiance engagements w = Some m \<Longrightarrow> engagements!m = Some w" using find_idx find_idx_Some by fastforce

fun findPerson::"person list \<Rightarrow> person \<Rightarrow> nat option" where
"findPerson ps p = find_idx p ps"
lemma findPerson_Some:"findPerson ps p \<noteq> None \<longleftrightarrow> p \<in> set ps" using find_idx_Some by fastforce

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
  ultimately show ?thesis using idx_1 idx_3 by force
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
    thus ?case
      apply (cases m)
      by (simp_all)
  qed
  ultimately have "sum_list next_prop_idxs = Suc (sum_list prop_idxs)" using 3 by blast
  with 4 show ?thesis by simp
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
  assume "is_terminal N engagements prop_idxs"
  thus ?thesis by auto
next
  assume "\<not> is_terminal N engagements prop_idxs"
  then obtain m where "findFreeMan engagements = Some m" by blast
  thus ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma GS'_arg_seq_0 [simp]:"(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)!0 = (engagements, prop_idxs)"
proof cases
  assume "is_terminal N engagements prop_idxs"
  thus ?thesis by force
next
  assume "\<not> is_terminal N engagements prop_idxs"
  moreover then obtain m where "findFreeMan engagements = Some m" by blast
  ultimately show ?thesis
    apply (cases "findFiance engagements (MPrefs!m!(prop_idxs!m))")
    by (simp_all add:Let_def)
qed

lemma GS'_arg_seq_snd_1: (* prove this using _step instead? *) (* prove a general case of this using _step, and instantiate this. as a simp rule too, use simp del *)
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and non_terminal:"\<not>is_terminal N engagements prop_idxs"
      and m:"findFreeMan engagements = Some m"
    shows "snd(seq!1) = prop_idxs[m:=Suc(prop_idxs!m)]"
proof -
  let ?w = "MPrefs!m!(prop_idxs!m)"
  let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
  show ?thesis
  proof (cases "findFiance engagements ?w")
    case None
    let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
    from non_terminal m None seq have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
    thus ?thesis by (simp del:GS'_arg_seq.simps)
  next
    case (Some m')
    show ?thesis
    proof cases
      assume change:"prefers ?w WPrefs m m'"
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
      from non_terminal m Some change seq have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      thus ?thesis by (simp del:GS'_arg_seq.simps)
    next
      assume no_change:"\<not> prefers ?w WPrefs m m'"
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
      from non_terminal m Some no_change seq have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      thus ?thesis by (simp del:GS'_arg_seq.simps)
    qed
  qed
qed

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
        hence "tl = GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs" using Cons.hyps(2) non_terminal m Some by (simp add:Let_def del:prefers.simps)
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

lemma GS'_arg_seq_terminal_is_last:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); is_terminal N X Y\<rbrakk> \<Longrightarrow> length seq = Suc i"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof (cases i)
    case 0
    with "1.prems"(1-3) have "(X, Y) = (engagements, prop_idxs)" by (simp del:GS'_arg_seq.simps)
    with "1.prems"(4) have "is_terminal N engagements prop_idxs" by simp
    hence "seq = [(engagements, prop_idxs)]" using "1.prems"(1) by auto
    with "1.prems"(2) show ?thesis by simp
  next
    case (Suc i_1)
    have non_terminal:"\<not> is_terminal N engagements prop_idxs"
    proof
      assume "is_terminal N engagements prop_idxs"
      hence "seq = [(engagements, prop_idxs)]" using "1.prems"(1) by auto
      with "1.prems"(2) Suc show False by simp
    qed
    then obtain m where m:"findFreeMan engagements = Some m" by auto
    let ?w = "MPrefs!m!(prop_idxs!m)"
    let ?next_prop_idxs = "prop_idxs[m:=Suc(prop_idxs!m)]"
    show ?thesis
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w]) ?next_prop_idxs"
      from "1.prems"(1) non_terminal m None have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      moreover with "1.prems"(2) Suc have "i_1 < length ?seq_tl" by simp
      moreover with "1.prems"(3) Suc seq_tl have "?seq_tl!i_1 = (X, Y)" by simp
      ultimately have "length ?seq_tl = Suc i_1" using "1.prems"(4) "1.IH"(1) using non_terminal m None by metis
      thus ?thesis using seq_tl Suc by simp
    next
      case (Some m')
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
        from "1.prems"(1) non_terminal m Some change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        moreover with "1.prems"(2) Suc have "i_1 < length ?seq_tl" by simp
        moreover with "1.prems"(3) Suc seq_tl have "?seq_tl!i_1 = (X, Y)" by simp
        ultimately have "length ?seq_tl = Suc i_1" using "1.prems"(4) "1.IH"(2) using non_terminal m Some change by metis
        thus ?thesis using seq_tl Suc by simp
      next
        assume no_change:"\<not> prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from "1.prems"(1) non_terminal m Some no_change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        moreover with "1.prems"(2) Suc have "i_1 < length ?seq_tl" by simp
        moreover with "1.prems"(3) Suc seq_tl have "?seq_tl!i_1 = (X, Y)" by simp
        ultimately have "length ?seq_tl = Suc i_1" using "1.prems"(4) "1.IH"(3) using non_terminal m Some no_change by metis
        thus ?thesis using seq_tl Suc by simp
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
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)" using not_init "1.prems" non_terminal m Some by (auto simp add:Let_def simp del:prefers.simps)
          ultimately show ?thesis using "1.IH"(2) non_terminal m Some by (simp del:prefers.simps)
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

lemma GS'_arg_seq_preserves_length:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; (X, Y) \<in> set seq\<rbrakk> \<Longrightarrow> length X = length engagements \<and> length Y = length prop_idxs"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary: seq rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show ?case
  proof cases
    assume "(X, Y) = (engagements, prop_idxs)"
    thus ?case by simp
  next
    assume not_first:"(X, Y) \<noteq> (engagements, prop_idxs)"
    show ?case
    proof cases
      assume "is_terminal N engagements prop_idxs"
      hence "seq = [(engagements, prop_idxs)]" using `seq = ?seq` by auto
      hence False using "1.prems"(2) not_first by simp
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
        from None `seq = ?seq` have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        with not_first "1.prems"(2) have "(X, Y) \<in> set ?seq_tl" by auto
        with "1.IH"(1) non_terminal m None show ?thesis by simp
      next
        case (Some m')
        show ?thesis
        proof cases
          assume change:"prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
          from Some change `seq = ?seq` have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
          with not_first "1.prems"(2) have "(X, Y) \<in> set ?seq_tl" by auto
          with "1.IH"(2) non_terminal m Some change show ?thesis by simp
        next
          assume no_change:"\<not>prefers ?w WPrefs m m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
          from Some no_change `seq = ?seq` have "seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
          with not_first "1.prems"(2) have "(X, Y) \<in> set ?seq_tl" by auto
          with "1.IH"(3) non_terminal m Some no_change show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_step_1:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = None\<rbrakk> \<Longrightarrow> seq!Suc i = (X[m:=Some w], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by auto
    ultimately have False using "1.prems"(2-4) by simp
    thus ?case by simp
  next
    assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
    then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by auto
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
qed

lemma GS'_arg_seq_step_2:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; prefers w WPrefs m m'\<rbrakk> \<Longrightarrow> seq!Suc i = (X[m:=Some w, m':=None], Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by auto
    ultimately have False using "1.prems"(2-4) by simp
    thus ?case by simp
  next
    assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
    then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by auto
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
qed

lemma GS'_arg_seq_step_3:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; seq!i = (X, Y); \<not>is_terminal N X Y; findFreeMan X = Some m; w = MPrefs!m!(Y!m); findFiance X w = Some m'; \<not>prefers w WPrefs m m'\<rbrakk> \<Longrightarrow> seq!Suc i = (X, Y[m:=Suc(Y!m)])"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    moreover with "1.prems"(1) have "seq = [(engagements, prop_idxs)]" by auto
    ultimately have False using "1.prems"(2-4) by simp
    thus ?case by simp
  next
    assume non_terminal:"\<not>is_terminal N engagements prop_idxs"
    then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by auto
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
  moreover have "mset (xs::nat list) = mset ys \<Longrightarrow> mset (map Some xs) = mset (map Some ys)" for xs ys by simp
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
        hence "\<forall>m < length engagements. engagements!m \<noteq> Some ?w" by (metis nth_mem findFiance_None)
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
          moreover hence "(X, Y) \<in> set (GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs)" using non_terminal m Some not_init "1.prems"(2) by (auto simp add:Let_def simp del:prefers.simps)
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

lemma distinct:"is_distinct (Gale_Shapley MPrefs WPrefs)"
proof -
  let ?N = "length MPrefs"
  have "Gale_Shapley MPrefs WPrefs = Gale_Shapley' ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0)" by (simp add:Let_def)
  hence "Gale_Shapley MPrefs WPrefs = fst (last (GS'_arg_seq ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0)))" using GS'_arg_seq_computes_GS' by metis
  then obtain Y where "(Gale_Shapley MPrefs WPrefs, Y) \<in> set (GS'_arg_seq ?N MPrefs WPrefs (replicate ?N None) (replicate ?N 0))" using GS'_arg_seq_non_Nil by (metis eq_fst_iff last_in_set)
  moreover have "is_distinct (replicate ?N None)" by simp
  ultimately show ?thesis using GS'_arg_seq_all_distinct by blast
qed

fun married_better::"woman \<Rightarrow> pref_matrix \<Rightarrow> matching \<Rightarrow> matching \<Rightarrow> bool" where
"married_better w WPrefs eng_1 eng_2 = (case findFiance eng_1 w of None \<Rightarrow> True | Some m_1 \<Rightarrow> (
                                          case findFiance eng_2 w of None \<Rightarrow> False | Some m_2 \<Rightarrow> (
                                            if m_1 = m_2 then True
                                                         else prefers w WPrefs m_2 m_1)))"

lemma married_better_refl: "married_better w WPrefs eng eng"
  apply (cases "findFiance eng w")
  by simp_all

lemma married_better_imp:
  assumes "findFiance eng_1 w = Some m_1" and "married_better w WPrefs eng_1 eng_2"
  shows "\<exists>m_2. (findFiance eng_2 w = Some m_2 \<and> (m_1 = m_2 \<or> prefers w WPrefs m_2 m_1))"
proof -
  from assms obtain m_2 where m_2:"findFiance eng_2 w = Some m_2" by fastforce
  have "findFiance eng_2 w = Some m_2 \<and> (m_1 = m_2 \<or> prefers w WPrefs m_2 m_1)"
  proof cases
    assume "m_1 = m_2"
    with m_2 show ?thesis by blast
  next
    assume "m_1 \<noteq> m_2"
    with assms m_2 show ?thesis by fastforce 
  qed
  thus ?thesis by blast
qed

lemma married_better_trans:
  assumes 12:"married_better w WPrefs eng_1 eng_2" and 23:"married_better w WPrefs eng_2 eng_3"
  shows "married_better w WPrefs eng_1 eng_3"
proof (cases "findFiance eng_1 w")
  case None
  thus ?thesis by simp
next
  case (Some m_1)
  then obtain m_2 where m_2:"findFiance eng_2 w = Some m_2" using 12 by force
  then obtain m_3 where m_3:"findFiance eng_3 w = Some m_3" using 23 by force
  with m_2 23 married_better_imp have imp_23:"m_2 = m_3 \<or> prefers w WPrefs m_3 m_2" by fastforce
  from Some m_2 12 married_better_imp have "m_1 = m_2 \<or> prefers w WPrefs m_2 m_1" by fastforce
  thus ?thesis
  proof
    assume "m_1 = m_2"
    with imp_23 show ?thesis using Some m_3 by auto
  next
    assume imp_12:"prefers w WPrefs m_2 m_1"
    from imp_23 show ?thesis
    proof
      assume "m_2 = m_3"
      thus ?thesis using imp_12 Some m_3 by fastforce
    next
      assume "prefers w WPrefs m_3 m_2"
      with imp_12 prefers_trans have "prefers w WPrefs m_3 m_1" by blast
      with Some m_3 show ?thesis by fastforce
    qed
  qed
qed

lemma GS'_arg_seq_all_w_marry_better:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; is_distinct engagements; i < length seq; j < length seq; i < j\<rbrakk> \<Longrightarrow> married_better w WPrefs (fst(seq!i)) (fst(seq!j))"
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
      from GS'_arg_seq_non_Nil GS'_arg_seq_0 have "(engagements[m:=Some ?w], ?next_prop_idxs) \<in> set ?seq_tl" by (metis in_set_conv_nth length_greater_0_conv)
      moreover from None `seq=?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
      ultimately have "(engagements[m:=Some ?w], ?next_prop_idxs) \<in> set seq" by simp
      with "1.prems"(1-2) GS'_arg_seq_all_distinct have distinct:"is_distinct (engagements[m:=Some ?w])" by simp
      from seq_tl have length:"length seq = Suc (length ?seq_tl)" by simp
      moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
      ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
      show ?thesis
      proof (cases i)
        case (Suc i_1)
        with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
        with "1.IH"(1) `j_1 < length ?seq_tl` non_terminal m None distinct have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
        thus ?thesis using seq_tl Suc j_1 by simp
      next
        case 0
        with seq_tl have i:"fst(seq!i) = engagements" by (simp del:GS'_arg_seq.simps)
        have first_second:"married_better w WPrefs engagements (engagements [m:=Some ?w])"
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
        show ?thesis
        proof (cases j_1)
          case 0
          with j_1 i first_second seq_tl show ?thesis by (simp del:GS'_arg_seq.simps)
        next
          case (Suc j_2)
          hence "0 < j_1" by simp
          moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
          ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(1) non_terminal m None distinct `j_1 < length ?seq_tl` by metis
          with seq_tl j_1 have "married_better w WPrefs (engagements[m:=Some ?w]) (fst(seq!j))" by (simp del:GS'_arg_seq.simps)
          with i first_second married_better_trans show ?thesis by metis
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
        from GS'_arg_seq_0 GS'_arg_seq_non_Nil have "(engagements[m:=Some ?w, m':=None], ?next_prop_idxs) \<in> set ?seq_tl" by (metis in_set_conv_nth length_greater_0_conv)
        moreover from Some change `seq=?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        ultimately have "(engagements[m:=Some ?w, m':=None], ?next_prop_idxs) \<in> set seq" by simp
        with GS'_arg_seq_all_distinct "1.prems"(1-2) have distinct:"is_distinct (engagements[m:=Some ?w, m':=None])" by simp
        from seq_tl have length:"length seq = Suc (length ?seq_tl)" by simp
        moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
        ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
          with "1.IH"(2) `j_1 < length ?seq_tl` non_terminal m Some change distinct have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
          thus ?thesis using seq_tl Suc j_1 by simp
        next
          case 0
          with seq_tl have i:"fst(seq!i) = engagements" by (simp del:GS'_arg_seq.simps)
          have first_second:"married_better w WPrefs engagements (engagements[m:=Some ?w, m':=None])"
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
          show ?thesis
          proof (cases j_1)
            case 0
            with j_1 i seq_tl first_second show ?thesis by (simp del:GS'_arg_seq.simps)
          next
            case (Suc j_2)
            hence "0 < j_1" by simp
            moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
            ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(2) non_terminal m Some change distinct `j_1 < length ?seq_tl` by metis
            with seq_tl j_1 have "married_better w WPrefs (engagements[m:=Some ?w, m':=None]) (fst(seq!j))" by (simp del:GS'_arg_seq.simps)
            with i first_second married_better_trans show ?thesis by metis
          qed
        qed
      next
        assume no_change:"\<not> prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from Some no_change have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m `seq=?seq` by (simp add:Let_def)
        hence length:"length seq = Suc (length ?seq_tl)" by simp
        moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
        ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
          with "1.IH"(3) `j_1 < length ?seq_tl` non_terminal m Some no_change "1.prems"(2) have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
          thus ?thesis using seq_tl Suc j_1 by simp
        next
          case 0
          with seq_tl have i:"fst(seq!i) = engagements" by (simp del:GS'_arg_seq.simps)
          show ?thesis
          proof (cases j_1)
            case 0
            with seq_tl j_1 i married_better_refl show ?thesis by (simp del:GS'_arg_seq.simps)
          next
            case (Suc j_2)
            hence "0 < j_1" by simp
            moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
            ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(3) non_terminal m Some no_change "1.prems"(2) `j_1 < length ?seq_tl` by metis
            with seq_tl j_1 i show ?thesis by (simp del:GS'_arg_seq.simps)
          qed
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_prev_prop_idx_same_or_1_less:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "i < length seq" and "0 < i"
      and "k > 0" and "snd(seq!i)!m = k"
    shows "snd(seq!(i-1))!m = k \<or> (snd(seq!(i-1))!m = k - 1 \<and> findFreeMan (fst(seq!(i-1))) = Some m)"
proof -
  from assms(2) have i_1:"i-1 < length seq" by simp
  have seq_i_1:"seq!(i-1) = (fst(seq!(i-1)), snd(seq!(i-1)))" by simp
  show ?thesis
  proof cases
    assume "is_terminal N (fst(seq!(i-1))) (snd(seq!(i-1)))"
    hence "length seq = Suc(i-1)" using GS'_arg_seq_terminal_is_last seq i_1 seq_i_1 by metis
    with assms(2-3) show ?thesis by simp
  next
    assume non_terminal:"\<not> is_terminal N (fst(seq!(i-1))) (snd(seq!(i-1)))"
    then obtain m_prev where m_prev:"findFreeMan (fst(seq!(i-1))) = Some m_prev" by auto
    let ?w = "MPrefs!m_prev!((snd(seq!(i-1)))!m_prev)"
    let ?next_prop_idxs = "(snd(seq!(i-1)))[m_prev:=Suc(snd(seq!(i-1))!m_prev)]"
    have next_prop_idxs:"snd(seq!(i)) = ?next_prop_idxs"
    proof (cases "findFiance (fst(seq!(i-1))) ?w")
      case None
      with GS'_arg_seq_step_1 seq i_1 seq_i_1 non_terminal m_prev have "seq!Suc(i-1) = ((fst(seq!(i-1)))[m_prev:=Some ?w], ?next_prop_idxs)" by metis
      with `0<i` show ?thesis by simp
    next
      case (Some m')
      show ?thesis
      proof cases
        assume "prefers ?w WPrefs m_prev m'"
        with GS'_arg_seq_step_2 seq i_1 seq_i_1 non_terminal m_prev Some have "seq!Suc(i-1) = ((fst(seq!(i-1)))[m_prev:=Some ?w, m':=None], ?next_prop_idxs)" by metis
        with `0<i` show ?thesis by simp
      next
        assume "\<not> prefers ?w WPrefs m_prev m'"
        with GS'_arg_seq_step_3 seq i_1 seq_i_1 non_terminal m_prev Some have "seq!Suc(i-1) = ((fst(seq!(i-1))), ?next_prop_idxs)" by metis
        with `0<i` show ?thesis by simp
      qed
    qed
    show ?thesis
    proof (rule ccontr)
      assume asm:"\<not>(snd(seq!(i-1))!m = k \<or> (snd(seq!(i-1))!m = k - 1 \<and> findFreeMan (fst(seq!(i-1))) = Some m))"
      from assms(5) next_prop_idxs have assms_5:"?next_prop_idxs!m = k" by simp
      show False
      proof cases
        assume "m = m_prev"
        with asm m_prev have "(snd(seq!(i-1)))!m \<noteq> k-1" by blast
        moreover from m_prev findFreeMan_bound non_terminal `m=m_prev` have "m < length (snd(seq!(i-1)))" by metis
        ultimately show False using `m=m_prev` assms_5 by simp
      next
        assume "m \<noteq> m_prev"
        with asm assms_5 show False by auto
      qed
    qed
  qed
qed

lemma GS'_arg_seq_exists_prev_prop_idx:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0)"
      and "i < length seq" and "0 < i" and "k > 0" and "m < N" and "snd(seq!i)!m = k"
    shows "\<exists>j < i. snd(seq!j)!m = k - 1 \<and> findFreeMan (fst(seq!j)) = Some m"
proof (rule ccontr)
  assume asm:"\<not> (\<exists>j < i. snd(seq!j)!m = k - 1 \<and> findFreeMan (fst(seq!j)) = Some m)"
  have "j < i \<Longrightarrow> snd(seq!j)!m = k" for j
  proof (induction "i - j - 1" arbitrary: j)
    case 0
    hence "j = i - 1" by simp
    with `0 < i` have "j < i" by simp
    from assms `j = i - 1` have "snd(seq!j)!m = k \<or> (snd(seq!(j))!m = k - 1 \<and> findFreeMan (fst(seq!(j))) = Some m)"
      by (metis GS'_arg_seq_prev_prop_idx_same_or_1_less)
    with asm `j < i` show ?case by blast
  next
    case (Suc d)
    hence "snd(seq!Suc j)!m = k" by auto
    moreover from Suc have "Suc j < length seq" using `i < length seq` by simp
    moreover have "0 < Suc j" by simp
    ultimately have "snd(seq!(Suc j - 1))!m = k \<or> (snd(seq!(Suc j - 1))!m = k - 1 \<and> findFreeMan (fst(seq!(Suc j - 1))) = Some m)" using GS'_arg_seq_prev_prop_idx_same_or_1_less seq `k > 0` by metis
    moreover have "Suc j - 1 < i" using Suc by simp
    ultimately have "snd(seq!(Suc j - 1))!m = k" using asm by blast
    thus ?case by simp
  qed
  hence "snd(seq!0)!m = k" using `0 < i` by simp
  hence "(replicate N 0)!m = k" using seq by (simp del:GS'_arg_seq.simps)
  thus False using `k > 0` `m < N` by simp
qed

lemma GS'_arg_seq_all_prev_prop_idxs_exist: "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements (replicate N 0); i < length seq; seq!i = (X, prop_idxs); m < N; prop_idxs!m = k; prop_idx < k\<rbrakk> \<Longrightarrow> \<exists>j < i. snd(seq!j)!m = prop_idx \<and> findFreeMan (fst(seq!j)) = Some m"
proof (induction "k - prop_idx - 1" arbitrary: prop_idx)
  case 0
  hence "prop_idx = k - 1" by simp
  moreover from "0.prems"(6) have "k > 0" by simp
  moreover have "0 < i"
  proof (rule ccontr)
    assume "\<not> 0 < i"
    hence "i = 0" by simp
    with "0.prems"(1-3) have "prop_idxs = replicate N 0" by (simp del:GS'_arg_seq.simps)
    with "0.prems"(4-5) `k > 0` show False by simp
  qed
  moreover have "snd(seq!i)!m = k" using "0.prems"(3-5) by simp
  ultimately show ?case using GS'_arg_seq_exists_prev_prop_idx "0.prems"(1-4) by metis
next
  case (Suc d)
  moreover hence "Suc prop_idx < k" by simp
  moreover from Suc.hyps(2) have "d = k - Suc prop_idx - 1" by simp
  ultimately have "\<exists>j < i. findFreeMan (fst(seq!j)) = Some m \<and> snd (seq!j)!m = Suc prop_idx" by metis
  then obtain j where j:"j < i \<and> findFreeMan (fst(seq!j)) = Some m \<and> snd(seq!j)!m = Suc prop_idx" by blast
  with Suc.prems(2) have "j < length seq" by simp
  moreover have "0 < j"
  proof (rule ccontr)
    assume "\<not>0 < j"
    with j Suc.prems(1) `m<N` show False by (simp del:GS'_arg_seq.simps)
  qed
  moreover have "Suc prop_idx > 0" by simp
  moreover have "prop_idx = Suc prop_idx - 1" by simp
  ultimately have "\<exists>j'<j. snd(seq!j')!m = prop_idx \<and> findFreeMan (fst(seq!j')) = Some m" using GS'_arg_seq_exists_prev_prop_idx j Suc.prems(1) `m<N` by metis
  moreover from j have "j < i" by simp
  ultimately show ?case using Suc_lessD less_trans_Suc by blast
qed

lemma GS'_arg_seq_married_once_proposed_to:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
      and "i < length seq - 1"
      and m:"findFreeMan (fst(seq!i)) = Some m" and w:"w = MPrefs!m!(snd(seq!i)!m)"
    shows "findFiance (fst(seq!Suc i)) w \<noteq> None"
proof -
  have seq_i:"seq!i = (fst(seq!i), snd(seq!i))" by simp
  let ?next_prop_idxs = "(snd(seq!i))[m:=Suc(snd(seq!i)!m)]"
  from assms(2) have "i < length seq" by simp
  from findFreeMan_bound m have m_bound:"m < length (fst(seq!i))" by simp
  have non_terminal:"\<not> is_terminal N (fst(seq!i)) (snd(seq!i))"
  proof
    assume "is_terminal N (fst(seq!i)) (snd(seq!i))"
    hence "length seq = Suc i" using seq seq_i `i<length seq` GS'_arg_seq_terminal_is_last by metis
    with assms(2) show False by simp
  qed
  show ?thesis
  proof (cases "findFiance (fst(seq!i)) w")
    case None
    hence seq_Suc_i:"seq!Suc i = ((fst(seq!i))[m:=Some w], ?next_prop_idxs)" using GS'_arg_seq_step_1 seq seq_i `i<length seq` non_terminal m w by metis
    from m_bound have "Some w \<in> set ((fst(seq!i))[m:=Some w])" by (simp add:set_update_memI)
    hence "findFiance ((fst(seq!i))[m:=Some w]) w \<noteq> None" using findFiance_None by blast
    thus ?thesis using seq_Suc_i by simp
  next
    case (Some m')
    with m findFreeMan findFiance have "m \<noteq> m'" by fastforce
    show ?thesis
    proof cases
      assume "prefers w WPrefs m m'"
      hence seq_Suc_i:"seq!Suc i = ((fst(seq!i))[m:=Some w, m':=None], ?next_prop_idxs)" using GS'_arg_seq_step_2 seq seq_i `i<length seq` non_terminal m Some w by metis
      from m_bound `m\<noteq>m'` have "Some w \<in> set ((fst(seq!i))[m:=Some w, m':=None])" by (simp add: list_update_swap set_update_memI)
      hence "findFiance ((fst(seq!i))[m:=Some w, m':=None]) w \<noteq> None" using findFiance_None by blast
      thus ?thesis using seq_Suc_i by simp
    next
      assume "\<not>prefers w WPrefs m m'"
      hence "seq!Suc i = (fst(seq!i), ?next_prop_idxs)" using GS'_arg_seq_step_3 seq seq_i `i<length seq` non_terminal m Some w by metis
      thus ?thesis using Some by simp
    qed
  qed
qed

lemma GS'_arg_seq_any_man_done_proposing_means_done:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs" and "(engagements, prop_idxs) \<in> set seq" and "m < N" and "prop_idxs!m = N"
    shows "None \<notin> set engagements"
proof -
  from assms(3) obtain i where i:"seq!i = (engagements, prop_idxs) \<and> i < length seq" by (metis in_set_conv_nth)
  with GS'_arg_seq_all_prev_prop_idxs_exist assms(4-5) seq have each_increment:"prop_idx < N \<Longrightarrow> \<exists>j < i. findFreeMan (fst(seq!j)) = Some m \<and> snd(seq!j)!m = prop_idx" for prop_idx by metis
  have each_womans_marriage:"prop_idx < N \<Longrightarrow> \<exists>j \<le> i. findFiance (fst(seq!j)) (MPrefs!m!prop_idx) \<noteq> None" for prop_idx
  proof -
    assume "prop_idx < N"
    with each_increment obtain j_1 where j_1:"j_1 < i \<and> findFreeMan(fst(seq!j_1)) = Some m \<and> snd(seq!j_1)!m = prop_idx" by blast
    moreover with i have "j_1 < length seq - 1" by auto
    ultimately have "findFiance (fst(seq!Suc j_1)) (MPrefs!m!prop_idx) \<noteq> None" using GS'_arg_seq_married_once_proposed_to seq by blast
    moreover from j_1 have "Suc j_1 \<le> i" by simp 
    ultimately show ?thesis by blast
  qed
  have w_all_still_married:"prop_idx < N \<Longrightarrow> findFiance engagements (MPrefs!m!prop_idx) \<noteq> None" for prop_idx
  proof -
    assume "prop_idx < N"
    with each_womans_marriage obtain j where j:"j \<le> i \<and> findFiance (fst(seq!j)) (MPrefs!m!prop_idx) \<noteq> None" by blast
    hence "j = i \<or> j < i" by auto
    thus ?thesis
    proof
      assume "j = i"
      thus ?thesis using j i by simp
    next
      assume "j < i"
      moreover with i have "j < length seq" by simp
      moreover have "is_distinct (replicate N None)" by simp
      ultimately have "married_better (MPrefs!m!prop_idx) WPrefs (fst(seq!j)) (fst(seq!i))" using GS'_arg_seq_all_w_marry_better seq i by metis
      hence "married_better (MPrefs!m!prop_idx) WPrefs (fst(seq!j)) engagements" using i by simp
      thus ?thesis using j married_better_imp by blast 
    qed
  qed
  from assms(2) `m<N` have perm:"MPrefs!m <~~> [0 ..< N]" using perm_PPref by metis
  moreover have "length [0 ..< N] = N" by simp
  ultimately have "length (MPrefs!m) = N" by (metis perm_length)
  hence "\<forall>w \<in> set (MPrefs!m). findFiance engagements w \<noteq> None" using w_all_still_married by (metis in_set_conv_nth)
  with perm have "\<forall>w \<in> set [0 ..< N]. findFiance engagements w \<noteq> None" by (metis mset_eq_setD mset_eq_perm)
  with findFiance_Some have "\<forall>w \<in> set [0 ..< N]. Some w \<in> set engagements" by simp
  hence "\<forall>wo \<in> set (map Some [0 ..< N]). wo \<in> set engagements" by simp
  hence subset:"set (map Some [0 ..< N]) \<subseteq> set engagements" by blast
  moreover have card_front:"card (set (map Some [0 ..< N])) = N"
    apply (induction N)
     apply (auto)
    by (metis atLeast0_lessThan_Suc atLeastLessThan_empty_iff card_Suc_eq image_is_empty insert_absorb lessThan_atLeast0 lessThan_eq_iff not_gr_zero these_image_Some_eq these_insert_Some)
  moreover have finite:"finite (set engagements)" by simp
  ultimately have "card (set engagements) \<ge> N" by (metis card_mono)
  moreover have "length engagements = N" using GS'_arg_seq_preserves_length seq assms(3) by (metis length_replicate)
  moreover hence "card (set engagements) \<le> N" using card_length by auto
  ultimately have card_back:"card (set engagements) = N" by simp
  from subset card_front card_back finite have "set (map Some [0 ..< N]) = set engagements" by (metis card_subset_eq)
  moreover have "None \<notin> set (map Some [0 ..< N])" by simp
  ultimately show ?thesis by simp
qed

theorem GS'_arg_seq_never_reaches_NxN:
  assumes seq:"seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
      and "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
      and "(engagements, prop_idxs) \<in> set seq"
    shows "sum_list prop_idxs < N * N"
proof (rule ccontr)
  assume asm:"\<not> sum_list prop_idxs < N * N"
  from assms(4) obtain i where i:"i < length seq \<and> seq!i = (engagements, prop_idxs)" by (metis in_set_conv_nth)
  have l_prop_idxs:"length prop_idxs = N" using GS'_arg_seq_preserves_length seq assms(4) by (metis length_replicate)
  have sum_bound:"\<forall>m < length prop_idxs. prop_idxs!m \<le> N \<Longrightarrow> sum_list prop_idxs \<le> length prop_idxs * N" for prop_idxs N
  proof (induction prop_idxs)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    hence "x \<le> N" by auto
    let ?prop_idxs = "x # xs"
    from Cons.prems have "\<forall>m < length (x # xs) - 1. (x # xs) ! Suc m \<le> N" by (metis diff_Suc_eq_diff_pred zero_less_diff)
    hence "\<forall>m < length xs. xs!m \<le> N" by simp
    with Cons.IH have "sum_list xs \<le> length xs * N" by simp
    moreover have "sum_list ?prop_idxs = x + sum_list xs" by simp
    moreover have "length ?prop_idxs * N = length xs * N + N" by simp
    ultimately show ?case using `x\<le>N` by simp
  qed
  have "\<exists>m < N. prop_idxs!m \<ge> N"
  proof (rule ccontr)
    assume "\<not>(\<exists>m < N. prop_idxs!m \<ge> N)"
    hence "\<forall>m < length prop_idxs. prop_idxs!m \<le> N - 1" using l_prop_idxs by auto
    with sum_bound l_prop_idxs have "sum_list prop_idxs \<le> N * (N - 1)" by metis
    hence "sum_list prop_idxs \<le> N * N - N" by (simp add: diff_mult_distrib2)
    thus False using asm `N\<ge>2` using le_add_diff_inverse2 by fastforce
  qed
  then obtain m k where m_k:"m < N \<and> prop_idxs!m = k \<and> k \<ge> N" by blast
  have less_eq_N:"\<lbrakk>m < N; prop_idxs!m = k; k > N\<rbrakk> \<Longrightarrow> False" for m k
  proof -
    assume "k > N" and 0:"m < N" and 1:"prop_idxs!m = k"
    hence "\<exists>j < i. snd(seq!j)!m = N \<and> findFreeMan (fst(seq!j)) = Some m" using GS'_arg_seq_all_prev_prop_idxs_exist seq i by metis
    then obtain j where j:"j < i \<and> snd(seq!j)!m = N \<and> findFreeMan (fst(seq!j)) = Some m" by blast
    with i have "j < length seq" by simp
    hence "(fst(seq!j), snd(seq!j)) \<in> set seq" by simp
    with GS'_arg_seq_any_man_done_proposing_means_done seq assms(2) 0 1 j have "None \<notin> set (fst(seq!j))" by metis
    moreover from findFreeMan findFreeMan_bound j have "None \<in> set (fst(seq!j))" by (metis in_set_conv_nth)
    ultimately show False by simp
  qed
  from m_k have "k > N \<or> k = N" by auto
  thus False
  proof
    assume "k > N"
    with m_k less_eq_N show False by metis
  next
    assume "k = N"
    hence "None \<notin> set engagements" using m_k GS'_arg_seq_any_man_done_proposing_means_done assms(1-4) by metis
    hence "findFreeMan engagements = None" by (metis findFreeMan_None)
    hence "is_terminal N engagements prop_idxs" by simp
    hence "length seq = Suc i" using GS'_arg_seq_terminal_is_last seq i by metis 

    have "0 < i"
    proof (rule ccontr)
      assume "\<not> 0 < i"
      hence "i = 0" by simp
      with i have "(engagements, prop_idxs) = (replicate N None, replicate N 0)" using seq by (simp del:GS'_arg_seq.simps)
      with m_k have "(replicate N 0)!m = k" by simp
      with `k = N` `N \<ge> 2` m_k show False by simp
    qed

    have if_N_then_prev_is_bump:"\<lbrakk>m' < N; prop_idxs!m' = N\<rbrakk> \<Longrightarrow> findFreeMan (fst(seq!(i-1))) = Some m'" for m'
    proof -
      assume "prop_idxs!m' = N" and "m' < N"
      hence "snd(seq!i)!m' = N" using i by simp
      moreover have "0 < N" using `N \<ge> 2` by simp
      ultimately have "snd(seq!(i-1))!m' = N \<or> snd(seq!(i-1))!m' = N-1 \<and> findFreeMan (fst(seq!(i-1))) = Some m'" using GS'_arg_seq_prev_prop_idx_same_or_1_less i `0 < i` seq by metis
      moreover have "m'<N \<Longrightarrow> \<not>snd(seq!(i-1))!m' = N" for m'
      proof
        assume asm:"snd(seq!(i-1))!m' = N"
        moreover have "i-1 < length seq" using i by auto
        ultimately have "(fst(seq!(i-1)), snd(seq!(i-1)))\<in> set seq" by simp
        moreover assume "m' < N"
        ultimately have "None \<notin> set (fst(seq!(i-1)))" using GS'_arg_seq_any_man_done_proposing_means_done asm assms(1-2) by metis
        hence "findFreeMan (fst(seq!(i-1))) = None" by (metis findFreeMan_None)
        hence "is_terminal N (fst(seq!(i-1))) (snd(seq!(i-1)))" by simp
        moreover have "seq!(i-1) = (fst(seq!(i-1)), snd(seq!(i-1)))" by simp
        ultimately have "length seq = Suc (i-1)" using `i-1<length seq` GS'_arg_seq_terminal_is_last seq by metis
        with `0<i` `length seq = Suc i` show False by simp
      qed
      ultimately show ?thesis using `m'<N` by blast
    qed

    have "\<lbrakk>m' < N; m' \<noteq> m\<rbrakk> \<Longrightarrow> prop_idxs!m' \<noteq> N" for m'
    proof
      assume "m' < N" and "prop_idxs!m' = N"
      hence "findFreeMan (fst(seq!(i-1))) = Some m'" using if_N_then_prev_is_bump by simp
      moreover from m_k `k=N` have "findFreeMan (fst(seq!(i-1))) = Some m" using if_N_then_prev_is_bump by simp
      moreover assume "m'\<noteq>m"
      ultimately show False by simp
    qed
    moreover from less_eq_N have "m' < N \<Longrightarrow> prop_idxs!m' \<le> N" for m' by fastforce
    ultimately have "\<lbrakk>m' < N; m' \<noteq> m\<rbrakk> \<Longrightarrow> prop_idxs!m' < N" for m' by fastforce
    hence "\<forall>m'<N. m'\<noteq>m \<longrightarrow> prop_idxs!m' < N" by blast
    moreover from m_k `k = N` l_prop_idxs have m:"prop_idxs!m = N \<and> m < length prop_idxs" by auto
    moreover from `N\<ge>2` have "N - 1 < N" by simp
    ultimately have "\<forall>m'<N. (prop_idxs[m:=N-1])!m' < N" by (metis nth_list_update)
    moreover have "x < N \<Longrightarrow> x \<le> N-1" for x by fastforce
    ultimately have "\<forall>m'<N. (prop_idxs[m:=N-1])!m' \<le> N - 1" by blast
    moreover from l_prop_idxs have "length (prop_idxs[m:=N-1]) = N" by simp
    ultimately have "sum_list (prop_idxs[m:=N-1]) \<le> N * (N - 1)" using sum_bound by metis
    hence "sum_list (prop_idxs[m:=N-1]) \<le> N * N - N" by (simp add: diff_mult_distrib2)
    moreover from m have "sum_list (prop_idxs[m:=N-1]) = sum_list prop_idxs - 1" using `N\<ge>2` by (simp add: sum_list_update)
    ultimately have "sum_list prop_idxs \<le> N * N - N + 1" by (metis le_diff_conv)
    with asm `N\<ge>2` show False by (metis add_leD2 le_add_diff_inverse2 le_neq_implies_less le_square nat_1_add_1 nat_add_left_cancel_le numeral_le_one_iff semiring_norm(69))
  qed
qed

lemma noFree:
  assumes "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
  shows "\<forall> wo \<in> set (Gale_Shapley MPrefs WPrefs). wo \<noteq> None"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  let ?result = "Gale_Shapley MPrefs WPrefs"
  from assms(1) have "length MPrefs = N" using length_PPrefs by blast
  hence "?result = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by (simp add:Let_def)
  hence result:"?result = fst(last ?seq)" by (metis GS'_arg_seq_computes_GS')

  have is_last:"(fst(last ?seq), snd(last ?seq)) = last ?seq" by simp
  hence terminal:"is_terminal N (fst(last ?seq)) (snd(last ?seq))" using GS'_arg_seq_last_is_terminal by metis

  from is_last have in_set:"(fst(last ?seq), snd(last ?seq)) \<in> set ?seq" using GS'_arg_seq_non_Nil by (metis last_in_set)
  hence length:"length (fst(last ?seq)) = length (snd(last ?seq))" using GS'_arg_seq_preserves_length by (metis length_replicate)

  from GS'_arg_seq_never_reaches_NxN assms in_set have "sum_list (snd(last?seq)) < N * N" by metis
  with terminal length have "findFreeMan (fst(last?seq)) = None" by simp
  with findFreeMan_None result show ?thesis by metis
qed

lemma GS'_arg_seq_all_bounded:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0); is_valid_pref_matrix N MPrefs; i < length seq\<rbrakk> \<Longrightarrow> is_bounded (fst(seq!i))"
proof (induction i)
  case 0
  thus ?case using "0.prems"(1) by (simp del:GS'_arg_seq.simps)
next
  case (Suc i)
  have seq_i: "seq!i = (fst(seq!i), snd(seq!i))" by simp
  moreover have i_bound: "i < length seq" using Suc.prems(3) by simp
  ultimately have in_set:"(fst(seq!i), snd(seq!i)) \<in> set seq" by (metis in_set_conv_nth)
  show ?case
  proof cases
    assume "is_terminal N (fst(seq!i)) (snd(seq!i))"
    hence "length seq = Suc i" using GS'_arg_seq_terminal_is_last Suc.prems(1) seq_i i_bound by metis
    with Suc.prems(3) have False by simp
    thus ?case by simp
  next
    assume non_terminal:"\<not> is_terminal N (fst(seq!i)) (snd(seq!i))"
    then obtain m where m:"findFreeMan (fst(seq!i)) = Some m" by auto
    let ?w = "MPrefs!m!((snd(seq!i))!m)"
    let ?next_prop_idxs = "(snd(seq!i))[m:=Suc((snd(seq!i))!m)]"
    from i_bound Suc.prems(1-2) Suc.IH have IH:"is_bounded (fst(seq!i))" by metis

    from GS'_arg_seq_preserves_length in_set Suc.prems(1) have length:"length (fst(seq!i)) = N \<and> length (snd(seq!i)) = N" by (metis length_replicate)
    with m findFreeMan_bound have "m < N" by metis
    have prop_idx:"(snd(seq!i))!m < N"
    proof (rule ccontr)
      assume "\<not>(snd(seq!i))!m < N"
      hence "(snd(seq!i))!m = N \<or> (snd(seq!i))!m > N" by auto
      thus False
      proof
        assume "(snd(seq!i))!m = N"
        hence "None \<notin> set (fst(seq!i))" using GS'_arg_seq_any_man_done_proposing_means_done Suc.prems(1-2) in_set `m<N` by metis
        hence "findFreeMan (fst(seq!i)) = None" by (metis findFreeMan_None)
        with m show False by simp
      next
        assume "(snd(seq!i))!m > N"
        then obtain k where "(snd(seq!i))!m = k \<and> N < k" by simp
        hence "\<exists>j<i. snd(seq!j)!m = N \<and> findFreeMan (fst(seq!j)) = Some m" using GS'_arg_seq_all_prev_prop_idxs_exist Suc.prems(1) seq_i i_bound `m<N` by metis
        then obtain j where j:"j < i \<and> snd(seq!j)!m = N \<and> findFreeMan (fst(seq!j)) = Some m" by blast
        with i_bound have "j < length seq" by simp
        moreover hence "(fst(seq!j), snd(seq!j)) \<in> set seq" using in_set_conv_nth by simp
        ultimately have "None \<notin> set (fst(seq!j))" using GS'_arg_seq_any_man_done_proposing_means_done Suc.prems(1-2) `m<N` j by metis
        hence "findFreeMan (fst(seq!j)) = None" by (metis findFreeMan_None)
        with j show False by simp
      qed
    qed

    from Suc.prems(2) `m<N` have perm:"MPrefs!m <~~> [0 ..< N]" using perm_PPref by blast
    hence "length (MPrefs!m) = N" by (simp add:perm_length)
    with prop_idx have "?w \<in> set (MPrefs!m)" by simp
    with perm in_perm_upt have "?w < N" by metis

    show ?case
    proof (cases "findFiance (fst(seq!i)) ?w")
      case None
      hence "seq!Suc i = (((fst(seq!i))[m:=Some ?w]), ?next_prop_idxs)" using GS'_arg_seq_step_1 non_terminal m Suc.prems(1) i_bound seq_i by metis
      hence "fst(seq!Suc i) = (fst(seq!i))[m:=Some ?w]" by simp
      with `?w<N` IH length show ?thesis by (metis in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq option.sel)
    next
      case (Some m')
      show ?thesis
      proof cases
        assume "prefers ?w WPrefs m m'"
        hence "seq!Suc i = (((fst(seq!i))[m:=Some ?w, m':=None]), ?next_prop_idxs)" using GS'_arg_seq_step_2 non_terminal m Some Suc.prems(1) i_bound seq_i by metis
        hence seq_Suc_i:"fst(seq!Suc i) = (fst(seq!i))[m:=Some ?w, m':=None]" by simp

        from `?w<N` length have "the (Some ?w) < length ((fst(seq!i))[m:=Some ?w])" by simp
        with IH have "is_bounded ((fst(seq!i))[m:=Some ?w])" by (metis (no_types, lifting) in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq)
        moreover have "is_bounded X \<Longrightarrow> is_bounded (X[m':=None])" for X by (metis in_set_conv_nth length_list_update nth_list_update nth_list_update_neq)
        ultimately have "is_bounded (((fst(seq!i))[m:=Some ?w])[m':=None])" by blast
        with seq_Suc_i show ?thesis by simp
      next
        assume "\<not>prefers ?w WPrefs m m'"
        hence "seq!Suc i = (fst(seq!i), ?next_prop_idxs)" using GS'_arg_seq_step_3 non_terminal m Some Suc.prems(1) i_bound seq_i by metis
        hence "fst(seq!Suc i) = fst(seq!i)" by simp
        with IH show ?thesis by simp
      qed
    qed
  qed
qed

lemma bounded:
  assumes "is_valid_pref_matrix N MPrefs"
  shows "is_bounded (Gale_Shapley MPrefs WPrefs)"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  let ?result = "Gale_Shapley MPrefs WPrefs"
  from assms have "length MPrefs = N" using length_PPrefs by blast
  hence "?result = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by (simp add:Let_def)
  hence result:"?result = fst(last ?seq)" by (metis GS'_arg_seq_computes_GS')

  have "(fst(last ?seq), snd(last ?seq)) = last ?seq" by simp
  hence "(fst(last ?seq), snd(last ?seq)) \<in> set ?seq" using GS'_arg_seq_non_Nil by (metis last_in_set)
  then obtain i where "i < length ?seq \<and> ?seq!i = (fst(last ?seq), snd(last ?seq))" by (metis in_set_conv_nth)
  moreover with GS'_arg_seq_all_bounded assms have "is_bounded (fst(?seq!i))" by metis
  ultimately show ?thesis using result by simp
qed

theorem is_matching:
  assumes "is_valid_pref_matrix N MPrefs" and "N \<ge> 2"
  shows "(Gale_Shapley MPrefs WPrefs) <~~> map Some [0..<N]"
proof -
  let ?seq = "GS'_arg_seq N MPrefs WPrefs (replicate N None) (replicate N 0)"
  let ?result = "Gale_Shapley MPrefs WPrefs"
  from assms have "length MPrefs = N" using length_PPrefs by blast
  hence "?result = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by (simp add:Let_def)
  hence result:"?result = fst(last ?seq)" by (metis GS'_arg_seq_computes_GS')

  have "(fst(last ?seq), snd(last ?seq)) = last ?seq" by simp
  hence "(fst(last ?seq), snd(last ?seq)) \<in> set ?seq" using GS'_arg_seq_non_Nil by (metis last_in_set)
  with GS'_arg_seq_preserves_length have "length (fst(last ?seq)) = N" by (metis length_replicate)
  with result have "length ?result = N" by simp
  with is_matching_intro assms noFree distinct bounded show ?thesis by metis
qed
end
