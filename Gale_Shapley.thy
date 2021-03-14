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

lemma in_perm_upt: "x < k \<longleftrightarrow> (\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A)"
proof
  assume "x < k"
  show "\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A"
  proof
    from in_upt `x<k` perm_refl show "[0 ..< k] <~~> [0 ..< k] \<and> x \<in> set [0 ..< k]" by metis
  qed
next
  assume "\<exists>A. A <~~> [0 ..< k] \<and> x \<in> set A"
  then obtain A where A:"A <~~> [0 ..< k] \<and> x \<in> set A" by blast
  with perm_set_eq in_upt show "x < k" by metis
qed

fun is_perm::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_perm A B = (mset A = mset B)"
lemma is_perm:"is_perm A B \<Longrightarrow> A <~~> B" by (metis is_perm.simps mset_eq_perm)

fun is_valid_pref_matrix::"nat \<Rightarrow> pref_matrix \<Rightarrow> bool" where
"is_valid_pref_matrix N PPrefs = (if length PPrefs \<noteq> N then False else Ball (set PPrefs) (\<lambda>PPref. is_perm PPref [0 ..< N]))"

fun findFreeMan::"matching \<Rightarrow> man option" where
"findFreeMan engagements = find_idx (\<lambda>wo. wo = None) engagements"
lemma findFreeMan_bound:"findFreeMan engagements = Some m \<Longrightarrow> m < length engagements" by (auto intro:find_idx_bound)
lemma findFreeMan_None:"findFreeMan engagements = None \<longleftrightarrow> (\<forall>wo\<in>set engagements. wo \<noteq> None)"
proof
  let ?F = "\<lambda>wo. wo = None"
  from find_idx_None have "find_idx pred xs = None \<Longrightarrow> (\<forall>x\<in>set xs. \<not>pred x)" for pred xs by metis
  hence "find_idx ?F engagements = None \<Longrightarrow> (\<forall>x \<in>set engagements. \<not>?F x)" by blast
  thus "findFreeMan engagements = None \<Longrightarrow> (\<forall>wo\<in>set engagements. wo \<noteq> None)" by (metis findFreeMan.simps)
next
  let ?F = "\<lambda>wo. wo = None"
  from find_idx_None have 0:"(\<forall>x\<in>set xs. \<not>pred x) \<Longrightarrow> find_idx pred xs = None" for pred xs by metis
  have "(\<forall>x\<in>set engagements. \<not>?F x) \<Longrightarrow> find_idx ?F engagements = None" by (simp add:0)
  thus "(\<forall>wo\<in>set engagements. wo \<noteq> None) \<Longrightarrow> findFreeMan engagements = None" by simp
qed
lemma findFreeMan:"findFreeMan engagements = Some m \<Longrightarrow> engagements!m = None"
proof -
  from find_idx_Some find_idx have "\<exists>idx. find_idx pred xs = Some idx \<Longrightarrow> pred (xs ! the (find_idx pred xs))" for pred xs by metis
  thus "findFreeMan engagements = Some m \<Longrightarrow> engagements!m = None" using findFreeMan.elims by fastforce
qed

fun findFiance::"matching \<Rightarrow> woman \<Rightarrow> man option" where
"findFiance engagements w = find_idx (\<lambda>wo. wo = Some w) engagements"
lemma findFiance_bound:"findFiance engagements w = Some m' \<Longrightarrow> m' < length engagements" by (auto intro:find_idx_bound)
lemma findFiance_Some:"findFiance engagements w \<noteq> None \<Longrightarrow> Some w \<in> set engagements"
proof -
  assume "findFiance engagements w \<noteq> None"
  hence "\<exists>idx. findFiance engagements w = Some idx" by auto
  moreover from find_idx_Some have "\<exists>idx. find_idx pred xs = Some idx \<Longrightarrow> \<exists>x \<in> set xs. pred x" for pred xs by metis
  ultimately have "\<exists>wo \<in> set engagements. wo = Some w" by auto
  thus ?thesis by simp
qed
lemma findFiance_None:"findFiance engagements w = None \<Longrightarrow> \<forall>wo\<in>set engagements. wo \<noteq> Some w"
proof -
  have "find_idx pred xs = None \<Longrightarrow> \<forall>x\<in>set xs. \<not>pred x" for pred xs using find_idx_None by metis
  thus "findFiance engagements w = None \<Longrightarrow> \<forall>wo\<in>set engagements. wo\<noteq>Some w" by auto
qed
lemma findFiance_Some_is_first:
  assumes 0:"findFiance engagements w = Some m" and 1:"m' < m"
    shows "engagements!m' \<noteq> Some w"
proof -
  let ?F = "\<lambda>wo. wo = Some w"
  from 0 have "find_idx ?F engagements = Some m" by simp
  with 1 find_idx_Some_is_first show ?thesis by auto
qed
lemma findFiance_first_is_Some:
  assumes 0:"m < length engagements" and 1:"\<forall>m'<m. engagements!m'\<noteq>Some w"
      and 2:"engagements!m = Some w"
    shows "findFiance engagements w = Some m"
proof -
  let ?F = "\<lambda>wo. wo = Some w"
  from 1 have "\<forall>m'<m. \<not> ?F (engagements!m')" by simp
  moreover from 2 have "?F (engagements!m)" by simp
  ultimately have "find_idx ?F engagements = Some m" using 0 by (simp add: find_idx_first_is_Some)
  thus ?thesis by simp
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
                                   Some idx_2 \<Rightarrow> idx_1 < idx_2))"

lemma prefers_trans:
  assumes 0:"prefers p PPrefs p1 p2" and 1:"prefers p PPrefs p2 p3"
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
    hence "idx_1 < idx_2" using 0 idx_1 by simp
    show ?thesis
    proof (cases "findPerson (PPrefs!p) p3")
      case None
      hence False using 1 idx_2 by simp
      thus ?thesis by simp
    next
      case (Some idx_3)
      hence "idx_2 < idx_3" using 1 idx_2 by simp
      with `idx_1 < idx_2` have "idx_1 < idx_3" by simp
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
      thus ?thesis using non_terminal m Some asm by (simp add:Let_def del:prefers.simps)
    next
      assume "\<not> prefers ?w WPrefs m m'"
      thus ?thesis using non_terminal m Some asm by (simp add:Let_def del:prefers.simps)
    qed
  qed
qed

lemma GS'_arg_seq_first_is_start_idx:"(GS'_arg_seq N MPrefs WPrefs engagements prop_idxs)!0 = (engagements, prop_idxs)" using GS'_arg_seq_first_is_start GS'_arg_seq_non_Nil by (metis list.exhaust nth_Cons_0 surj_pair)

lemma GS'_arg_seq_snd_snd_is_next_prop_idx:
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
    hence "seq!1 = ?seq_tl!0" by simp
    thus ?thesis using GS'_arg_seq_first_is_start_idx by (metis snd_conv)
  next
    case (Some m')
    show ?thesis
    proof cases
      assume change:"prefers ?w WPrefs m m'"
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m:=Some ?w, m':=None]) ?next_prop_idxs"
      from non_terminal m Some change seq have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      hence "seq!1 = ?seq_tl!0" by simp
      thus ?thesis using GS'_arg_seq_first_is_start_idx by (metis snd_conv)
    next
      assume no_change:"\<not> prefers ?w WPrefs m m'"
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
      from non_terminal m Some no_change seq have "seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      hence "seq!1 = ?seq_tl!0" by simp
      thus ?thesis using GS'_arg_seq_first_is_start_idx by (metis snd_conv)
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
    with "1.prems"(1-3) GS'_arg_seq_first_is_start_idx have "(X, Y) = (engagements, prop_idxs)" by metis
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
      with "1.prems"(1-3) GS'_arg_seq_first_is_start_idx have "(X, Y) = (engagements, prop_idxs)" by metis
      with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w]) (Y[m:=Suc(Y!m)])" by (simp add:Let_def)
      with 0 have "seq!Suc i = (GS'_arg_seq N MPrefs WPrefs (X[m:=Some w]) (Y[m:=Suc(Y!m)]))!0" by simp
      thus ?thesis using GS'_arg_seq_first_is_start_idx by metis
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
      with "1.prems"(1-3) GS'_arg_seq_first_is_start_idx have "(X, Y) = (engagements, prop_idxs)" by metis
      with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs (X[m:=Some w, m':=None]) (Y[m:=Suc(Y!m)])" by (auto simp add:Let_def)
      with 0 have "seq!Suc i = (GS'_arg_seq N MPrefs WPrefs (X[m:=Some w, m':=None]) (Y[m:=Suc(Y!m)]))!0" by simp
      thus ?thesis using GS'_arg_seq_first_is_start_idx by metis
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
      with "1.prems"(1-3) GS'_arg_seq_first_is_start_idx have "(X, Y) = (engagements, prop_idxs)" by metis
      with "1.prems" have "seq = (X, Y) # GS'_arg_seq N MPrefs WPrefs X (Y[m:=Suc(Y!m)])" by (auto simp add:Let_def)
      with 0 have "seq!Suc i = (GS'_arg_seq N MPrefs WPrefs X (Y[m:=Suc(Y!m)]))!0" by simp
      thus ?thesis using GS'_arg_seq_first_is_start_idx by metis
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
"married_better w WPrefs eng_1 eng_2 = (if findFiance eng_1 w = None then 
                                          True
                                        else (
                                          let m_1 = the (findFiance eng_1 w) in (
                                          if findFiance eng_2 w = None then
                                            False
                                          else (
                                            let m_2 = the (findFiance eng_2 w) in (
                                            if m_1 = m_2 then
                                              True
                                            else
                                              prefers w WPrefs m_2 m_1)))))"

lemma married_better_refl: "married_better w WPrefs eng eng" by simp

lemma married_better_trans:
  assumes 0:"married_better w WPrefs eng_1 eng_2" and 1:"married_better w WPrefs eng_2 eng_3"
    shows "married_better w WPrefs eng_1 eng_3"
proof -
  let ?m_1 = "the (findFiance eng_1 w)"
  let ?m_2 = "the (findFiance eng_2 w)"
  let ?m_3 = "the (findFiance eng_3 w)"
  from 0 have "findFiance eng_1 w = None \<or> (findFiance eng_1 w \<noteq> None \<and> findFiance eng_2 w \<noteq> None \<and> (?m_1 = ?m_2 \<or> prefers w WPrefs ?m_2 ?m_1))" by (metis married_better.simps)
  thus ?thesis
  proof
    assume "findFiance eng_1 w = None"
    thus ?thesis by (metis married_better.simps)
  next
    assume asm:"findFiance eng_1 w \<noteq> None \<and> findFiance eng_2 w \<noteq> None \<and> (?m_1 = ?m_2 \<or> prefers w WPrefs ?m_2 ?m_1)"
    hence married_2:"findFiance eng_2 w \<noteq> None" by simp
    with 1 have married_3:"findFiance eng_3 w \<noteq> None" by (metis married_better.simps)
    from married_2 1 have "(?m_2 = ?m_3 \<or> prefers w WPrefs ?m_3 ?m_2)" by (metis married_better.simps)
    moreover from asm have "?m_1 = ?m_2 \<or> prefers w WPrefs ?m_2 ?m_1" by simp
    ultimately have "?m_1 = ?m_3 \<or> prefers w WPrefs ?m_3 ?m_1" using prefers_trans by metis
    thus ?thesis using married_3 by (metis married_better.simps)
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
      from GS'_arg_seq_non_Nil obtain X Y xys where "(X, Y) # xys = ?seq_tl" by (metis neq_Nil_conv surj_pair)
      with GS'_arg_seq_first_is_start have "(engagements[m:=Some ?w], ?next_prop_idxs) \<in> set ?seq_tl" by (metis list.set_intros(1))
      moreover from None have seq_tl:"?seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
      ultimately have "(engagements[m:=Some ?w], ?next_prop_idxs) \<in> set ?seq" by simp
      with "1.prems"(2) GS'_arg_seq_all_distinct have distinct:"is_distinct (engagements[m:=Some ?w])" by simp
      from seq_tl have length:"length seq = Suc (length ?seq_tl)" using `seq = ?seq` by simp
      moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
      ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
      show ?thesis
      proof (cases i)
        case (Suc i_1)
        with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
        with "1.IH"(1) `j_1 < length ?seq_tl` non_terminal m None distinct have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
        thus ?thesis using seq_tl Suc j_1 `seq = ?seq` by simp
      next
        case 0
        with `seq = ?seq` have i:"fst(seq!i) = engagements" using GS'_arg_seq_first_is_start_idx by auto
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
          hence "j = 1" using j_1 by simp
          with seq_tl `seq = ?seq` have "seq!j = ?seq_tl!0" by simp
          with GS'_arg_seq_first_is_start_idx have "fst(seq!j) = engagements[m:=Some ?w]" by (metis fst_conv)
          with first_second i show ?thesis by simp
        next
          case (Suc j_2)
          hence "0 < j_1" by simp
          moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
          ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(1) non_terminal m None distinct `j_1 < length ?seq_tl` by metis
          with GS'_arg_seq_first_is_start_idx have "married_better w WPrefs (engagements[m:=Some ?w]) (fst(?seq_tl!j_1))" by (metis fst_conv)
          with seq_tl `seq = ?seq` j_1 have "married_better w WPrefs (engagements[m:=Some ?w]) (fst(seq!j))" by simp
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
        from GS'_arg_seq_non_Nil obtain X Y xys where "(X, Y) # xys = ?seq_tl" by (metis neq_Nil_conv surj_pair)
        with GS'_arg_seq_first_is_start have "(engagements[m:=Some ?w, m':=None], ?next_prop_idxs) \<in> set ?seq_tl" by (metis list.set_intros(1))
        moreover from Some change have seq_tl:"?seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        ultimately have "(engagements[m:=Some ?w, m':=None], ?next_prop_idxs) \<in> set ?seq" by simp
        with GS'_arg_seq_all_distinct "1.prems"(2) have distinct:"is_distinct (engagements[m:=Some ?w, m':=None])" by simp
        from seq_tl have length:"length seq = Suc (length ?seq_tl)" using `seq = ?seq` by simp
        moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
        ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
          with "1.IH"(2) `j_1 < length ?seq_tl` non_terminal m Some change distinct have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
          thus ?thesis using seq_tl Suc j_1 `seq = ?seq` by simp
        next
          case 0
          with `seq = ?seq` have i:"fst(seq!i) = engagements" using GS'_arg_seq_first_is_start_idx by auto
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
            hence "j = 1" using j_1 by simp
            with seq_tl `seq = ?seq` have "seq!j = ?seq_tl!0" by simp
            with GS'_arg_seq_first_is_start_idx have "fst(seq!j) = (engagements[m:=Some ?w, m':=None])" by (metis fst_conv)
            with first_second i show ?thesis by simp
          next
            case (Suc j_2)
            hence "0 < j_1" by simp
            moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
            ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(2) non_terminal m Some change distinct `j_1 < length ?seq_tl` by metis
            with GS'_arg_seq_first_is_start_idx have "married_better w WPrefs (engagements[m:=Some ?w, m':=None]) (fst(?seq_tl!j_1))" by (metis fst_conv)
            with seq_tl `seq = ?seq` j_1 have "married_better w WPrefs (engagements[m:=Some ?w, m':=None]) (fst(seq!j))" by simp
            with i first_second married_better_trans show ?thesis by metis
          qed
        qed
      next
        assume no_change:"\<not> prefers ?w WPrefs m m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from Some no_change have seq_tl:"?seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m by (simp add:Let_def)
        hence length:"length seq = Suc (length ?seq_tl)" using `seq = ?seq` by simp
        moreover from "1.prems"(5) obtain j_1 where j_1:"j = Suc j_1" by (metis Nat.lessE)
        ultimately have "j_1 < length ?seq_tl" using "1.prems"(4) by simp
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with length j_1 "1.prems"(3-5) have "i_1 < length ?seq_tl" and "i_1 < j_1" by auto
          with "1.IH"(3) `j_1 < length ?seq_tl` non_terminal m Some no_change "1.prems"(2) have "married_better w WPrefs (fst(?seq_tl!i_1)) (fst(?seq_tl!j_1))" by metis
          thus ?thesis using seq_tl Suc j_1 `seq = ?seq` by simp
        next
          case 0
          with `seq = ?seq` have i:"fst(seq!i) = engagements" using GS'_arg_seq_first_is_start_idx by auto
          show ?thesis
          proof (cases j_1)
            case 0
            hence "j = 1" using j_1 by simp
            with seq_tl `seq = ?seq` have "seq!j = ?seq_tl!0" by simp
            with GS'_arg_seq_first_is_start_idx have "fst(seq!j) = engagements" by (metis fst_conv)
            with married_better_refl i show ?thesis by simp
          next
            case (Suc j_2)
            hence "0 < j_1" by simp
            moreover have "0 < length ?seq_tl" using GS'_arg_seq_non_Nil by blast
            ultimately have "married_better w WPrefs (fst(?seq_tl!0)) (fst(?seq_tl!j_1))" using "1.IH"(3) non_terminal m Some no_change "1.prems"(2) `j_1 < length ?seq_tl` by metis
            with GS'_arg_seq_first_is_start_idx have "married_better w WPrefs engagements (fst(?seq_tl!j_1))" by (metis fst_conv)
            with seq_tl `seq = ?seq` j_1 i show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma GS'_arg_seq_prev_prop_idx_same_or_1_less:"\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq; 0 < i; k > 0; snd(seq!i)!m = k\<rbrakk> \<Longrightarrow> snd(seq!(i-1))!m = k \<or> (snd(seq!(i-1))!m = k - 1 \<and> findFreeMan (fst(seq!(i-1))) = Some m)"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show ?case
  proof (cases)
    assume "is_terminal N engagements prop_idxs"
    hence "seq = [(engagements, prop_idxs)]" using `seq = ?seq` by auto
    hence "length seq = 1" by simp
    with "1.prems"(2-3) show ?case by simp
  next
    assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
    then obtain m_free where m_free:"findFreeMan engagements = Some m_free" by auto
    let ?w = "MPrefs!m_free!(prop_idxs!m_free)"
    let ?next_prop_idxs = "prop_idxs[m_free:=Suc(prop_idxs!m_free)]"
    from `0 < i` obtain i_1 where i_1:"i = Suc i_1" by (metis Nat.lessE)
    show ?case
    proof (cases i_1)
      case 0
      with i_1 have "i = 1" by simp
      hence seq_i_1:"seq!(i-1) = (engagements, prop_idxs)" using `seq = ?seq` GS'_arg_seq_first_is_start_idx by simp
      from `i = 1` have seq_i:"snd(seq!i) = ?next_prop_idxs" using `seq = ?seq` GS'_arg_seq_snd_snd_is_next_prop_idx non_terminal m_free by metis
      show ?thesis
      proof (rule ccontr)
        assume asm:"\<not> (snd(seq!(i-1))!m = k \<or> (snd(seq!(i-1))!m = k - 1 \<and> findFreeMan (fst(seq!(i-1))) = Some m))"
        hence "snd(seq!(i-1))!m \<noteq> k" by simp
        with seq_i_1 have "prop_idxs!m \<noteq> k" by simp
        from seq_i "1.prems"(5) have "?next_prop_idxs!m = k" by simp
        show False
        proof cases
          assume "m_free = m"
          from asm seq_i_1 have "prop_idxs!m \<noteq> k - 1 \<or> findFreeMan engagements \<noteq> Some m" by simp
          with m_free `m_free = m` have "prop_idxs!m \<noteq> k - 1" by simp
          moreover from findFreeMan_bound m_free non_terminal `m_free = m` have "m < length prop_idxs" by metis
          ultimately show False using `m_free = m` `?next_prop_idxs!m = k` by simp
        next
          assume "m_free \<noteq> m"
          with `prop_idxs!m \<noteq> k` `?next_prop_idxs!m = k` show False by auto
        qed
      qed
    next
      case (Suc i_2)
      show ?thesis
      proof (cases "findFiance engagements ?w")
        case None
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_free:=Some ?w]) ?next_prop_idxs"
        from None `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m_free by (simp add:Let_def)
        from Suc have "0 < i_1" by simp
        moreover from seq_tl i_1 `i < length seq` have "i_1 < length ?seq_tl" by simp
        moreover from seq_tl i_1 "1.prems"(5) have "snd(?seq_tl!i_1)!m = k" by simp
        ultimately have "snd(?seq_tl!(i_1-1))!m = k \<or> (snd(?seq_tl!(i_1-1))!m = k - 1 \<and> findFreeMan (fst(?seq_tl!(i_1-1))) = Some m)" using "1.IH"(1) `k > 0` non_terminal m_free None by metis
        thus ?thesis using seq_tl i_1 `0 < i_1` by simp
      next
        case (Some m')
        show ?thesis
        proof cases
          assume change:"prefers ?w WPrefs m_free m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_free:=Some ?w, m':=None]) ?next_prop_idxs"
          from Some change `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m_free by (simp add:Let_def)
          from Suc have "0 < i_1" by simp
          moreover from seq_tl i_1 `i < length seq` have "i_1 < length ?seq_tl" by simp
          moreover from seq_tl i_1 "1.prems"(5) have "snd(?seq_tl!i_1)!m = k" by simp
          ultimately have "snd(?seq_tl!(i_1-1))!m = k \<or> (snd(?seq_tl!(i_1-1))!m = k - 1 \<and> findFreeMan (fst(?seq_tl!(i_1-1))) = Some m)" using "1.IH"(2) `k > 0` non_terminal m_free Some change by metis
          thus ?thesis using seq_tl i_1 `0 < i_1` by simp
        next
          assume no_change:"\<not> prefers ?w WPrefs m_free m'"
          let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
          from Some no_change `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" using non_terminal m_free by (simp add:Let_def)
          from Suc have "0 < i_1" by simp
          moreover from seq_tl i_1 `i < length seq` have "i_1 < length ?seq_tl" by simp
          moreover from seq_tl i_1 "1.prems"(5) have "snd(?seq_tl!i_1)!m = k" by simp
          ultimately have "snd(?seq_tl!(i_1-1))!m = k \<or> (snd(?seq_tl!(i_1-1))!m = k - 1 \<and> findFreeMan (fst(?seq_tl!(i_1-1))) = Some m)" using "1.IH"(3) `k > 0` non_terminal m_free Some no_change by metis
          thus ?thesis using seq_tl i_1 `0 < i_1` by simp
        qed
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
  moreover have "snd(seq!0) = replicate N 0" using seq GS'_arg_seq_first_is_start_idx snd_conv by metis
  ultimately have "(replicate N 0)!m = k" by simp
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
    with "0.prems"(1-3) have "prop_idxs = replicate N 0" using GS'_arg_seq_first_is_start_idx by (metis prod.inject)
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
    hence "j = 0" by simp
    with j Suc.prems(1) have "snd(seq!j) = replicate N 0" using GS'_arg_seq_first_is_start_idx by (metis snd_conv)
    with j `m < N` show False by simp
  qed
  moreover have "Suc prop_idx > 0" by simp
  moreover have "prop_idx = Suc prop_idx - 1" by simp
  ultimately have "\<exists>j'<j. snd(seq!j')!m = prop_idx \<and> findFreeMan (fst(seq!j')) = Some m" using GS'_arg_seq_exists_prev_prop_idx j Suc.prems(1) `m<N` by metis
  moreover from j have "j < i" by simp
  ultimately show ?case using Suc_lessD less_trans_Suc by blast
qed

lemma GS'_arg_seq_married_once_proposed_to: "\<lbrakk>seq = GS'_arg_seq N MPrefs WPrefs engagements prop_idxs; i < length seq - 1; findFreeMan (fst(seq!i)) = Some m; w = MPrefs!m!(snd(seq!i)!m)\<rbrakk> \<Longrightarrow> findFiance (fst(seq!Suc i)) w \<noteq> None"
proof (induction N MPrefs WPrefs engagements prop_idxs arbitrary:seq i rule:GS'_arg_seq.induct)
  case (1 N MPrefs WPrefs engagements prop_idxs)
  let ?seq = "GS'_arg_seq N MPrefs WPrefs engagements prop_idxs"
  show ?case
  proof cases
    assume "is_terminal N engagements prop_idxs"
    hence "seq = [(engagements, prop_idxs)]" using `seq = ?seq` by auto
    with "1.prems"(2) have False by simp
    thus ?case by simp
  next
    assume non_terminal:"\<not> is_terminal N engagements prop_idxs"
    then obtain m_0 where m_0:"findFreeMan engagements = Some m_0" by auto
    let ?w = "MPrefs!m_0!(prop_idxs!m_0)"
    let ?next_prop_idxs = "prop_idxs[m_0:=Suc(prop_idxs!m_0)]"
    show ?case
    proof (cases "findFiance engagements ?w")
      case None
      let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w]) ?next_prop_idxs"
      from non_terminal m_0 None `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
      show ?thesis
      proof (cases i)
        case (Suc i_1)
        with "1.prems"(2) seq_tl have "i_1 < length ?seq_tl - 1" by simp
        moreover with "1.prems"(3) seq_tl Suc have "findFreeMan (fst(?seq_tl!i_1)) = Some m" by simp
        moreover with "1.prems"(4) seq_tl Suc have "w = MPrefs!m!(snd(?seq_tl!i_1)!m)" by simp
        ultimately have "findFiance (fst(?seq_tl!Suc i_1)) w \<noteq> None" using "1.IH"(1) non_terminal m_0 None by metis
        thus ?thesis using seq_tl Suc by simp
      next
        case 0
        hence "seq!i = (engagements, prop_idxs)" using GS'_arg_seq_first_is_start_idx seq_tl by simp
        with "1.prems"(3-4) m_0 have "m = m_0" and "w = ?w" by auto
        have "fst(seq!Suc i) = fst(?seq_tl!0)" using 0 seq_tl by simp
        with GS'_arg_seq_first_is_start_idx have "fst(seq!Suc i) = engagements[m_0:=Some ?w]" by (metis fst_conv)
        hence seq_Suc_i:"fst(seq!Suc i) = engagements[m:=Some w]" using `m=m_0` `w=?w` by simp
        from findFreeMan_bound m_0 `m = m_0` have "m < length engagements" by simp
        hence "Some w \<in> set (engagements[m:=Some w])" by (simp add: set_update_memI)
        hence "findFiance (engagements[m:=Some w]) w \<noteq> None" using findFiance_None by blast
        thus ?thesis using seq_Suc_i by simp
      qed
    next
      case (Some m')
      show ?thesis
      proof cases
        assume change:"prefers ?w WPrefs m_0 m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs (engagements[m_0:=Some ?w, m':=None]) ?next_prop_idxs"
        from non_terminal m_0 Some change `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with "1.prems"(2) seq_tl have "i_1 < length ?seq_tl - 1" by simp
          moreover with "1.prems"(3) seq_tl Suc have "findFreeMan (fst(?seq_tl!i_1)) = Some m" by simp
          moreover with "1.prems"(4) seq_tl Suc have "w = MPrefs!m!(snd(?seq_tl!i_1)!m)" by simp
          ultimately have "findFiance (fst(?seq_tl!Suc i_1)) w \<noteq> None" using "1.IH"(2) non_terminal m_0 Some change by metis
          thus ?thesis using seq_tl Suc by simp
        next
          case 0
          hence "seq!i = (engagements, prop_idxs)" using GS'_arg_seq_first_is_start_idx seq_tl by simp
          with "1.prems"(3-4) m_0 have "m = m_0" and "w = ?w" by auto
          from findFiance Some have "engagements!m' = Some ?w" by simp
          moreover have "engagements!m_0 = None" using findFreeMan m_0 by simp
          ultimately have "m \<noteq> m'" using `m = m_0` by auto
          have "fst(seq!Suc i) = fst(?seq_tl!0)" using 0 seq_tl by simp
          with GS'_arg_seq_first_is_start_idx have "fst(seq!Suc i) = engagements[m_0:=Some ?w, m':=None]" by (metis fst_conv)
          hence seq_Suc_i:"fst(seq!Suc i) = engagements[m:=Some w, m':=None]" using `m=m_0` `w=?w` by simp
          from findFreeMan_bound m_0 `m = m_0` have "m < length engagements" by simp
          hence "Some w \<in> set(engagements[m:=Some w, m':=None])" using `m\<noteq>m'` by (simp add: list_update_swap set_update_memI)
          hence "findFiance (engagements[m:=Some w, m':=None]) w \<noteq> None" using findFiance_None by blast
          thus ?thesis using seq_Suc_i by simp
        qed
      next
        assume no_change:"\<not> prefers ?w WPrefs m_0 m'"
        let ?seq_tl = "GS'_arg_seq N MPrefs WPrefs engagements ?next_prop_idxs"
        from non_terminal m_0 Some no_change `seq = ?seq` have seq_tl:"seq = (engagements, prop_idxs) # ?seq_tl" by (simp add:Let_def)
        show ?thesis
        proof (cases i)
          case (Suc i_1)
          with "1.prems"(2) seq_tl have "i_1 < length ?seq_tl - 1" by simp
          moreover with "1.prems"(3) seq_tl Suc have "findFreeMan (fst(?seq_tl!i_1)) = Some m" by simp
          moreover with "1.prems"(4) seq_tl Suc have "w = MPrefs!m!(snd(?seq_tl!i_1)!m)" by simp
          ultimately have "findFiance (fst(?seq_tl!Suc i_1)) w \<noteq> None" using "1.IH"(3) non_terminal m_0 Some no_change by metis
          thus ?thesis using seq_tl Suc by simp
        next
          case 0
          hence "seq!i = (engagements, prop_idxs)" using GS'_arg_seq_first_is_start_idx seq_tl by simp
          with "1.prems"(3-4) m_0 have "w = ?w" by auto
          have "fst(seq!Suc i) = fst(?seq_tl!0)" using 0 seq_tl by simp
          with GS'_arg_seq_first_is_start_idx have "fst(seq!Suc i) = engagements" by (metis fst_conv)
          thus ?thesis using `w=?w` Some by simp
        qed
      qed
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
      thus ?thesis using j by (metis married_better.simps)
    qed
  qed
  from assms(2) have "length MPrefs = N" by (metis is_valid_pref_matrix.simps)
  with `m < N` have "m < length MPrefs" by simp
  with assms(2) have perm:"(MPrefs!m) <~~> [0 ..< N]" by (metis is_valid_pref_matrix.simps nth_mem is_perm)
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
      with i GS'_arg_seq_first_is_start_idx have "(engagements, prop_idxs) = (replicate N None, replicate N 0)" using seq by metis
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
  from assms have "length MPrefs = N" by (metis is_valid_pref_matrix.simps)
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
  have "fst(seq!0) = (replicate N None)" using "0.prems"(1) by (metis GS'_arg_seq_first_is_start_idx fst_conv)
  thus ?case by simp
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

    from Suc.prems(2) have "length MPrefs = N" by (metis is_valid_pref_matrix.simps)
    moreover from Suc.prems(2) have "\<forall>MPref \<in> set MPrefs. is_perm MPref [0 ..< N]" by (metis is_valid_pref_matrix.simps)
    ultimately have "is_perm (MPrefs!m) [0 ..< N]" using `m < N` by simp
    hence perm:"MPrefs!m <~~> [0 ..< N]" by (metis is_perm)
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
  from assms have "length MPrefs = N" by (metis is_valid_pref_matrix.simps)
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
  from assms have "length MPrefs = N" by (metis is_valid_pref_matrix.simps)
  hence "?result = Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0)" by (simp add:Let_def)
  hence result:"?result = fst(last ?seq)" by (metis GS'_arg_seq_computes_GS')

  have "(fst(last ?seq), snd(last ?seq)) = last ?seq" by simp
  hence "(fst(last ?seq), snd(last ?seq)) \<in> set ?seq" using GS'_arg_seq_non_Nil by (metis last_in_set)
  with GS'_arg_seq_preserves_length have "length (fst(last ?seq)) = N" by (metis length_replicate)
  with result have "length ?result = N" by simp
  with is_matching_intro assms noFree distinct bounded show ?thesis by metis
qed
end
