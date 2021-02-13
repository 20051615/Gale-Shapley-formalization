theory Gale_Shapley
  imports Main find_idx
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

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

lemma prop_idxs_prog:"m < length xs \<Longrightarrow> sum_list (xs[m:=Suc (xs!m)]) = Suc (sum_list xs)"
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
    moreover from m_1 Cons.prems Suc have "(x # xs)[m:=Suc ((x # xs)!m)] = x # xs[m_1:=Suc (xs!m_1)]" by simp
    ultimately show ?thesis by fastforce
  qed
qed

fun Gale_Shapley'::"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix
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

fun Gale_Shapley::"pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching" where
"Gale_Shapley MPrefs WPrefs = (let N = length MPrefs in
 Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0))"
end