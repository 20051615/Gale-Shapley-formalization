theory Gale_Shapley
  imports Main
begin
type_synonym person = "nat"
type_synonym man = "person"
type_synonym woman = "person"
type_synonym pref_matrix = "(person list) list"
type_synonym matching = "(woman option) list"

fun findFreeMan::"matching \<Rightarrow> man option" where
"findFreeMan [] = None" |
"findFreeMan (None # ops) = Some 0" |
"findFreeMan ((Some w) # ops) = (case findFreeMan ops of None \<Rightarrow> None | Some m \<Rightarrow> Some (m + 1))"

fun findFiance::"matching \<Rightarrow> woman \<Rightarrow> man option" where
"findFiance [] _ = None" |
"findFiance (None # ops) w = (case (findFiance ops w) of None \<Rightarrow> None | Some m \<Rightarrow> Some (m + 1))" |
"findFiance ((Some w1) # ops) w = (if w1 = w then (Some 0) else
                             (case (findFiance ops w) of None \<Rightarrow> None | Some m \<Rightarrow> Some (m + 1)))"

fun find_idx::"person list \<Rightarrow> person \<Rightarrow> nat" where
"find_idx [] p = 0" |
"find_idx (p1 # ps) p = (if p = p1 then 0 else 1 + find_idx ps p)"

fun prefers::"person \<Rightarrow> pref_matrix \<Rightarrow> person \<Rightarrow> person \<Rightarrow> bool" where
"prefers p PPrefs p1 p2 = (let PPref = PPrefs!p in
                          find_idx PPref p1 < find_idx PPref p2)"

fun Gale_Shapley'::"nat \<Rightarrow> pref_matrix \<Rightarrow> pref_matrix
 \<Rightarrow> matching \<Rightarrow> nat list \<Rightarrow>
 matching" where
"Gale_Shapley' N MPrefs WPrefs 
 engagements prop_idxs 
 = 
(if sum_list prop_idxs \<ge> N * N then engagements else
  (case findFreeMan engagements of 
   None \<Rightarrow> engagements |
   Some m \<Rightarrow> (let w = (MPrefs!m)!(prop_idxs!m);
     next_prop_idxs = list_update prop_idxs m (Suc (prop_idxs!m)) in (
     case findFiance engagements w of
       None \<Rightarrow> Gale_Shapley' N MPrefs WPrefs 
         (list_update engagements m (Some w)) next_prop_idxs
     | Some m' \<Rightarrow> (
       if prefers w WPrefs m m' then Gale_Shapley' N MPrefs WPrefs
         (list_update (list_update engagements m (Some w)) m' None) next_prop_idxs
       else Gale_Shapley' N MPrefs WPrefs
         engagements next_prop_idxs
     )
   ))
  )
)"

fun Gale_Shapley::"pref_matrix \<Rightarrow> pref_matrix \<Rightarrow> matching" where
"Gale_Shapley MPrefs WPrefs = (let N = length MPrefs in
 Gale_Shapley' N MPrefs WPrefs (replicate N None) (replicate N 0))"
end