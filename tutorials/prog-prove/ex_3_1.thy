theory ex_3_1
  imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
fun set::"'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

(* true \<longrightarrow> isLeft *)
fun isOrdered::"int \<Rightarrow> bool \<Rightarrow> int tree \<Rightarrow> bool" where
"isOrdered _ _ Tip = True" |
"isOrdered parent True (Node _ child _) = (child \<le> parent)" |
"isOrdered parent False (Node _ child _) = (parent \<le> child)"

fun ord::"int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l a r) = (isOrdered a True l 
                   \<and> isOrdered a False r 
                   \<and> ord l \<and> ord r)"

fun ins::"int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l a r) = (if x = a then (Node l a r) 
                 else (if x < a then (Node (ins x l) a r)
                                else (Node l a (ins x r))))"

theorem inserted:"set (ins x t) = {x} \<union> set t"
  apply (induction t)
  by (auto)

lemma isOrdered_ins_l:"\<lbrakk>i < a; isOrdered a True t\<rbrakk> \<Longrightarrow> isOrdered a True (ins i t)"
  apply (induction t)
  by (auto)

lemma isOrdered_ins_r:"\<lbrakk>i > a; isOrdered a False t\<rbrakk> \<Longrightarrow> isOrdered a False (ins i t)"
  apply (induction t)
  by (auto)

theorem still_ordered:"ord t \<Longrightarrow> ord(ins i t)"
  apply (induction t)
  apply (auto)
  apply (rule isOrdered_ins_l)
  apply (auto)
  apply (rule isOrdered_ins_r)
  by (auto)
end