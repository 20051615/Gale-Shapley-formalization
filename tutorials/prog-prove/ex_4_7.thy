theory ex_4_7
  imports Main ex_3_5
begin
fun balanced::"nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 [] = True" |
"balanced _ [] = False" |
"balanced 0 (b # as) = False" |
"balanced (Suc n) (b # as) = balanced n as" |
"balanced n (a # as) = balanced (Suc n) as"


theorem balanced_n_S_n:"balanced n w = S (replicate n a @ w)"
proof
  show "balanced n w \<Longrightarrow> S (replicate n a @ w)"
  proof (induction n w rule:balanced.induct)
    case 1
    show ?case using S.intros(1) by simp
  next
    case 2
    hence False by simp
    thus ?case by blast
  next
    case 3
    hence False by simp
    thus ?case by blast
  next
    case (4 n as)
    hence "S (replicate n a @ as)" by simp
    moreover have "S (replicate n a @ as) \<Longrightarrow> S (replicate (Suc n) a @ b # as)"
    proof (induction "replicate n a @ as" arbitrary: n as rule:S.induct)
      case 1
      hence "n = 0 \<and> as = []" by simp
      thus ?case using S.intros(1) S.intros(2) by fastforce
    next
      case (2 w)
      show ?case
      proof cases
        assume "n = 0"
        with "2.hyps"(3) have "a # w @ [b] = as" by simp
        with S.intros(2) `S w` have "S as" by fastforce

        from `n = 0` have goal:"replicate (Suc n) a @ b # as = a # [b] @ as" by simp

        from S.intros have "S (a # [b])" by fastforce
        with `S as` S.intros(3) have "S (a # [b] @ as)" by fastforce
        thus ?case using goal by simp 
      next
        assume "n \<noteq> 0"
        with "2.hyps"(3) have "w @ [b] = replicate (n - 1) a @ as"
          by (metis One_nat_def Suc_pred append_Cons list.inject not_gr_zero replicate_Suc)
        moreover with `n \<noteq> 0` "2.hyps"(3) have w:"w = replicate (n - 1) a @ take (length as - 1) as"
          by (smt alpha.distinct(1) append_is_Nil_conv butlast_append butlast_conv_take butlast_snoc last.simps last_append last_replicate)
        ultimately have as:"as = take (length as - 1) as @ [b]" by simp

        from "2.hyps"(2) w `n \<noteq> 0` have "S (replicate n a @ b # take (length as - 1) as)"
          by (metis One_nat_def Suc_pred not_gr_zero)
        with S.intros(2) have "S (replicate (Suc n) a @ b # take (length as - 1) as @ [b])" by fastforce
        with as show ?case by simp
      qed
    next
      case (3 x y)
      show ?case
      proof cases
        assume "n \<le> length x"
        with "3.hyps"(5) have x:"x = (replicate n a) @ drop n x"
          by (metis append_eq_append_conv_if append_eq_conv_conj length_replicate)
        with "3.hyps"(5) have as:"drop n x @ y = as"
          by (metis append.assoc same_append_eq)

        from "3.hyps"(2) x have "S (replicate (Suc n) a @ b # (drop n x))" by fastforce
        with S.intros(3) "3.hyps"(3) have "S (replicate (Suc n) a @ b # (drop n x) @ y)" by fastforce
        with as show ?case by simp
      next
        assume asm:"\<not> n \<le> length x"

        let ?x = "replicate (length x) a"
        from "3.hyps"(5) have "x = take (length x) (replicate n a @ as)"
          using append_eq_conv_conj by blast 
        also have "... = ?x" using asm by auto
        finally have "x = ?x" .

        let ?y = "replicate (n - length x) a @ as"
        let ?y_front_a = "replicate (Suc (n - length x)) a"
        let ?y_ab = "?y_front_a @ b # as"
        from "3.hyps"(5) asm have "y = ?y"
          by (metis append_eq_append_conv_if drop_replicate length_replicate)
        with "3.hyps"(4) have "S ?y_ab" by fastforce
        with S.intros(3) "3.hyps"(1) have "S (x @ ?y_ab)" by fastforce

        have "?x @ ?y_front_a = replicate (Suc n) a" using asm
          by (metis replicate_add add_Suc_right le_add_diff_inverse nat_le_linear)
        with `x = ?x` `S (x @ ?y_ab)` show ?case by (metis append_assoc)
      qed
    qed
    ultimately show ?case by simp
  next
    case (5 n as)
    thus ?case by (simp add: replicate_app_Cons_same)
  qed
next
  have b_notS:"S (b # as) \<Longrightarrow> False" for as
    proof (induction "b # as" arbitrary: as rule:S.induct)
      case (3 x y)
      show False
      proof (cases x)
        case Nil
        with "3.hyps"(5) have "y = b # as" by simp
        with "3.hyps"(4) show ?thesis by blast
      next
        case Cons
        hence "length x > 0" by simp
        with "3.hyps"(5) have "x = b # drop 1 x" by (simp add: local.Cons)
        with "3.hyps"(2) show ?thesis by blast
      qed
    qed
  have "\<not>balanced n w \<Longrightarrow> \<not> S(replicate n a @ w)"
  proof (induction n w rule:balanced.induct)
    case 1
    hence False by simp
    thus ?case by simp
  next
    case (2 n)
    have "S (replicate (Suc n) a) \<Longrightarrow> False"
    proof (induction "replicate (Suc n) a" arbitrary: n rule: S.induct)
      case 1
      thus ?case by simp
    next
      case (2 w)
      from "2.hyps"(3) show ?case
        by (metis alpha.distinct(1) last_ConsR last_replicate old.nat.distinct(2) snoc_eq_iff_butlast)
    next
      case (3 x y)
      from "3.hyps"(5) have x:"x = replicate (length x) a"
        by (metis append_eq_append_conv length_append length_replicate replicate_add)
      from "3.hyps"(5) have y:"y = replicate (length y) a"
        by (metis append_eq_append_conv length_append length_replicate replicate_add)
      from "3.hyps"(5) have x_y_length:"length x + length y = Suc n"
        by (metis length_append length_replicate)
      show ?case
      proof cases
        assume "length x > 0"
        with "3.hyps"(2) x show ?case by (metis Suc_pred)
      next
        assume "\<not>length x > 0"
        with x_y_length have "length y > 0" by simp
        with "3.hyps"(4) y show ?case by (metis Suc_pred)
      qed
    qed
    thus ?case by auto
  next
    case (3 as)   
    with b_notS show ?case by fastforce
  next
    case (4 n as)
    have "S (replicate (Suc n) a @ b # as) \<Longrightarrow> S (replicate n a @ as)"
    proof (induction "replicate (Suc n) a @ b # as" arbitrary:n as rule:S.induct)
      case 1
      hence False by simp
      thus ?case by blast
    next
      case (2 w)
      thus ?case
      proof (cases n)
        case 0
        show ?thesis
        proof (cases w)
          case Nil
          with "2.hyps"(3) 0 have "as = []" by simp
          thus ?thesis using 0 S.intros(1) by simp
        next
          case (Cons w_0 ws)
          with "2.hyps"(3) 0 have "w = b # drop 1 w" by simp
          with b_notS "2.hyps"(1) have False by metis
          thus ?thesis by blast
        qed
      next
        case (Suc n_1)
        have as_notS:"S(replicate (Suc k) a) \<Longrightarrow> False" for k
        proof (induction "replicate (Suc k) a" arbitrary: k rule:S.induct)
          case 1
          thus ?case by simp
        next
          case 2
          from "2.hyps"(3) show ?case
            by (metis alpha.distinct(1) last.simps last_replicate nat.distinct(1) snoc_eq_iff_butlast)
        next
          case (3 x y)
          show ?case
          proof (cases x)
            case Nil
            with "3.hyps"(5) have "y = replicate (Suc k) a" by simp
            with "3.hyps"(4) show ?thesis by auto
          next
            case Cons
            with "3.hyps"(5) have "x = replicate (length x) a"
              by (metis append.assoc append_eq_append_conv append_replicate_commute length_replicate)
            with "3.hyps"(2) Cons show ?thesis by auto
          qed
        qed
        show ?thesis
        proof (cases as)
          case Nil
          with "2.hyps"(3) have "w = replicate n a" by simp
          with Suc "2.hyps"(1) as_notS show ?thesis by blast
        next
          case Cons
          from "2.hyps"(3) Suc have "w @ [b] = replicate (Suc n_1) a @ b # as" by simp
          moreover with Cons have as:"as = take (length as - 1) as @ [b]"
            by (metis append_butlast_last_id butlast_conv_take last.simps last_append list.distinct(1))
          ultimately have "w = replicate (Suc n_1) a @ b # take (length as - 1) as"
            by (metis (no_types, lifting) Cons_replicate_eq butlast.simps(2) butlast_append butlast_snoc empty_replicate less_numeral_extra(3) local.Cons)
          with "2.hyps"(2) have "S (replicate n_1 a @ take (length as - 1) as)" by simp
          with S.intros(2) have "S (a # (replicate n_1 a @ take (length as - 1) as) @ [b])" by blast
          with Suc as show ?thesis by auto
        qed
      qed
    next
      case (3 x y)
      have "length x \<le> n \<or> (length x = Suc n) \<or> length x \<ge> n + 2" by auto
      thus ?case
      proof
        assume asm:"length x \<le> n"
        hence "length x \<le> Suc n" by auto
        with "3.hyps"(5) have x:"x = replicate (length x) a"
          by (metis append_eq_append_conv_if append_eq_conv_conj length_replicate nat_le_iff_add replicate_add)
        with "3.hyps"(5) `length x \<le> Suc n` have "y = replicate (Suc n - length x) a @ b # as"
          by (metis append_eq_append_conv_if drop_replicate length_replicate)
        moreover from asm have "Suc n - length x > 0" by auto
        ultimately have "S (replicate (n - length x) a @ as)" using "3.hyps"(4)
          by (simp add: Suc_diff_le)
        with S.intros(3) "3.hyps"(1) have "S (x @ replicate (n - length x) a @ as)" by auto
        with x have "S (replicate (length x) a @ replicate (n - length x) a @ as)" by auto
        with asm show ?case by (metis replicate_add append_assoc le_add_diff_inverse)
      next
        assume "length x = Suc n \<or> length x \<ge> n + 2"
        thus ?case
        proof
          assume "length x = Suc n"
          with "3.hyps"(5) have "y = b # as"
            by (metis append_eq_append_conv length_replicate)
          with b_notS "3.hyps"(3) have False by auto
          thus ?case by auto
        next
          assume asm:"length x \<ge> n + 2"
          let ?front = "(replicate (Suc n) a @ [b])"
          from "3.hyps"(5) have "x @ y = ?front @ as" by simp
          moreover with asm have "length x \<ge> length ?front" by auto
          ultimately have "x = ?front @ take (length x - length ?front) as"
            by (metis append.right_neutral cancel_comm_monoid_add_class.diff_cancel dual_order.refl take_0 take_all take_append)
          hence "x = replicate (Suc n) a @ b # take (length x - n - 2) as" by simp
          with "3.hyps"(2) have almost_there:"S (replicate n a @ take (length x - n - 2) as)" by simp

          from `x @ y = ?front @ as` `length x \<ge> length ?front` have "y = drop (length x - length ?front) as"
            by (metis append_eq_conv_conj drop_append drop_eq_Nil self_append_conv2)
          with "3.hyps"(3) have "S (drop (length x - n - 2) as)" by simp
          with almost_there S.intros(3) have "S (replicate n a @ take (length x - n - 2) as @ drop (length x - n - 2) as)" by fastforce
          thus ?case by auto
        qed
      qed
    qed
    hence "\<not> S (replicate n a @ as) \<Longrightarrow> \<not> S (replicate (Suc n) a @ b # as)" by blast
    with "4.prems" "4.IH" show ?case by fastforce
  next
    case (5 n as)
    thus ?case
      by (metis Cons_eq_appendI balanced.simps(5) replicate_Suc replicate_app_Cons_same)
  qed
  thus "S (replicate n a @ w) \<Longrightarrow> balanced n w" by blast
qed

lemma balanced_S:"S w = balanced 0 w"
  by (auto simp add: balanced_n_S_n)

lemma "S [a, a, b, a, b, b]"
  by (auto simp add: balanced_S)
end