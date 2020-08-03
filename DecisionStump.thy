theory DecisionStump
imports
  Complex_Main
  "HOL-Data_Structures.Cmp"
begin

text "This document contains an attempt at providing an upper bound for the error of decision stumps.
      Since there is no non-trivial (better than 0.5) upper bound without assumptions, 
      I tried to specify the conditions necessary for such a bound. I proof that the condition
      I came up with is sufficient for the bound provided but it turns out, it is not a necessary
      condition for a bound <0.5 and as such not optimal. However, such a bound would not be very
      powerful so this side-project was stopped."

locale Stump =
  fixes X :: "'a set"
    and y :: "'a \<Rightarrow> real"
    and D :: "'a \<Rightarrow> real"
    and comp :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> cmp_val"
    and d1 :: nat
  assumes 
       nonemptyx: "X \<noteq> {}"
    and finitex: "finite X"
    and ytwoclass: "\<forall>x. y x \<in> {-1,1}"
    and Dsum: "sum D X = 1"
    and dgtz: "\<forall>x. D x \<ge> 0"
    and comprefl: "\<forall>x d. comp x x d = EQ"
    and compcomm: "\<forall>x y d. (comp x y d = EQ) = (comp y x d = EQ)"
begin


lemma 
  assumes "\<forall>Xs\<subseteq>X. Xs \<noteq> {} \<longrightarrow> (\<exists>x1\<in>Xs.\<exists>d\<le>d1. \<forall>x2\<in>X. ((comp x1 x2 d = EQ) \<longrightarrow> (y x1 = y x2)))"
      and "\<forall>x. D x \<ge> 0"
      and "\<forall>x d. comp x x d = EQ"
      and "(\<forall>x3\<in>X. \<forall>d3\<le>d1. 1 / (2 ^ (card X)) > \<bar>\<Sum>x | x \<in> X \<and> comp x3 x d3 = EQ. D x * y x\<bar>)"  
    shows part2: "n \<le> card X \<Longrightarrow> \<exists>S\<subseteq>X. card(S) = n \<and> sum D S \<le> 1/(2^(card (X-S))) - 1/(2^(card X))"
proof(induction n)
case 0
  then show ?case
    using zero_less_power by auto 
next
  case c1:(Suc n)
  then show ?case 
  proof(cases "n < card X")
    case c2: True
    from c1 obtain S where s1:"card S = n" "S\<subseteq>X" "sum D S \<le> 1/(2^(card (X-S))) - 1/(2^(card X))" by auto
    have s3: "X-S \<subseteq> X" by auto
    have "X-S \<noteq> {}" using c2 s1 by auto
    then obtain x1 d where s4: "x1\<in>(X-S)" "\<forall>x2\<in>(X-S). ((comp x1 x2 d = EQ) \<longrightarrow> (y x1 = y x2))" "d\<le>d1"
      using assms(1) s3 by (meson DiffE)

    have finites: "finite S"
      using finitex rev_finite_subset s1(2) by auto 
    have s01: "X-S \<subseteq> X" by auto
    have s02: "x1 \<notin> S" using s4 by auto 
   have "(\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x * y x)
      = (\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x) * y x1"
    using s4 by (smt CollectD sum.cong sum_distrib_right)    
  then have s010:"\<bar>\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x * y x\<bar>
      = (\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x)"
    using assms(2) ytwoclass
    by (smt empty_iff insertE mult_cancel_left2 mult_minus_right sum_nonneg)

        have s03:"{x\<in>X-S. comp x1 x d = EQ}\<union>{x\<in>S. comp x1 x d = EQ} = {x\<in>X. comp x1 x d = EQ}" using s1(2) by auto
        have s04:"finite {x\<in>S. comp x1 x d = EQ}" using s1(2) finitex finite_subset by fastforce 
        have s05:"finite {x\<in>X-S. comp x1 x d = EQ}" using finitex by auto 
        have s06:"{x\<in>X-S. comp x1 x d = EQ}\<inter>{x\<in>S. comp x1 x d = EQ} = {}" by blast 
  then have s011: "sum (\<lambda>x. D x * y x) {x\<in>X. comp x1 x d = EQ} = 
        sum (\<lambda>x. D x * y x) {x\<in>X-S. comp x1 x d = EQ} +
        sum (\<lambda>x. D x * y x) {x\<in>S. comp x1 x d = EQ}" 
    using Groups_Big.comm_monoid_add_class.sum.union_inter s03 s04 s05 s06 
          Groups_Big.comm_monoid_add_class.sum.empty by smt
  have subs1:"{x\<in>S. comp x1 x d = EQ} \<subseteq> S" by auto
  have s111: "\<forall>x. \<bar> D x * y x\<bar> \<le> D x" using ytwoclass
     by (smt assms(2) empty_iff insert_iff mult_left_le mult_minus_right)
   have "(\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x) \<le>
         \<bar>\<Sum>x | x \<in> (X) \<and> comp x1 x d = EQ. D x * y x\<bar> +
        \<bar>\<Sum>x | x \<in> S \<and> comp x1 x d = EQ. D x * y x\<bar>"
     using Groups.ordered_ab_group_add_abs_class.abs_triangle_ineq4 s010 s011 by auto
   also have "\<bar>\<Sum>x | x \<in> S \<and> comp x1 x d = EQ. D x * y x\<bar> \<le>
              (\<Sum>x | x \<in> S \<and> comp x1 x d = EQ.\<bar> D x * y x\<bar>)"  by blast
   also have "... \<le> (\<Sum>x | x \<in> S \<and> comp x1 x d = EQ. D x)" using s111
     by (simp add: sum_mono) 
   also have "... \<le> sum D S"
     using subs1 by (meson assms(2) finitex infinite_super s1(2) sum_mono2)
   finally have "(\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x) \<le>
         \<bar>\<Sum>x | x \<in> (X) \<and> comp x1 x d = EQ. D x * y x\<bar> + sum D S" by auto
   also have "\<bar>\<Sum>x | x \<in> (X) \<and> comp x1 x d = EQ. D x * y x\<bar> < 1/(2^card X)"
     using assms(4) s4(1,3) by blast
   finally have "(\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x) < 1/(2 ^ (card (X-S)))"
     using s1(3) by auto 
   moreover have "D x1 \<le> (\<Sum>x | x \<in> (X-S) \<and> comp x1 x d = EQ. D x)"
    using assms(2,3) s4
        proof -
          have f1: "\<forall>a r A. ((D a \<le> r \<or> sum D A \<noteq> r) \<or> a \<notin> A) \<or> infinite A"
            by (meson assms(2) sum_nonneg_leq_bound)
        have "finite {a \<in> X - S. comp x1 a d = EQ} \<and> x1 \<in> X - S \<and> comp x1 x1 d = EQ"
        using s4 assms(3) finitex by auto
          then show ?thesis
            using f1 by blast
        qed
  ultimately have s004: "D x1 < 1 / real (2 ^ (card (X-S)))"
    by auto
  have s6: "card (X - (S \<union> {x1})) = card (X - S) - 1"
    using s4(1) finitex by auto
  have s3: "card (X-S) \<ge> 1"
    by (metis One_nat_def Suc_leI s4(1) card_gt_0_iff empty_iff finite_Diff finitex)
  then have "(2::real) ^ (card (X - S) - 1) = 2 ^ card (X - S) / 2 ^ 1"
    by (simp add: power_diff) 
  then have s5: "(2::real) ^ 1 / 2 ^ card (X - S) = 1 / 2 ^ (card (X - S) - 1)"
    by (smt diff_diff_cancel diff_le_self divide_divide_eq_left divide_self_if mult.commute power_diff s3 two_realpow_ge_one)    
  have "sum D (S \<union> {x1}) \<le> sum D S + D x1"
    using s1(2) finite_subset finitex s02 by fastforce 
  then have "sum D (S \<union> {x1}) < 1 / 2 ^ card (X - S) + 1 / 2 ^ card (X - S) - 1 / 2 ^ (card X)" using s004 s1(3) by auto
  then have "sum D (S\<union>{x1})< 1/(2^(card (X-(S\<union>{x1})))) - 1 / 2 ^ (card X)"
     using s5 s6 by auto
     then show ?thesis
       by (smt Un_insert_right card.insert finites insert_subset s01 s02 s1(1) s1(2) s4(1) set_mp sup_bot.right_neutral) 
  next
    case False
    then show ?thesis using c1.prems by auto
  qed
qed

(*sperability assumption formulated*)
lemma 
  assumes "\<forall>Xs\<subseteq>X. Xs \<noteq> {} \<longrightarrow> (\<exists>x1\<in>Xs.\<exists>d\<le>d1. \<forall>x2\<in>X. ((comp x1 x2 d = EQ) \<longrightarrow> (y x1 = y x2)))"
  and "sum D X = 1"
  and "\<forall>x. D x \<ge> 0"
  and "\<forall>x d. comp x x d = EQ"
  shows part1: "\<exists>x3\<in>X.\<exists>d3\<le>d1. abs (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) \<ge> 1/(2^ (card X))"
proof(rule ccontr)
  assume "\<not>?thesis"
  then have s1: "(\<forall>x3\<in>X. \<forall>d3\<le>d1. 1 / real (2 ^ (card X)) > \<bar>\<Sum>x | x \<in> X \<and> comp x3 x d3 = EQ. D x * y x\<bar>)"
    using linorder_not_le by auto
    have "\<exists>S\<subseteq>X. card S = card X \<and> sum D S \<le> 1/(2^(card (X-S))) - 1/(2^(card X))"
      using s1 assms(1,3,4) part2 by auto
    then obtain S where s2: "S\<subseteq>X" "card S = card X" "sum D S \<le> 1/(2^(card (X-S))) - 1/(2^(card X))"
      by auto
    then have "S = X" using finitex Finite_Set.card_subset_eq by auto
    then have "sum D X < 1" using s2(3)
      by (smt Diff_cancel card_empty divide_numeral_1 power_0 zero_less_divide_1_iff zero_less_power) 
    then show False using assms(2) by auto
qed

(*apply to set is image*)

type_synonym 'b split  = "('b \<times> nat \<times> bool)"

definition "allsplits = X \<times> {0..d1} \<times> {False, True}"

fun comsplit :: "'a split \<Rightarrow> ('a split \<times> bool \<times> bool)" where
"comsplit s = (if snd (snd s) then (s, sum D {x\<in>X. y x = 1 \<and> comp x (fst s) (fst (snd s)) = LT}
                                > sum D {x\<in>X. y x = -1 \<and> comp x (fst s) (fst (snd s)) = LT},
                                 sum D {x\<in>X. y x = 1 \<and> comp x (fst s) (fst (snd s)) \<noteq> LT}
                                > sum D {x\<in>X. y x = -1 \<and> comp x (fst s) (fst (snd s)) \<noteq> LT})
                else (s, sum D {x\<in>X. y x = 1 \<and> comp x (fst s) (fst (snd s)) = GT}
                                > sum D {x\<in>X. y x = -1 \<and> comp x (fst s) (fst (snd s)) = GT},
                                 sum D {x\<in>X. y x = 1 \<and> comp x (fst s) (fst (snd s)) \<noteq> GT}
                                > sum D {x\<in>X. y x = -1 \<and> comp x (fst s) (fst (snd s)) \<noteq> GT}))"

fun err :: "'a split \<Rightarrow> real" where
"err (x3,d3,b) = (if b then min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 = LT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 = LT}) +
                                min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 \<noteq> LT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 \<noteq> LT})
                else min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 = GT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 = GT}) +
                                min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 \<noteq> GT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 \<noteq> GT}))"


lemma assumes "\<forall>Xs\<subseteq>X. Xs \<noteq> {} \<longrightarrow> (\<exists>x1\<in>Xs.\<exists>d\<le>d1. \<forall>x2\<in>X. ((comp x1 x2 d = EQ) \<longrightarrow> (y x1 = y x2)))"
      shows "Inf (image err allsplits) \<le> 1/2 - 1 / 2^(card X + 1)"
proof(rule ccontr)
  assume a1: "\<not>?thesis"
  have "\<exists>x3\<in>X.\<exists>d3\<le>d1. abs (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) \<ge> 1/(2^ (card X))"
    using part1 dgtz Dsum comprefl assms by auto
  then obtain x3 d3 where s1: "x3\<in>X" "d3\<le>d1" "abs (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) \<ge> 1/(2^ (card X))"
    by auto
  have s2: "(x3, d3, False) \<in> allsplits" using allsplits_def s1(1,2) by auto
  have s3: "bdd_below (image err allsplits)" using allsplits_def finitex by auto
  from a1 have "1/2 - 1 / 2^(card X + 1) < (INF i:allsplits. err i)" by auto
  from s2 s3 this have s20: "err (x3, d3, False) > 1/2 - 1 / 2^(card X + 1)" 
    using Conditionally_Complete_Lattices.conditionally_complete_lattice_class.less_cINF_D
        [of err allsplits "1/2 - 1 / 2^(card X + 1)" "(x3, d3, False)"] by auto
  have s4: "err (x3, d3, False) = min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 = GT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 = GT}) +
                                min (sum D {x\<in>X. y x = 1 \<and> comp x3 x d3 \<noteq> GT})
                                (sum D {x\<in>X. y x = -1 \<and> comp x3 x d3 \<noteq> GT})" by auto
  let ?s = "sgn (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ})"
  have s5: "?s \<in> {-1,1}" using s1(3) zero_less_power
    by (smt insertCI sgn_neg sgn_pos zero_less_divide_1_iff) 
  from this s4 have "(sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> GT}) +
        (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT}) \<ge> err (x3, d3, False)"
    by (smt Collect_cong empty_iff insert_iff)
  from this s1(3) have s12: "abs (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) +
             (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> GT}) +
             (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT})
              \<ge> err (x3, d3, False) + 1/(2^ (card X))" by auto
  have s13: "abs (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ})
      = ?s * (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ})"
    by (simp add: linordered_idom_class.abs_sgn)
  have "{x\<in>X. comp x3 x d3 = EQ} = {x\<in>{x\<in>X. comp x3 x d3 = EQ}. y x = ?s} \<union> {x\<in>{x\<in>X. comp x3 x d3 = EQ}. y x \<noteq> ?s}"
    by auto
  then have "{x\<in>X. comp x3 x d3 = EQ} = {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ} \<union> {x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ}"
    by auto
  moreover have "{x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ} \<inter> {x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ} = {}"
    by auto
  moreover have "finite {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}" using finitex by auto
  moreover have "finite {x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ}" using finitex by auto
  ultimately have s6: "(sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) = ((sum (\<lambda>x. D x * y x) {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}) +
                        (sum (\<lambda>x. D x * y x) {x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ}))"
    using sum.union_disjoint by (metis (no_types, lifting))
  have s9: "(sum (\<lambda>x. D x * y x) {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}) = (sum (\<lambda>x. D x * ?s) {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ})"
    by auto
  then have s7: "(sum (\<lambda>x. D x * ?s) {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}) = ?s * (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ})"
    by (smt mult.commute sum.cong sum_distrib_left)
  have s11: "{x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ} = {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}"
    using s5 ytwoclass by auto 
  then have s8: "(sum (\<lambda>x. D x * y x) {x\<in>X. y x \<noteq> ?s \<and> comp x3 x d3 = EQ}) = (sum (\<lambda>x. D x * -1*?s) {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ})"
    by auto
  have s10: "(sum (\<lambda>x. D x * -1*?s) {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}) = -1*?s*(sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ})"
    by (smt mult.commute mult_minus_left sum.cong sum_distrib_left)
   have "?s * (sum (\<lambda>x. D x * y x) {x\<in>X. comp x3 x d3 = EQ}) =  (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}) -
                        (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ})"
     by (smt mult_cancel_right1 mult_minus_left s1(3) s10 s11 s6 s7 s8 s9 sgn_neg sgn_pos zero_less_divide_1_iff zero_less_power) 
   from this s12 s13 have s14: "(sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}) -
                           (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}) + 
                           (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> GT}) +
                           (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT})
                            \<ge> err (x3, d3, False) + 1/(2^ (card X))"
     by linarith
   have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT} \<inter> {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ} = {}"
     by auto
   moreover have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> GT} =
          {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT} \<union> {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}"
   using Un_def[of "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}" "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}"]
     by (smt Collect_cong cmp_val.distinct(3) cmp_val.distinct(5) cmp_val.exhaust mem_Collect_eq)
   moreover have "finite {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}" using finitex by auto
   moreover have "finite {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ}" using finitex by auto
   ultimately have s15: "(sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> GT})
       - (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = EQ})
       = (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT})"
    using sum.union_disjoint by smt

   have "{x\<in>X. y x = ?s \<and> comp x3 x d3 = GT} \<inter> {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ} = {}"
     by auto
   moreover have "{x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT} =
          {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT} \<union> {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}"
     using Un_def[of "{x\<in>X. y x = ?s \<and> comp x3 x d3 = GT}" "{x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}"]
     by (smt Collect_cong cmp_val.distinct(4) cmp_val.distinct(2) cmp_val.exhaust mem_Collect_eq)
   moreover have "finite {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT}" using finitex by auto
   moreover have "finite {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ}" using finitex by auto
   ultimately have "(sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT})
       = (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = EQ})
       + (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = GT})"
    using sum.union_disjoint by smt
  
  from this s14 s15 have s21: " (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}) + 
                           (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT})
                            \<ge> err (x3, d3, False) + 1/(2^ (card X))"
    by linarith
  from s20 have "err (x3, d3, False) + (1::real)/(2^ (card X))
                            > 1/2 + 1/(2^ (card X + 1))"
    by simp
  from s21 this have s22: "(sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}) + 
                      (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT})
                        > 1/2 + 1/(2^ (card X + 1))"
    by linarith
  have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT} \<union> {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}
        = {x\<in>X. comp x3 x d3 = LT}" using s5 ytwoclass by auto
  moreover have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT} \<inter> {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}
        = {}" using s5 by auto
  moreover have "finite {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}" using finitex by auto
  moreover have "finite {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}" using finitex by auto
  ultimately have "(sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}) + 
                   (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}) = 
                   (sum D {x\<in>X. comp x3 x d3 = LT})"
    using sum.union_disjoint by smt
  moreover have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT} \<union> {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT}
        = {x\<in>X. comp x3 x d3 \<noteq> LT}" using s5 ytwoclass by auto
  moreover have "{x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT} \<inter> {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT}
        = {}" using s5 by auto
  moreover have "finite {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT}" using finitex by auto
  moreover have "finite {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT}" using finitex by auto
  ultimately have "(sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}) + 
                   (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}) +
                   (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT}) + 
                   (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT}) = 
                   (sum D {x\<in>X. comp x3 x d3 = LT}) +
                   (sum D {x\<in>X. comp x3 x d3 \<noteq> LT})"
    using sum.union_disjoint by smt
  moreover have "{x\<in>X. comp x3 x d3 = LT} \<union> {x\<in>X. comp x3 x d3 \<noteq> LT} = X" by auto
  moreover have "{x\<in>X. comp x3 x d3 = LT} \<inter> {x\<in>X. comp x3 x d3 \<noteq> LT} = {}" by auto
  moreover have "finite {x\<in>X. comp x3 x d3 = LT}" using finitex by auto
  moreover have "finite {x\<in>X. comp x3 x d3 \<noteq> LT}" using finitex by auto
  ultimately have "(sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT}) + 
                   (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 = LT}) +
                   (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 \<noteq> LT}) + 
                   (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT}) = 
                   sum D X"
    using sum.union_disjoint by smt
  from this s22 have "(sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT})+
                      (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT})
                         < 1/2 - 1/(2^ (card X + 1))"
    using Dsum by linarith
  moreover have "err (x3,d3,True) \<le> (sum D {x\<in>X. y x = -1*?s \<and> comp x3 x d3 \<noteq> LT})+
                      (sum D {x\<in>X. y x = ?s \<and> comp x3 x d3 = LT})" using s5 by auto
  ultimately have s24: "err (x3,d3,True) < 1/2 - 1/(2^(card X +1))" by linarith
  have s23: "(x3, d3, True) \<in> allsplits" using allsplits_def s1(1,2) by auto
  from a1 have "1/2 - 1 / 2^(card X + 1) < (INF i:allsplits. err i)" by auto
  from s23 s3 this have s20: "err (x3, d3, True) > 1/2 - 1 / 2^(card X + 1)" 
    using Conditionally_Complete_Lattices.conditionally_complete_lattice_class.less_cINF_D
        [of err allsplits "1/2 - 1 / 2^(card X + 1)" "(x3, d3, True)"] by auto
  from this s24 show False by auto
qed