\<^marker>\<open>creator Eric Koepke\<close>

theory Theorem611
  imports Complex_Main LearningTheory
begin

text "This document contains a collection of (mostly failed) attempts at gathering subproofs and
  important lemmata for theorem 6.11. It may help proving the theorem in the future and serves
  no other purpose."


 (*measure_pmf.jensens_inequality*)

lemma "AE x in measure_pmf M. X' x \<in> UNIV"
  by simp

lemma "convex_on UNIV abs"
unfolding convex_on_def
  apply (simp)
  by (metis (mono_tags, hide_lams) abs_mult abs_of_nonneg abs_triangle_ineq add.commute mult.commute)

lemma "integrable (measure_pmf M) abs"
  oops

(*for lemma A.3*)
lemma "measure_pmf.expectation p (abs \<circ> f)
   \<le> infsetsum (\<lambda>i. (a::real) * (Suc i) * (measure_pmf.prob p {x. (abs \<circ> f) x > a * i})) UNIV"
  oops

lemma "abs (infsetsum f A) \<le> infsetsum (abs \<circ> f) A"
  oops




lemma "\<forall>x. f x \<in> {-1<..<1::real} \<Longrightarrow> f \<in> borel_measurable borel"
  oops


lemma "\<forall>x. f x \<in> {-1<..<1::real} \<Longrightarrow> simple_function (measure_pmf M) f"
  oops

lemma "\<forall>x. f x \<in> {-1<..<1} \<Longrightarrow> integrable (measure_pmf M) f"
  oops

lemma "emeasure (measure_pmf M) {(y::real) \<in> space M. id y \<noteq> 0} \<noteq> \<infinity>"
  by simp 

lemma "integrable (measure_pmf M) (id::(real\<Rightarrow>real))" 
  oops

lemma if_summable: "f abs_summable_on A \<Longrightarrow> (\<lambda>x. if P x then f x else 0) abs_summable_on A"
  by (simp add: abs_summable_on_comparison_test)

lemma "(\<lambda>x. if h x \<noteq> f x then pmf D x else 0) abs_summable_on A"
  using pmf_abs_summable[of "D"] if_summable[of "pmf D"] by auto

lemma exp_to_prob: "measure_pmf.expectation pr (\<lambda>x. if P x then 1::real else 0)
     = measure_pmf.prob pr {x. P x}"
proof -
  have "measure_pmf.expectation pr (\<lambda>x. if P x then 1::real else 0)
      = infsetsum (\<lambda>x. if P x then pmf pr x else 0) UNIV"
    by (smt infsetsum_cong mult_cancel_left2 mult_not_zero pmf_expectation_eq_infsetsum)
  also have "... = ... - infsetsum (\<lambda>x. if P x then pmf pr x else 0) {x. \<not> P x}"
    by (smt infsetsum_all_0 mem_Collect_eq)
  also have "... = infsetsum (\<lambda>x. if P x then pmf pr x else 0) (UNIV - {x. \<not> P x})"
    by (simp add: if_summable infsetsum_Diff pmf_abs_summable)
  also have "... = infsetsum (\<lambda>x. if P x then pmf pr x else 0) {x. P x}"
  proof -
    have "UNIV - {x. \<not> P x} = {x. P x}"
      by blast
    then show ?thesis by auto
  qed 
  also have "... = infsetsum (pmf pr) {x. P x}"
    by (smt infsetsum_cong mem_Collect_eq)
  finally show ?thesis
    by (simp add: measure_pmf_conv_infsetsum) 
qed

lemma "((g:: 'c \<Rightarrow> real) y) * measure_pmf.expectation D f = measure_pmf.expectation D (\<lambda>x. (g y) * f x)"
   by simp

lemma "measure_pmf.expectation D f - (a::real) = measure_pmf.expectation D (\<lambda>x. f x - a)"
proof -
  have "measure_pmf.expectation D f - (a::real) = (\<Sum>\<^sub>ax. pmf D x * f x) - (\<Sum>\<^sub>ax. pmf D x * a)"
    using pmf_expectation_eq_infsetsum infsetsum_pmf_eq_1
  proof -
    have "\<forall>p. integral\<^sup>L (count_space (UNIV::'c set)) (pmf p) = 1"
      by (metis (no_types) infsetsum_def measure_pmf_UNIV measure_pmf_conv_infsetsum)
    then show ?thesis sorry
  qed 
  show ?thesis sorry
qed


lemma assumes "card I > 0"
          and "(\<lambda>x. pmf D x * f x) abs_summable_on UNIV"
  shows stichprobenmittel: "measure_pmf.expectation (Pi_pmf I undefined (\<lambda>_. D)) (\<lambda>S. sum (f \<circ> S) I / card I)
     = measure_pmf.expectation D f"
proof -
(*
  have "measure_pmf.expectation (Pi_pmf I undefined (\<lambda>_. D)) (\<lambda>S. sum (f \<circ> S) I / card I)
      = sum (\<lambda>_.(measure_pmf.expectation D f)) I / card I"
    *)
  have "i\<notin>I \<Longrightarrow> sum (f \<circ> S) (insert i I) / (card I + 1) 
      = sum (f \<circ> S) I / (card I + 1) + (f \<circ> S) i / (card I + 1)"
    sorry
   (* by (metis add.commute add_divide_distrib assms card.infinite not_less0 sum.insert_if) *)
      
  have "measure_pmf.expectation (Pi_pmf (insert i I) undefined (\<lambda>_. D)) (\<lambda>S. sum (f \<circ> S) (insert i I) / (card I + 1))
      = measure_pmf.expectation (Pi_pmf (insert i I) undefined (\<lambda>_. D)) (\<lambda>S. sum (f \<circ> S) I / (card I + 1) + f (S i) / (card I + 1))"
    
    sorry
    show ?thesis sorry
qed

lemma assumes "card I > 0"
  shows "measure_pmf.expectation (Pi_pmf I undefined (\<lambda>_. D)) (\<lambda>S. sum (\<lambda>i. if h (S i) \<noteq> f (S i) then 1::real else 0) I / card I)
     = measure_pmf.expectation D (\<lambda>x. if h x \<noteq> f x then 1::real else 0)"
  sorry

(*for Jensens*)
lemma "abs (measure_pmf.expectation p f) \<le> measure_pmf.expectation p (abs \<circ> f)"
  using pmf_expectation_eq_infsetsum abs_triangle_ineq sorry

(*Theorem 6.11*)
lemma assumes "set_pmf D \<subseteq> X"
      and "f ` X = Y"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D f) {S. \<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
proof -
  (* replace max with sup? *)
  have "measure_pmf.expectation (Samples m D f) (\<lambda>S. (Max(image (\<lambda>h. abs(PredErr D f h - TrainErr S {0..<m} h)) H)))
        \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))" sorry
 (* have "\<forall>h\<in>H. measure_pmf.expectation D (\<lambda>x. if h x \<noteq> f x then 1::real else 0) = (\<Sum>\<^sub>ax. pmf D x * (\<lambda>x. if h x \<noteq> f x then 1::real else 0) x)"
    using pmf_expectation_eq_infsetsum by auto
  have "\<forall>h\<in>H. (\<Sum>\<^sub>ax. pmf D x * (\<lambda>x. if h x \<noteq> f x then 1::real else 0) x) = (\<Sum>\<^sub>ax. (if h x \<noteq> f x then pmf D x else 0))"
    by (smt infsetsum_cong mult_cancel_left1 mult_cancel_right1)
  have "\<forall>h A.(\<lambda>x. if h x \<noteq> f x then pmf D x else 0) abs_summable_on A"
    using pmf_abs_summable[of "D"] if_summable[of "pmf D"] by auto
  then have "\<forall>h\<in>H. infsetsum (\<lambda>x. if h x \<noteq> f x then pmf D x else 0) (UNIV - {x. h x = f x})
        = (\<Sum>\<^sub>ax. (if h x \<noteq> f x then pmf D x else 0)) - infsetsum (\<lambda>x. if h x \<noteq> f x then pmf D x else 0) {x. h x = f x}"
    by (simp add: infsetsum_Diff)
  have "\<forall>h\<in>H. infsetsum (\<lambda>x. if h x \<noteq> f x then pmf D x else 0) {x. h x = f x} = 0"
    by (smt infsetsum_all_0 mem_Collect_eq)
  have "\<forall>h\<in>H. infsetsum (\<lambda>x. if h x \<noteq> f x then pmf D x else 0) (UNIV - {x. h x = f x}) = infsetsum (pmf D) {x. h x \<noteq> f x}"
    by (smt Diff_iff UNIV_I infsetsum_Diff infsetsum_all_0 infsetsum_cong infsetsum_def mem_Collect_eq pmf_abs_summable subsetI)
      
*)fix h I
  have "PredErr D f h = measure_pmf.expectation D (\<lambda>x. if h x \<noteq> f x then 1::real else 0)"
    unfolding PredErr_def using exp_to_prob[of D "(\<lambda>x. h x \<noteq> f x)"]
    by (smt Collect_cong)
  moreover assume "card I > 0"
  moreover have "(\<lambda>x. pmf D x * (\<lambda>x. if h x \<noteq> f x then 1::real else 0) x) abs_summable_on UNIV"
    using pmf_abs_summable[of "D"] if_summable[of "pmf D"]
    by (smt abs_summable_on_comparison_test mult_cancel_left1 mult_not_zero zero_less_norm_iff)
  ultimately have "measure_pmf.expectation (Pi_pmf I undefined (\<lambda>_. D))
              (\<lambda>S. sum (\<lambda>i. if h (S i) \<noteq> f (S i) then 1::real else 0) I / card I)
               = PredErr D f h"
    using stichprobenmittel by auto
  have "\<forall>h\<in>H. (PredErr D f h) = measure_pmf.expectation (Samples m D f) (\<lambda>S. TrainErr S {0..m} h)"
    unfolding PredErr_def TrainErr_def Samples_def 
    sorry
  show ?thesis sorry
qed
