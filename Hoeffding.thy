(*
  File:    Hoeffding.thy
  Author:  Manuel Eberl
  
  Original version by Maximilian P. L. Haslbeck
*)
section \<open>Hoeffding's Lemma and Hoeffding's Inequality for PMFs\<close>
theory Hoeffding
  imports Pi_pmf
begin

subsection \<open>Auxiliary material\<close>

lemma finite_set_pmf_binomial_pmf [intro]: "p \<in> {0..1} \<Longrightarrow> finite (set_pmf (binomial_pmf n p))"
  by (subst set_pmf_binomial_eq) auto

lemma expectation_binomial_pmf [simp]:
  assumes p: "p \<in> {0..1}"
  shows   "measure_pmf.expectation (binomial_pmf n p) real = real n * p"
proof (induction n)
  case 0
  thus ?case using p by (simp add: binomial_pmf_0)
next
  case (Suc n)
  have int: "integrable (measure_pmf (binomial_pmf n p)) real"
    using p by (intro integrable_measure_pmf_finite) auto
  have "measure_pmf.expectation (binomial_pmf (Suc n) p) real =
           (1 - p) * (real n * p) + p * (1 + real n * p)"
    unfolding binomial_pmf_Suc[OF p] using p Suc int
    by (subst pmf_expectation_bind[where A = UNIV])
       (auto simp: binomial_pmf_Suc UNIV_bool bind_return_pmf
                   pmf_expectation_bind[where A = UNIV] simp flip: map_pmf_def intro!: finite_imageI)
  also have "\<dots> = real (Suc n) * p"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma expectation_binomial_pmf':
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows   "measure_pmf.expectation (binomial_pmf n p) f =
             (\<Sum>k\<le>n. (real (n choose k) * p ^ k * (1 - p) ^ (n - k)) *\<^sub>R f k)"
  using p by (subst integral_measure_pmf[where A = "{..n}"])
             (auto simp: set_pmf_binomial_eq split: if_splits)

lemma integrable_binomial_pmf [simp, intro]:
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows "integrable (binomial_pmf n p) f"
  by (rule integrable_measure_pmf_finite) (use assms in auto)

lemma set_Pi_pmf_subset':
  assumes "finite A"
  shows   "set_pmf (Pi_pmf A dflt p) \<subseteq> PiE_dflt A dflt (set_pmf \<circ> p)"
  using assms by (auto simp: set_pmf_eq pmf_Pi PiE_dflt_def)

lemma set_Pi_pmf:
  assumes "finite A"
  shows   "set_pmf (Pi_pmf A dflt p) = PiE_dflt A dflt (set_pmf \<circ> p)"
proof (rule equalityI)
  show "PiE_dflt A dflt (set_pmf \<circ> p) \<subseteq> set_pmf (Pi_pmf A dflt p)"
  proof safe
    fix f assume f: "f \<in> PiE_dflt A dflt (set_pmf \<circ> p)"
    hence "pmf (Pi_pmf A dflt p) f = (\<Prod>x\<in>A. pmf (p x) (f x))"
      using assms by (auto simp: pmf_Pi PiE_dflt_def)
    also have "\<dots> > 0"
      using f by (intro prod_pos) (auto simp: PiE_dflt_def set_pmf_eq)
    finally show "f \<in> set_pmf (Pi_pmf A dflt p)"
      by (auto simp: set_pmf_eq)
  qed
qed (use set_Pi_pmf_subset'[OF assms, of dflt p] in auto)

lemma nn_integral_prod_Pi_pmf:
  assumes "finite A"
  shows   "nn_integral (Pi_pmf A dflt p) (\<lambda>y. \<Prod>x\<in>A. f x (y x)) = (\<Prod>x\<in>A. nn_integral (p x) (f x))"
  using assms
proof (induction rule: finite_induct)
  case (insert x A)
  have "nn_integral (Pi_pmf (insert x A) dflt p) (\<lambda>y. \<Prod>z\<in>insert x A. f z (y z)) =
          (\<integral>\<^sup>+a. \<integral>\<^sup>+b. f x a * (\<Prod>z\<in>A. f z (if z = x then a else b z)) \<partial>Pi_pmf A dflt p \<partial>p x)"
    using insert by (auto simp: Pi_pmf_insert case_prod_unfold nn_integral_pair_pmf' cong: if_cong)
  also have "(\<lambda>a b. \<Prod>z\<in>A. f z (if z = x then a else b z)) = (\<lambda>a b. \<Prod>z\<in>A. f z (b z))"
    by (intro ext prod.cong) (use insert.hyps in auto)
  also have "(\<integral>\<^sup>+a. \<integral>\<^sup>+b. f x a * (\<Prod>z\<in>A. f z (b z)) \<partial>Pi_pmf A dflt p \<partial>p x) =
             (\<integral>\<^sup>+y. f x y \<partial>(p x)) * (\<integral>\<^sup>+y. (\<Prod>z\<in>A. f z (y z)) \<partial>(Pi_pmf A dflt p))"
    by (simp add: nn_integral_multc nn_integral_cmult)
  also have "(\<integral>\<^sup>+y. (\<Prod>z\<in>A. f z (y z)) \<partial>(Pi_pmf A dflt p)) = (\<Prod>x\<in>A. nn_integral (p x) (f x))"
    by (rule insert.IH)
  also have "(\<integral>\<^sup>+y. f x y \<partial>(p x)) * \<dots> = (\<Prod>x\<in>insert x A. nn_integral (p x) (f x))"
    using insert.hyps by simp
  finally show ?case .
qed auto

lemma integrable_prod_Pi_pmf:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field, second_countable_topology, banach}"
  assumes "finite A" and "\<And>x. x \<in> A \<Longrightarrow> integrable (measure_pmf (p x)) (f x)"
  shows   "integrable (measure_pmf (Pi_pmf A dflt p)) (\<lambda>h. \<Prod>x\<in>A. f x (h x))"
proof (intro integrableI_bounded)
  have "(\<integral>\<^sup>+ x. ennreal (norm (\<Prod>xa\<in>A. f xa (x xa))) \<partial>measure_pmf (Pi_pmf A dflt p)) =
        (\<integral>\<^sup>+ x. (\<Prod>y\<in>A. ennreal (norm (f y (x y)))) \<partial>measure_pmf (Pi_pmf A dflt p))"
    by (simp flip: prod_norm prod_ennreal)
  also have "\<dots> = (\<Prod>x\<in>A. \<integral>\<^sup>+ a. ennreal (norm (f x a)) \<partial>measure_pmf (p x))"
    by (intro nn_integral_prod_Pi_pmf) fact
  also have "(\<integral>\<^sup>+a. ennreal (norm (f i a)) \<partial>measure_pmf (p i)) \<noteq> \<top>" if i: "i \<in> A" for i
    using assms(2)[OF i] by (simp add: integrable_iff_bounded)
  hence "(\<Prod>x\<in>A. \<integral>\<^sup>+ a. ennreal (norm (f x a)) \<partial>measure_pmf (p x)) \<noteq> \<top>"
    by (subst ennreal_prod_eq_top) auto
  finally show "(\<integral>\<^sup>+ x. ennreal (norm (\<Prod>xa\<in>A. f xa (x xa))) \<partial>measure_pmf (Pi_pmf A dflt p)) < \<infinity>"
    by (simp add: top.not_eq_extremum)
qed auto

lemma expectation_prod_Pi_pmf:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> integrable (measure_pmf (p x)) (f x)"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> set_pmf (p x) \<Longrightarrow> f x y \<ge> 0"
  shows   "measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Prod>x\<in>A. f x (y x)) =
             (\<Prod>x\<in>A. measure_pmf.expectation (p x) (\<lambda>v. f x v))"
proof -
  have nonneg: "measure_pmf.expectation (p x) (f x) \<ge> 0" if "x \<in> A" for x
    using that by (intro Bochner_Integration.integral_nonneg_AE AE_pmfI assms)
  have nonneg': "0 \<le> measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Prod>x\<in>A. f x (y x))"
    by (intro Bochner_Integration.integral_nonneg_AE AE_pmfI assms prod_nonneg)
       (use assms in \<open>auto simp: set_Pi_pmf PiE_dflt_def\<close>)

  have "ennreal (measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Prod>x\<in>A. f x (y x))) =
          nn_integral (Pi_pmf A dflt p) (\<lambda>y. ennreal (\<Prod>x\<in>A. f x (y x)))" using assms
    by (intro nn_integral_eq_integral [symmetric] assms integrable_prod_Pi_pmf)
       (auto simp: AE_measure_pmf_iff set_Pi_pmf PiE_dflt_def prod_nonneg)
  also have "\<dots> = nn_integral (Pi_pmf A dflt p) (\<lambda>y. (\<Prod>x\<in>A. ennreal (f x (y x))))"
    by (intro nn_integral_cong_AE AE_pmfI prod_ennreal [symmetric])
       (use assms(1) in \<open>auto simp: set_Pi_pmf PiE_dflt_def intro!: assms(3)\<close>)
  also have "\<dots> = (\<Prod>x\<in>A. \<integral>\<^sup>+ a. ennreal (f x a) \<partial>measure_pmf (p x))"
    by (rule nn_integral_prod_Pi_pmf) fact+
  also have "\<dots> = (\<Prod>x\<in>A. ennreal (measure_pmf.expectation (p x) (f x)))"
    by (intro prod.cong nn_integral_eq_integral assms AE_pmfI) auto
  also have "\<dots> = ennreal (\<Prod>x\<in>A. measure_pmf.expectation (p x) (f x))"
    by (intro prod_ennreal nonneg)
  finally show ?thesis
    using nonneg nonneg' by (subst (asm) ennreal_inj) (auto intro!: prod_nonneg)
qed

lemma Pi_pmf_cong:
  assumes "A = A'" "dflt = dflt'" "\<And>x. x \<in> A \<Longrightarrow> f x = f' x"
  shows   "Pi_pmf A dflt f = Pi_pmf A' dflt' f'"
proof -
  have "(\<lambda>fa. if \<forall>x. x \<notin> A \<longrightarrow> fa x = dflt then \<Prod>x\<in>A. pmf (f x) (fa x) else 0) =
        (\<lambda>f. if \<forall>x. x \<notin> A' \<longrightarrow> f x = dflt' then \<Prod>x\<in>A'. pmf (f' x) (f x) else 0)"
    using assms by (intro ext) (auto intro!: prod.cong)
  thus ?thesis
    by (simp only: Pi_pmf_def)
qed

lemma Pi_pmf_return_pmf:
  assumes "finite A"
  shows   "Pi_pmf A dflt (\<lambda>x. return_pmf (f x)) = return_pmf (\<lambda>x. if x \<in> A then f x else dflt)"
  using assms by (intro pmf_eqI) (auto simp: pmf_Pi simp: indicator_def)

lemma integrable_map_pmf_eq [simp]:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable (map_pmf f p) g \<longleftrightarrow> integrable (measure_pmf p) (\<lambda>x. g (f x))"              
  by (subst map_pmf_rep_eq, subst integrable_distr_eq) auto

lemma integrable_map_pmf [intro]:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "integrable (measure_pmf p) (\<lambda>x. g (f x)) \<Longrightarrow> integrable (map_pmf f p) g"
  by (subst integrable_map_pmf_eq)

lemma
  fixes h :: "'a :: comm_monoid_add \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes fin: "finite I"
  assumes integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (measure_pmf (D i)) h"
  shows   integrable_sum_Pi_pmf: "integrable (Pi_pmf I dflt D) (\<lambda>g. \<Sum>i\<in>I. h (g i))"
    and   expectation_sum_Pi_pmf:
            "measure_pmf.expectation (Pi_pmf I dflt D) (\<lambda>g. \<Sum>i\<in>I. h (g i)) =
             (\<Sum>i\<in>I. measure_pmf.expectation (D i) h)"
proof -
  have integrable': "integrable (Pi_pmf I dflt D) (\<lambda>g. h (g i))" if i: "i \<in> I" for i
  proof -
    have "integrable (D i) h"
      using i by (rule assms)
    also have "D i = map_pmf (\<lambda>g. g i) (Pi_pmf I dflt D)"
      by (subst Pi_pmf_component) (use fin i in auto)
    finally show "integrable (measure_pmf (Pi_pmf I dflt D)) (\<lambda>x. h (x i))"
      by simp
  qed
  thus "integrable (Pi_pmf I dflt D) (\<lambda>g. \<Sum>i\<in>I. h (g i))"
    by (intro Bochner_Integration.integrable_sum)

  have "measure_pmf.expectation (Pi_pmf I dflt D) (\<lambda>x. \<Sum>i\<in>I. h (x i)) =
               (\<Sum>i\<in>I. measure_pmf.expectation (map_pmf (\<lambda>x. x i) (Pi_pmf I dflt D)) h)"
    using integrable' by (subst Bochner_Integration.integral_sum) auto
  also have "\<dots> = (\<Sum>i\<in>I. measure_pmf.expectation (D i) h)"
    by (intro sum.cong refl, subst Pi_pmf_component) (use fin in auto)
  finally show "measure_pmf.expectation (Pi_pmf I dflt D) (\<lambda>g. \<Sum>i\<in>I. h (g i)) =
                  (\<Sum>i\<in>I. measure_pmf.expectation (D i) h)" .
qed


subsection \<open>Corollaries of Markov's inequality\<close>

theorem markov_inequality_pmf:
  assumes "integrable (measure_pmf D) f"
     and  nonneg: "\<And>x. x \<in> set_pmf D \<Longrightarrow> f x \<ge> 0" and "a > 0"
  shows "measure_pmf.prob D {x. f x \<ge> a} \<le> measure_pmf.expectation D f / a"
proof -
  have nonneg': "measure_pmf.expectation D f / a \<ge> 0"
     by (intro divide_nonneg_pos integral_nonneg_AE nonneg \<open>a > 0\<close> AE_pmfI)
  have "ennreal (measure_pmf.prob D {x. f x \<ge> a}) = emeasure (measure_pmf D) {x. a \<le> f x}"
    unfolding measure_pmf.emeasure_eq_measure [symmetric] ..
  also have "\<dots>  = emeasure (measure_pmf D) {x\<in>space (measure_pmf D). a \<le> f x}"
    by simp
  also have "\<dots> = emeasure (measure_pmf D) ({x\<in>space (measure_pmf D). a \<le> f x} \<inter> set_pmf D)"
    by (subst emeasure_Int_set_pmf) (rule refl)
  also have "({x\<in>space (measure_pmf D). a \<le> f x} \<inter> set_pmf D) =
             ({x \<in> space (measure_pmf D). 1 \<le> ennreal (inverse a) * ennreal (f x)} \<inter> set_pmf D)"
    using \<open>a > 0\<close> nonneg by (auto simp: field_simps simp flip: ennreal_mult)
  also have "emeasure (measure_pmf D) \<dots> \<le>
             ennreal (inverse a) * (\<integral>\<^sup>+x\<in>set_pmf D. ennreal (f x) \<partial>measure_pmf D)" 
    by (rule nn_integral_Markov_inequality) auto
  also have "(\<integral>\<^sup>+x\<in>set_pmf D. ennreal (f x) \<partial>measure_pmf D) = (\<integral>\<^sup>+x. ennreal (f x) \<partial>measure_pmf D)"
    by (intro nn_integral_cong_AE AE_pmfI) auto
  also have "\<dots> = ennreal (measure_pmf.expectation D f)"
    by (intro nn_integral_eq_integral assms AE_pmfI)
  also have "ennreal (inverse a) * \<dots> = ennreal (inverse a * measure_pmf.expectation D f)"
    using assms by (intro ennreal_mult [symmetric] integral_nonneg_AE AE_pmfI) auto
  finally show ?thesis
    using nonneg' by (subst (asm) ennreal_le_iff) (auto simp: field_simps)
qed

theorem chebyshev_inequality_pmf:
  fixes D :: "real pmf"
  assumes "integrable (measure_pmf D) id"
  assumes "integrable (measure_pmf D) (\<lambda>x. x ^ 2)"
  defines "\<mu> \<equiv> measure_pmf.expectation D id"
  assumes "a > 0"
  shows "measure_pmf.prob D {x. a \<le> \<bar>x - \<mu>\<bar>} \<le> measure_pmf.variance D id / a\<^sup>2"
proof -
  define D' where "D' = map_pmf (\<lambda>x. (x - \<mu>)\<^sup>2) D"

  have "{x. \<bar>x - \<mu>\<bar> \<ge> a} = {x. (x - \<mu>)\<^sup>2 \<ge> a\<^sup>2}"
    using \<open>a > 0\<close> by (simp flip: abs_le_square_iff)
  hence "measure_pmf.prob D {x. \<bar>x - \<mu>\<bar> \<ge> a} = measure_pmf.prob D' {x. a\<^sup>2 \<le> x}"
    by (simp add: D'_def)
  also have "\<dots> \<le> measure_pmf.expectation D' (\<lambda>x. x) / a\<^sup>2"
  proof (intro markov_inequality_pmf)
    show "integrable (measure_pmf D') (\<lambda>x. x)" using assms
      by (auto simp: D'_def power2_eq_square algebra_simps id_def
               intro!: Bochner_Integration.integrable_add Bochner_Integration.integrable_diff)
  qed (use assms in \<open>auto simp: D'_def\<close>)
  also have "measure_pmf.expectation D' (\<lambda>x. x) = measure_pmf.variance D id"
    by (simp add: id_def D'_def \<mu>_def)
  finally show ?thesis .
qed

lemma chernoff_ineq_pmf_ge:
  assumes s: "s > 0"
  assumes integrable: "integrable (measure_pmf X) (\<lambda>x. exp (s * x))"
  shows   "measure_pmf.prob X {a..} \<le> exp (-s * a) * measure_pmf.expectation X (\<lambda>x. exp (s * x))"
proof -
  have "{a..} = {x. exp (s * x) \<ge> exp (s * a)}"
    using s by auto
  also have "measure_pmf.prob X \<dots> \<le> measure_pmf.expectation X (\<lambda>x. exp (s * x)) / exp (s * a)"
    by (intro markov_inequality_pmf integrable) auto
  finally show ?thesis 
    by (simp add: exp_minus field_simps)
qed

lemma chernoff_ineq_pmf_le:
  assumes s: "s > 0"
  assumes integrable: "integrable (measure_pmf X) (\<lambda>x. exp (-s * x))"
  shows   "measure_pmf.prob X {..a} \<le> exp (s * a) * measure_pmf.expectation X (\<lambda>x. exp (-s * x))"
proof -
  have "{..a} = {x. exp (-s * x) \<ge> exp (-s * a)}"
    using s by auto
  also have "measure_pmf.prob X \<dots> \<le> measure_pmf.expectation X (\<lambda>x. exp (-s * x)) / exp (-s * a)"
    by (intro markov_inequality_pmf integrable) auto
  finally show ?thesis 
    by (simp add: exp_minus field_simps)
qed


subsection \<open>Hoeffding's Lemma\<close>

lemma convex_on_exp: 
  fixes l :: real
  assumes "l > 0"
  shows   "convex_on UNIV (\<lambda>x. exp(l*x))"
  using assms
  by (intro convex_on_realI[where f' = "\<lambda>x. l * exp (l * x)"])
     (auto intro!: derivative_eq_intros)

lemma mult_const_minus_self_real_le:
  fixes x :: real
  shows "x * (c - x) \<le> c\<^sup>2 / 4"
proof -
  have "x * (c - x) = -(x - c / 2)\<^sup>2 + c\<^sup>2 / 4"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 0 + c\<^sup>2 / 4"
    by (intro add_mono) auto
  finally show ?thesis by simp
qed

lemma hoeffdings_lemma_pmf_aux:
  fixes a b l :: real
  assumes "l > 0" and ab: "a < 0" "b > 0"
  defines "p \<equiv> -a / (b - a)"
  defines "h \<equiv> l * (b - a)"
  defines "L \<equiv> (\<lambda>h. -h * p + ln (1 + p * (exp h - 1)))"
  shows   "L h \<le> h\<^sup>2 / 8"
proof -
  define L' where "L' = (\<lambda>h. -p + p * exp h / (1 + p * (exp h - 1)))"
  define L'' where "L'' = (\<lambda>h. -(p ^ 2) * exp h * exp h / (1 + p * (exp h - 1)) ^ 2 +
                              p * exp h / (1 + p * (exp h - 1)))"
  define Ls where "Ls = (\<lambda>n. [L, L', L''] ! n)"

  from ab have "p > 0"
    by (auto simp: p_def field_simps)
  from ab and \<open>l > 0\<close> have "h > 0"
    by (auto simp: h_def)
  have [simp]: "L 0 = 0" "L' 0 = 0"
    by (auto simp: L_def L'_def)

  have L': "(L has_real_derivative L' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have "1 + p * (exp x - 1) > 0"
      using \<open>p > 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    thus ?thesis
      unfolding L_def L'_def by (auto intro!: derivative_eq_intros)
  qed

  have L'': "(L' has_real_derivative L'' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have *: "1 + p * (exp x - 1) > 0"
      using \<open>p > 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      unfolding L'_def L''_def
      by (insert *, (rule derivative_eq_intros refl | simp)+) (auto simp: divide_simps; algebra)
  qed

  have diff: "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> (Ls m has_real_derivative Ls (Suc m) t) (at t)"
    using L' L'' by (auto simp: Ls_def nth_Cons split: nat.splits)
  from Taylor[of 2 Ls L 0 h 0 h, OF _ _ diff]
    obtain t where t: "t \<in> {0<..<h}" "L h = L'' t * h ^ 2 / 2"
      using \<open>h > 0\<close> ab by (auto simp: Ls_def lessThan_nat_numeral)
  define u where "u = p * exp t / (1 + p * (exp t - 1))"

  have "L'' t = u * (1 - u)"
    by (simp add: L''_def u_def divide_simps; algebra)
  also have "\<dots> \<le> 1 / 4"
    using mult_const_minus_self_real_le[of u 1] by simp
  finally have "L'' t \<le> 1 / 4" .

  note t(2)
  also have "L'' t * h\<^sup>2 / 2 \<le> (1 / 4) * h\<^sup>2 / 2"
    using \<open>L'' t \<le> 1 / 4\<close> by (intro mult_right_mono divide_right_mono) auto
  finally show "L h \<le> h\<^sup>2 / 8" by simp
qed

text \<open>
  We first show Hoeffding's lemma for distributions whose expectation is 0. The general
  case will easily follow from this later.
\<close>
lemma hoeffdings_lemma_pmf_0:
  fixes a b :: real
  assumes range: "set_pmf D \<subseteq> {a..b}" 
  and E0: "measure_pmf.expectation D id = 0" and "l > 0"
  shows   "measure_pmf.expectation D (\<lambda>x. exp (l*x)) \<le> exp (l\<^sup>2 * (b - a)\<^sup>2 / 8)"
proof (cases "D = return_pmf 0")
  case True
  thus ?thesis by auto
next
  case False
  define h where "h = (\<lambda>x. exp (l*x))"
  have [intro]: "continuous_on {a..b} h"
    by (auto simp: h_def intro!: continuous_intros)

  text \<open>
    We make our lives a bit easier by introducing a shorthand notation for the expectation locally.
  \<close>
  define Exp :: "(real \<Rightarrow> real) \<Rightarrow> real" (binder "E" 10)
    where [simp]: "Exp = measure_pmf.expectation D"

  have integrable [intro]: "integrable (measure_pmf D) f" if "continuous_on {a..b} f"
    for f :: "real \<Rightarrow> real"
  proof (rule integrableI_bounded)
    have "bounded (f ` {a..b})"
      by (intro compact_imp_bounded compact_continuous_image that) auto
    then obtain c' where c': "\<forall>x\<in>{a..b}. norm (f x) \<le> c'"
      by (auto simp: bounded_iff)
    define c where "c = max c' 0"
    have c: "\<forall>x\<in>{a..b}. norm (f x) \<le> c" "c \<ge> 0"
      using c' by (auto simp: c_def)
    have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf D) \<le> (\<integral>\<^sup>+ x. ennreal c \<partial>measure_pmf D)"
      using range c by (intro nn_integral_mono_AE) (auto simp: AE_measure_pmf_iff)
    also have "\<dots> < \<infinity>"
      using c by simp
    finally show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf D) < \<infinity>" .
  qed auto

  have "a < 0"
  proof (rule ccontr)
    assume a: "\<not>(a < 0)"
    hence "AE x in D. id x = 0"
      using E0 range a by (subst (asm) integral_nonneg_eq_0_iff_AE) (auto simp: AE_measure_pmf_iff)
    hence "set_pmf D \<subseteq> {0}"
      by (auto simp: AE_measure_pmf_iff)
    with \<open>D \<noteq> return_pmf 0\<close> show False
      using set_pmf_subset_singleton by metis
  qed

  have "b > 0"
  proof (rule ccontr)
    assume b: "\<not>(b > 0)"
    have "(E x. -x) = 0"
      using E0 by (simp add: id_def)
    hence "AE x in D. (\<lambda>x. -x) x = 0"
      using range b unfolding Exp_def
      by (subst (asm) integral_nonneg_eq_0_iff_AE) (auto simp: AE_measure_pmf_iff)
    hence "set_pmf D \<subseteq> {0}"
      by (auto simp: AE_measure_pmf_iff)
    with \<open>D \<noteq> return_pmf 0\<close> show False
      using set_pmf_subset_singleton by metis
  qed
    
  have "a < b"
    using \<open>a < 0\<close> \<open>b > 0\<close> by linarith

  define p where "p = -a / (b - a)"
  define L where "L = (\<lambda>t. -t * p + ln (1 - p + p * exp t))"
  define z where "z = l * (b - a)"

  have "(E x. h x) \<le> (E x. (b-x) / (b-a) * exp (l*a) + (x-a)/(b-a) * exp (l * b))"
    unfolding Exp_def
  proof (rule Bochner_Integration.integral_mono_AE, unfold AE_measure_pmf_iff, safe?)
    show "integrable (measure_pmf D) (\<lambda>x. (b - x) / (b - a) * exp (l * a) + (x - a) / (b - a) * exp (l * b))"
      using \<open>a < b\<close> by (intro integrable continuous_intros) auto
  next
    fix x assume "x \<in> set_pmf D"
    hence x: "x \<in> {a..b}"
      using range by auto
    define y where "y = (b-x) / (b-a)"
    have y: "y \<in> {0..1}"
      using x \<open>a < b\<close> by (auto simp: y_def)

    have conv: "convex_on UNIV (\<lambda>x. exp(l*x))"
      by (intro convex_on_exp) fact+

    have "exp (l * ((1 - y) *\<^sub>R b + y *\<^sub>R a)) \<le> (1 - y) * exp (l * b) + y * exp (l * a)"
      using y \<open>l > 0\<close> by (intro convex_onD[OF convex_on_exp]) auto
    also have "(1 - y) *\<^sub>R b + y *\<^sub>R a = x"
      using \<open>a < b\<close> by (simp add: y_def divide_simps) (simp add: algebra_simps)?
    also have "1 - y = (x - a) / (b - a)"
      using \<open>a < b\<close> by (simp add: field_simps y_def)
    finally show "h x \<le> (b-x)/(b-a) * exp (l*a) + (x-a)/(b-a) * exp (l*b)"
      by (simp add: h_def y_def)
  qed auto
  also have "\<dots> = (E x. (b + (-x)) / (b-a) * exp (l*a) + (x + (-a)) / (b-a) * exp (l*b))"
      by simp
  also have "\<dots> = (E x. (b + (-x)) / (b-a) * exp (l * a)) + (E x. (x + -a) / (b-a) * exp (l*b))"
    unfolding Exp_def using \<open>a < b\<close>
    by (intro Bochner_Integration.integral_add integrable continuous_intros) auto
  also have "(E x. (b + (-x)) / (b-a) * exp (l * a)) = b / (b - a) * h a"
    unfolding times_divide_eq_left times_divide_eq_right [symmetric] Exp_def h_def
    by (subst integral_mult_left_zero, subst Bochner_Integration.integral_add)
       (use E0 in \<open>auto simp: id_def\<close>)
  also have "(E x. (x + (-a)) / (b-a) * exp (l * b)) = -(a / (b - a)) * h b"
    unfolding times_divide_eq_left times_divide_eq_right [symmetric] Exp_def h_def
    by (subst integral_mult_left_zero, subst Bochner_Integration.integral_add)
       (use E0 in \<open>auto simp: id_def\<close>)
  also have "(b / (b - a)) * h a + (- (a / (b - a)) * h b) = exp (L z)"
  proof -
    have pos: "1 - p + p * exp z > 0"
    proof -
      have "exp z > 1" using \<open>l > 0\<close> and \<open>a < b\<close>
        by (subst one_less_exp_iff) (auto simp: z_def intro!: mult_pos_pos)
      hence "(exp z - 1) * p \<ge> 0"
        unfolding p_def using \<open>a < 0\<close> and \<open>a < b\<close>
        by (intro mult_nonneg_nonneg divide_nonneg_pos) auto
      thus ?thesis
        by (simp add: algebra_simps)
    qed

    have "exp (L z) = exp (-z * p) * (1 - p + p * exp z)"
      using pos by (simp add: exp_add L_def exp_diff exp_minus divide_simps)
    also have "\<dots> = (b / (b - a)) * h a - (a / (b - a)) * h b" using \<open>a < b\<close>
      by (simp add: p_def z_def h_def divide_simps) (simp add:  exp_diff algebra_simps)?
    finally show ?thesis by simp
  qed
  also have "L z \<le> z\<^sup>2 / 8"
    unfolding L_def z_def p_def
    by (intro order.trans[OF _ hoeffdings_lemma_pmf_aux])
       (use \<open>l > 0\<close> \<open>a < 0\<close> \<open>b > 0\<close> \<open>a < b\<close> in \<open>auto simp: divide_simps p_def\<close>,
        (simp add: algebra_simps)?)
  hence "exp (L z) \<le> exp (z\<^sup>2 / 8)"
    by simp
  finally show ?thesis
    by (simp add: h_def z_def power_mult_distrib)
qed

text \<open>
  For the general case, we simply shift the distribution such that its expectation is 0 and
  then apply the previous lemma.
\<close>
theorem hoeffdings_lemma_pmf:
  fixes a b :: real
  assumes range: "set_pmf D \<subseteq> {a..b}" and "l > 0"
  defines "\<mu> \<equiv> measure_pmf.expectation D id"
  shows   "measure_pmf.expectation D (\<lambda>x. exp (l * (x - \<mu>))) \<le> exp (l\<^sup>2 * (b - a)\<^sup>2 / 8)"
proof -
  define D' where "D' = map_pmf (\<lambda>t. t - measure_pmf.expectation D id) D"

  have integrable [intro]: "integrable (measure_pmf D) f" if "continuous_on {a..b} f"
    for f :: "real \<Rightarrow> real"
  proof (rule integrableI_bounded)
    have "bounded (f ` {a..b})"
      by (intro compact_imp_bounded compact_continuous_image that) auto
    then obtain c' where c': "\<forall>x\<in>{a..b}. norm (f x) \<le> c'"
      by (auto simp: bounded_iff)
    define c where "c = max c' 0"
    have c: "\<forall>x\<in>{a..b}. norm (f x) \<le> c" "c \<ge> 0"
      using c' by (auto simp: c_def)
    have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf D) \<le> (\<integral>\<^sup>+ x. ennreal c \<partial>measure_pmf D)"
      using range c by (intro nn_integral_mono_AE) (auto simp: AE_measure_pmf_iff)
    also have "\<dots> < \<infinity>"
      using c by simp
    finally show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf D) < \<infinity>" .
  qed auto

  have "measure_pmf.expectation D (\<lambda>x. exp (l * (x - \<mu>))) =
        measure_pmf.expectation D' (\<lambda>x. exp (l * x))"
    unfolding D'_def \<mu>_def by auto
  also have "measure_pmf.expectation D' id = 0"
    unfolding D'_def integral_map_pmf id_def by (subst Bochner_Integration.integral_diff) auto
  hence "measure_pmf.expectation D' (\<lambda>x. exp (l * x)) \<le> exp (l\<^sup>2 * ((b - \<mu>) - (a - \<mu>))\<^sup>2 / 8)"
    using assms by (intro hoeffdings_lemma_pmf_0) (auto simp: D'_def)
  also have "\<dots> = exp (l\<^sup>2 * (b - a)\<^sup>2 / 8)"
    by simp
  finally show ?thesis .
qed


subsection \<open>Hoeffding's Inequality for bounded distributions\<close>

text \<open>
  We now consider a sum of finitely many independent distributions $(D_i)_{i\in I}$,
  where the support of $D_i$ is contained in the interval $[a_i, b_i]$.
  
  Hoeffding's inequality then shows that this sum is concentrated around its mean, in the
  sense that the probability of deviating from the expected value falls of exponentially.
\<close>

locale hoeffding_ineq_pmf =
  fixes I :: "'a set" and dflt :: real and D :: "'a \<Rightarrow> real pmf"
  fixes a b :: "'a \<Rightarrow> real"
  fixes X :: "real pmf" and E_X :: real
  assumes fin: "finite I"
  assumes range: "\<And>i. i \<in> I \<Longrightarrow> set_pmf (D i) \<subseteq> {a i..b i}"
  defines "X \<equiv> map_pmf (\<lambda>f. sum f I) (Pi_pmf I dflt D)"
  defines "E_X \<equiv> measure_pmf.expectation X id"
begin

text \<open>
  The basic form of the inequality shows the following bound for the probability of the result
  being at least $y$ above the expected value:
\<close>
theorem hoeffding_ineq_ge:
  assumes y: "y > 0"
  shows   "measure_pmf.prob X {E_X + y ..} \<le> exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof (cases "\<exists>i\<in>I. a i < b i")
  case False
  have "D i = return_pmf (a i)" if i: "i \<in> I" for i
  proof -
    have "set_pmf (D i) \<subseteq> {a i..b i}"
      by (rule range) fact
    also have "\<dots> \<subseteq> {a i}"
      using False i by auto
    finally show ?thesis
      using set_pmf_subset_singleton by metis
  qed
  hence "Pi_pmf I dflt D = Pi_pmf I dflt (\<lambda>i. return_pmf (a i))"
    by (intro Pi_pmf_cong) auto
  thus ?thesis
    using fin y by (simp add: X_def E_X_def Pi_pmf_return_pmf indicator_def)
next
  case True
  define \<mu> where "\<mu> \<equiv> (\<lambda>i. measure_pmf.expectation (D i) id)"
  define S where "S = (\<Sum>i\<in>I. (b i - a i) ^ 2)"
  define s :: real where "s = 4 * y / S"
  define X' where "X' = map_pmf (\<lambda>t. t - E_X) X"

  have sum_pos: "S > 0"
  proof -
    from True obtain i where "i \<in> I" "a i < b i"
      by auto
    thus ?thesis
      using fin unfolding S_def by (intro sum_pos2[where i = i]) auto
  qed
  have s: "s > 0"
    unfolding s_def using y sum_pos by (intro divide_pos_pos mult_pos_pos) auto

  have integrable [intro]: "integrable (measure_pmf (D i)) f"
    if "continuous_on {a i..b i} f" and i: "i \<in> I" for f :: "real \<Rightarrow> real" and i
  proof (rule integrableI_bounded)
    have "bounded (f ` {a i..b i})"
      by (intro compact_imp_bounded compact_continuous_image that) auto
    then obtain c' where c': "\<forall>x\<in>{a i..b i}. norm (f x) \<le> c'"
      by (auto simp: bounded_iff)
    define c where "c = max c' 0"
    have c: "\<forall>x\<in>{a i..b i}. norm (f x) \<le> c" "c \<ge> 0"
      using c' by (auto simp: c_def)
    have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf (D i)) \<le> (\<integral>\<^sup>+ x. ennreal c \<partial>measure_pmf (D i))"
      using range[OF i] c i by (intro nn_integral_mono_AE) (auto simp: AE_measure_pmf_iff)
    also have "\<dots> < \<infinity>"
      using c by simp
    finally show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>measure_pmf (D i)) < \<infinity>" .
  qed auto

  have integrable': "integrable (measure_pmf X') (\<lambda>t. exp (s * t))"
    unfolding X'_def X_def integrable_map_pmf_eq using fin
    by (auto simp: ring_distribs exp_diff sum_distrib_left exp_sum
             intro!: integrable_divide integrable_prod_Pi_pmf integrable continuous_intros)

  have E_X_eq: "E_X = (\<Sum>i\<in>I. \<mu> i)"
    unfolding E_X_def X_def \<mu>_def integral_map_pmf id_def
    by (intro expectation_sum_Pi_pmf integrable fin continuous_intros)

  have "{E_X + y..} = {t. t \<ge> E_X + y}"
    by auto
  also have "measure_pmf.prob X {t. t \<ge> E_X + y} = measure_pmf.prob X' {t. t \<ge> y}"
    by (simp add: X'_def algebra_simps)
  also have "{t. t \<ge> y} = {y..}"
    by auto
  also have "measure_pmf.prob X' {y..} \<le> exp (-s * y) * measure_pmf.expectation X' (\<lambda>t. exp (s * t))"
    using integrable' s by (intro chernoff_ineq_pmf_ge) auto
  also have "measure_pmf.expectation X' (\<lambda>t. exp (s * t)) =
             measure_pmf.expectation (Pi_pmf I dflt D) (\<lambda>v. \<Prod>x\<in>I. exp (s * (v x - \<mu> x)))"
    by (simp add: X_def sum_distrib_left right_diff_distrib exp_sum X'_def E_X_eq fin
             flip: sum_subtractf)
  also have "\<dots> = (\<Prod>x\<in>I. measure_pmf.expectation (D x) (\<lambda>t. exp (s * (t - \<mu> x))))" using fin
    by (subst expectation_prod_Pi_pmf) (auto intro!: integrable continuous_intros)
  also have "exp (-s * y) * \<dots> \<le> exp (-s * y) * (\<Prod>i\<in>I. exp (s\<^sup>2 * (b i - a i)\<^sup>2 / 8))"
  proof (intro prod_mono conjI mult_left_mono)
    fix i assume i: "i \<in> I"
    show "measure_pmf.expectation (D i) (\<lambda>t. exp (s * (t - \<mu> i))) \<ge> 0"
      by (intro Bochner_Integration.integral_nonneg) auto
    show "measure_pmf.expectation (D i) (\<lambda>t. exp (s * (t - \<mu> i))) \<le> exp (s\<^sup>2 * (b i - a i)\<^sup>2 / 8)"
      unfolding \<mu>_def by (rule hoeffdings_lemma_pmf) (use s range[OF i] in auto)
  qed auto
  also have "(\<Prod>i\<in>I. exp (s\<^sup>2 * (b i - a i)\<^sup>2 / 8)) = exp (\<Sum>i\<in>I. s\<^sup>2 * (b i - a i)\<^sup>2 / 8)"
    using fin by (simp add: exp_sum)
  also have "exp (-s * y) * \<dots> = exp (S * s\<^sup>2 / 8 - s * y)"
    by (simp add: exp_diff sum_distrib_left sum_distrib_right sum_divide_distrib
                  exp_minus field_simps S_def)
  also have "S * s\<^sup>2 / 8 - s * y = -2 * y\<^sup>2 / S"
    using sum_pos by (simp add: s_def field_simps power2_eq_square)
  finally show ?thesis unfolding S_def .
qed

text \<open>
  The following symmetric bound follows easily:
\<close>
corollary hoeffding_ineq_le:
  assumes y: "y > 0"
  shows   "measure_pmf.prob X {..E_X - y} \<le> exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  define X' where "X' = map_pmf (\<lambda>x. -x) X"
  define E_X' where "E_X' = measure_pmf.expectation X' id"
  have "E_X' = -E_X"
    by (simp add: E_X'_def E_X_def X'_def id_def)

  have X'_eq: "X' = map_pmf (\<lambda>f. sum f I) (Pi_pmf I (-dflt) (map_pmf (\<lambda>x. -x) \<circ> D))"
  proof -
    have "X' = map_pmf (\<lambda>x. sum x I) (map_pmf ((\<circ>) (\<lambda>x. -x)) (Pi_pmf I dflt D))"
      by (simp add: X'_def X_def pmf.map_comp o_def sum_negf)
    also have "map_pmf ((\<circ>) (\<lambda>x. -x)) (Pi_pmf I dflt D) =
               Pi_pmf I (-dflt) (\<lambda>x. map_pmf (\<lambda>x. -x) (D x))"
      using fin by (intro Pi_pmf_map [symmetric]) auto
    finally show ?thesis by (simp add: o_def)
  qed

  interpret flip: hoeffding_ineq_pmf I "-dflt"  "map_pmf (\<lambda>x. -x) \<circ> D" "\<lambda>i. -b i" "\<lambda>i. -a i" X' E_X'
    using fin range by unfold_locales (force simp: X'_eq E_X'_def)+

  have "(\<lambda>x. -x) -` {E_X' + y..} = {.. E_X - y}"
    by (auto simp: \<open>E_X' = -E_X\<close>)
  hence "measure_pmf.prob X {.. E_X - y} = measure_pmf.prob X' {E_X' + y ..}"
    by (simp add: X'_def)
  also have "\<dots> \<le> exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. ((- a i) - (- b i))\<^sup>2))"
    using y by (rule flip.hoeffding_ineq_ge)
  finally show ?thesis by simp
qed

text \<open>
  Combining the previous two bounds, we get the following bound:
\<close>
corollary hoeffding_ineq_abs_ge:
  assumes y: "y > 0"
  shows   "measure_pmf.prob X {t. \<bar>t - E_X\<bar> \<ge> y} \<le> 2 * exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  have "{t. \<bar>t - E_X\<bar> \<ge> y} = {.. E_X - y} \<union> {E_X + y ..}"
    by auto
  also have "measure_pmf.prob X \<dots> \<le>
               measure_pmf.prob X {.. E_X - y} + measure_pmf.prob X {E_X + y ..}"
    by (intro measure_Un_le) auto
  also have "\<dots> \<le> exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2)) + exp (-2 * y\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
    by (intro add_mono hoeffding_ineq_ge hoeffding_ineq_le y)
  finally show ?thesis by simp
qed

end


subsection \<open>Hoeffding's Inequality for the Binomial distribution\<close>

text \<open>
  We can now apply Hoeffding's inequality to the Binomial distribution, which can be seen
  as the sum of \<open>n\<close> i.i.d. coin flips (the support of each of which is contained in $[0,1]$).
\<close>

context
  fixes n::nat and p :: real and X :: "nat pmf" and Coin :: "real pmf"
  assumes p: "p \<in> {0..1}"
  defines "Coin \<equiv> map_pmf (\<lambda>b. if b then 1 else 0) (bernoulli_pmf p)"
  defines "X \<equiv> binomial_pmf n p"
begin

interpretation binomial:
  hoeffding_ineq_pmf "{..<n}" 0 "\<lambda>_. Coin" "\<lambda>_. 0" "\<lambda>_. 1" "map_pmf real X" "p * real n"
proof unfold_locales
  show "map_pmf real X \<equiv> map_pmf (\<lambda>v. sum v {..<n}) (Pi_pmf {..<n} 0 (\<lambda>_. Coin))"
  proof -
    have "map_pmf (\<lambda>v. sum v {..<n}) (Pi_pmf {..<n} 0 (\<lambda>_. Coin)) =
          map_pmf (\<lambda>x. \<Sum>i<n. if x i then 1 else 0) (Pi_pmf {..<n} False (\<lambda>_. bernoulli_pmf p))"
      unfolding Coin_def by (subst Pi_pmf_map[where dflt = False]) (simp_all add: pmf.map_comp o_def)
    also have "(\<lambda>x. \<Sum>i<n. if x i then 1 else 0 :: real) = (\<lambda>x. \<Sum>i \<in> {i\<in>{..<n}. x i}. 1)"
      by (intro ext sum.mono_neutral_cong_right) auto
    also have "\<dots> = (\<lambda>x. real (card {i\<in>{..<n}. x i}))"
      by simp
    also have "map_pmf (\<lambda>x. real (card {i \<in> {..<n}. x i}))
                (Pi_pmf {..<n} False (\<lambda>_. bernoulli_pmf p)) = map_pmf real X"
      unfolding X_def using p
      by (subst binomial_pmf_altdef'[where A = "{..<n}" and dflt = False])
         (simp_all add: pmf.map_comp o_def)
    finally show "map_pmf real X \<equiv> map_pmf (\<lambda>v. sum v {..<n}) (Pi_pmf {..<n} 0 (\<lambda>_. Coin))"
      by (simp only: )
  qed
qed (use p in \<open>auto simp: X_def Coin_def mult_ac\<close>)

corollary hoeffding_binomial_ge:
  fixes y :: real
  assumes y: "y > 0"
  shows   "measure_pmf.prob (binomial_pmf n p) {k. k \<ge> p * n + y} \<le> exp (-(2 * y\<^sup>2 / n))"
proof -
  have "{k. k \<ge> p * n + y} = real -` {p * n + y..}"
    by auto
  thus ?thesis using binomial.hoeffding_ineq_ge[OF y]
    by (simp add: X_def)
qed

corollary hoeffding_binomial_le:
  fixes y :: real
  assumes y: "y > 0"
  shows   "measure_pmf.prob (binomial_pmf n p) {k. k \<le> p * n - y} \<le> exp (-(2 * y\<^sup>2 / n))"
proof -
  have "{k. k \<le> p * n - y} = real -` {..p * n - y}"
    by auto
  thus ?thesis using binomial.hoeffding_ineq_le[OF y]
    by (simp add: X_def)
qed

corollary hoeffding_binomial_abs_ge:
  fixes y :: real
  assumes y: "y > 0"
  shows   "measure_pmf.prob (binomial_pmf n p) {k. \<bar>k - p * n\<bar> \<ge> y} \<le> 2 * exp (-(2 * y\<^sup>2 / n))"
  using binomial.hoeffding_ineq_abs_ge[OF y] by (simp add: X_def)

end

end