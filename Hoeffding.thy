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

(* TODO: a lot of this stuff should go into the library. *)

lemma borel_measurable_power_ennreal [measurable (raw)]:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
  by (induction n) (use f in auto)

lemma add_top_right_ennreal [simp]: "x + \<top> = (\<top> :: ennreal)"
  by (cases x) auto

lemma add_top_left_ennreal [simp]: "\<top> + x = (\<top> :: ennreal)"
  by (cases x) auto

lemma ennreal_top_mult_left [simp]: "x \<noteq> 0 \<Longrightarrow> x * \<top> = (\<top> :: ennreal)"
  by (subst ennreal_mult_eq_top_iff) auto

lemma ennreal_top_mult_right [simp]: "x \<noteq> 0 \<Longrightarrow> \<top> * x = (\<top> :: ennreal)"
  by (subst ennreal_mult_eq_top_iff) auto

lemma power_top_ennreal [simp]: "n > 0 \<Longrightarrow> \<top> ^ n = (\<top> :: ennreal)"
  by (induction n) auto

lemma power_eq_top_ennreal_iff: "x ^ n = \<top> \<longleftrightarrow> x = (\<top> :: ennreal) \<and> n > 0"
  by (induction n) (auto simp: ennreal_mult_eq_top_iff)

lemma power_divide_distrib_ennreal [algebra_simps]:
  "(x / y) ^ n = x ^ n / (y ^ n :: ennreal)"
  by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_power)

lemma ennreal_mult_le_mult_iff: "c \<noteq> 0 \<Longrightarrow> c \<noteq> \<top> \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> a \<le> (b :: ennreal)"
  including ennreal.lifting
  by (transfer, subst ereal_mult_le_mult_iff) (auto simp: top_ereal_def)

lemma power_mono_ennreal: "x \<le> y \<Longrightarrow> x ^ n \<le> (y ^ n :: ennreal)"
  by (induction n) (auto intro!: mult_mono)

lemma sum_of_squares_ge_ennreal:
  fixes a b :: ennreal
  shows "2 * a * b \<le> a\<^sup>2 + b\<^sup>2"
proof (cases a; cases b)
  fix x y
  assume xy: "x \<ge> 0" "y \<ge> 0" and [simp]: "a = ennreal x" "b = ennreal y"
  have "0 \<le> (x - y)\<^sup>2"
    by simp
  also have "\<dots> = x\<^sup>2 + y\<^sup>2 - 2 * x * y"
    by (simp add: algebra_simps power2_eq_square)
  finally have "2 * x * y \<le> x\<^sup>2 + y\<^sup>2"
    by simp
  hence "ennreal (2 * x * y) \<le> ennreal (x\<^sup>2 + y\<^sup>2)"
    by (intro ennreal_leI)
  thus ?thesis using xy
    by (simp add: ennreal_mult ennreal_power)
qed auto

lemma Cauchy_Schwarz_nn_integral:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f x * g x \<partial>M)\<^sup>2 \<le> (\<integral>\<^sup>+x. f x ^ 2 \<partial>M) * (\<integral>\<^sup>+x. g x ^ 2 \<partial>M)"
proof (cases "(\<integral>\<^sup>+x. f x * g x \<partial>M) = 0")
  case False
  define F where "F = nn_integral M (\<lambda>x. f x ^ 2)"
  define G where "G = nn_integral M (\<lambda>x. g x ^ 2)"
  from False have "\<not>(AE x in M. f x = 0 \<or> g x = 0)"
    by (auto simp: nn_integral_0_iff_AE)
  hence "\<not>(AE x in M. f x = 0)" and "\<not>(AE x in M. g x = 0)"
    by (auto intro: AE_disjI1 AE_disjI2)
  hence nz: "F \<noteq> 0" "G \<noteq> 0"
    by (auto simp: nn_integral_0_iff_AE F_def G_def)

  show ?thesis
  proof (cases "F = \<infinity> \<or> G = \<infinity>")
    case True
    thus ?thesis using nz
      by (auto simp: F_def G_def)
  next
    case False
    define F' where "F' = ennreal (sqrt (enn2real F))"
    define G' where "G' = ennreal (sqrt (enn2real G))"
    from False have fin: "F < \<top>" "G < \<top>"
      by (simp_all add: top.not_eq_extremum)
    have F'_sqr: "F'\<^sup>2 = F"
      using False by (cases F) (auto simp: F'_def ennreal_power)
    have G'_sqr: "G'\<^sup>2 = G"
      using False by (cases G) (auto simp: G'_def ennreal_power)
    have nz': "F' \<noteq> 0" "G' \<noteq> 0" and fin': "F' \<noteq> \<infinity>" "G' \<noteq> \<infinity>"
      using F'_sqr G'_sqr nz fin by auto
    from fin' have fin'': "F' < \<top>" "G' < \<top>"
      by (auto simp: top.not_eq_extremum)

    have "2 * (F' / F') * (G' / G') * (\<integral>\<^sup>+x. f x * g x \<partial>M) =
          F' * G' * (\<integral>\<^sup>+x. 2 * (f x / F') * (g x / G') \<partial>M)"
      using nz' fin''
      by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_mult flip: nn_integral_cmult)
    also have "F'/ F' = 1"
      using nz' fin'' by simp
    also have "G'/ G' = 1"
      using nz' fin'' by simp
    also have "2 * 1 * 1 = (2 :: ennreal)" by simp
    also have "F' * G' * (\<integral>\<^sup>+ x. 2 * (f x / F') * (g x / G') \<partial>M) \<le>
               F' * G' * (\<integral>\<^sup>+x. (f x / F')\<^sup>2 + (g x / G')\<^sup>2 \<partial>M)"
      by (intro mult_left_mono nn_integral_mono sum_of_squares_ge_ennreal) auto
    also have "\<dots> = F' * G' * (F / F'\<^sup>2 + G / G'\<^sup>2)" using nz
      by (auto simp: nn_integral_add algebra_simps nn_integral_divide F_def G_def)
    also have "F / F'\<^sup>2 = 1"
      using nz F'_sqr fin by simp
    also have "G / G'\<^sup>2 = 1"
      using nz G'_sqr fin by simp
    also have "F' * G' * (1 + 1) = 2 * (F' * G')"
      by (simp add: mult_ac)
    finally have "(\<integral>\<^sup>+x. f x * g x \<partial>M) \<le> F' * G'"
      by (subst (asm) ennreal_mult_le_mult_iff) auto
    hence "(\<integral>\<^sup>+x. f x * g x \<partial>M)\<^sup>2 \<le> (F' * G')\<^sup>2"
      by (intro power_mono_ennreal)
    also have "\<dots> = F * G"
      by (simp add: algebra_simps F'_sqr G'_sqr)
    finally show ?thesis
      by (simp add: F_def G_def)
  qed
qed auto

(* TODO: remove superfluous assumptions from e.g. CLT *)
lemma (in prob_space) square_integrable_imp_integrable:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, real_normed_div_algebra}"
  assumes [measurable]: "f \<in> borel_measurable M"
  assumes "integrable M (\<lambda>x. f x ^ 2)"
  shows   "integrable M f"
proof -
  have "nn_integral M (\<lambda>x. norm (f x)) ^ 2 \<le> nn_integral M (\<lambda>x. norm (f x) ^ 2)"
    using Cauchy_Schwarz_nn_integral[of "\<lambda>x. norm (f x)" M "\<lambda>_. 1"]
    by (simp add: emeasure_space_1 ennreal_power)
  also have "\<dots> < \<infinity>"
    using assms(2) by (subst (asm) integrable_iff_bounded) (auto simp: norm_power)
  finally have "nn_integral M (\<lambda>x. norm (f x)) < \<infinity>"
    by (simp add: power_less_top_ennreal)
  thus ?thesis
    by (simp add: integrable_iff_bounded)
qed
find_theorems name:cantelli

lemma product_prob_spaceI:
  assumes "\<And>i. prob_space (M i)"
  shows   "product_prob_space M"
  unfolding product_prob_space_def product_prob_space_axioms_def product_sigma_finite_def
proof safe
  fix i
  interpret prob_space "M i"
    by (rule assms)
  show "sigma_finite_measure (M i)" "prob_space (M i)"
    by unfold_locales
qed

lemma finite_set_pmf_binomial_pmf [intro]: "p \<in> {0..1} \<Longrightarrow> finite (set_pmf (binomial_pmf n p))"
  by (subst set_pmf_binomial_eq) auto

lemma add_divide_distrib_ennreal: "(a + b) / c = a / c + b / (c :: ennreal)"
  by (simp add: divide_ennreal_def ring_distribs)

lemma prod_mono_ennreal:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> (g x :: ennreal)"
  shows   "prod f A \<le> prod g A"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: mult_mono)

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

lemma (in prob_space) indep_vars_iff_distr_eq_PiM':
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "I \<noteq> {}"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
           distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
proof -
  from assms obtain j where j: "j \<in> I"
    by auto
  define N' where "N' = (\<lambda>i. if i \<in> I then M' i else M' j)"
  define Y where "Y = (\<lambda>i. if i \<in> I then X i else X j)"
  have rv: "random_variable (N' i) (Y i)" for i
    using j by (auto simp: N'_def Y_def intro: assms)

  have "indep_vars M' X I = indep_vars N' Y I"
    by (intro indep_vars_cong) (auto simp: N'_def Y_def)
  also have "\<dots> \<longleftrightarrow> distr M (\<Pi>\<^sub>M i\<in>I. N' i) (\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i))"
    by (intro indep_vars_iff_distr_eq_PiM rv assms)
  also have "(\<Pi>\<^sub>M i\<in>I. N' i) = (\<Pi>\<^sub>M i\<in>I. M' i)"
    by (intro PiM_cong) (simp_all add: N'_def)
  also have "(\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<lambda>x. \<lambda>i\<in>I. X i x)"
    by (simp_all add: Y_def fun_eq_iff)
  also have "(\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i)) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
    by (intro PiM_cong distr_cong) (simp_all add: N'_def Y_def)
  finally show ?thesis .
qed

lemma indep_vars_Pi_pmf:
  assumes fin: "finite I"
  shows   "prob_space.indep_vars (measure_pmf (Pi_pmf I dflt p))
             (\<lambda>_. count_space UNIV) (\<lambda>x f. f x) I"
proof (cases "I = {}")
  case True
  show ?thesis 
    by (subst prob_space.indep_vars_def [OF measure_pmf.prob_space_axioms],
        subst prob_space.indep_sets_def [OF measure_pmf.prob_space_axioms]) (simp_all add: True)
next
  case [simp]: False
  show ?thesis
  proof (subst prob_space.indep_vars_iff_distr_eq_PiM')
    show "distr (measure_pmf (Pi_pmf I dflt p)) (Pi\<^sub>M I (\<lambda>i. count_space UNIV)) (\<lambda>x. restrict x I) =
          Pi\<^sub>M I (\<lambda>i. distr (measure_pmf (Pi_pmf I dflt p)) (count_space UNIV) (\<lambda>f. f i))"
    proof (rule product_sigma_finite.PiM_eqI, goal_cases)
      case 1
      interpret product_prob_space "\<lambda>i. distr (measure_pmf (Pi_pmf I dflt p)) (count_space UNIV) (\<lambda>f. f i)"
        by (intro product_prob_spaceI prob_space.prob_space_distr measure_pmf.prob_space_axioms)
           simp_all
      show ?case by unfold_locales
    next
      case 3
      have "sets (Pi\<^sub>M I (\<lambda>i. distr (measure_pmf (Pi_pmf I dflt p)) (count_space UNIV) (\<lambda>f. f i))) =
            sets (Pi\<^sub>M I (\<lambda>_. count_space UNIV))"
        by (intro sets_PiM_cong) simp_all
      thus ?case by simp
    next
      case (4 A)
      have "Pi\<^sub>E I A \<in> sets (Pi\<^sub>M I (\<lambda>i. count_space UNIV))"
        using 4 by (intro sets_PiM_I_finite fin) auto
      hence "emeasure (distr (measure_pmf (Pi_pmf I dflt p)) (Pi\<^sub>M I (\<lambda>i. count_space UNIV))
              (\<lambda>x. restrict x I)) (Pi\<^sub>E I A) =
             emeasure (measure_pmf (Pi_pmf I dflt p)) ((\<lambda>x. restrict x I) -` Pi\<^sub>E I A)"
        using 4 by (subst emeasure_distr) (auto simp: space_PiM)
      also have "\<dots> = emeasure (measure_pmf (Pi_pmf I dflt p)) (PiE_dflt I dflt A)"
        by (intro emeasure_eq_AE AE_pmfI) (auto simp: PiE_dflt_def set_Pi_pmf fin)
      also have "\<dots> = (\<Prod>i\<in>I. emeasure (measure_pmf (p i)) (A i))"
        by (simp add: measure_pmf.emeasure_eq_measure measure_Pi_pmf_PiE_dflt fin prod_ennreal)
      also have "\<dots> = (\<Prod>i\<in>I. emeasure (measure_pmf (map_pmf (\<lambda>f. f i) (Pi_pmf I dflt p))) (A i))"
        by (intro prod.cong refl, subst Pi_pmf_component) (auto simp: fin)
      finally show ?case
        by (simp add: map_pmf_rep_eq)
    qed fact+
  qed (simp_all add: measure_pmf.prob_space_axioms)
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

lemma (in prob_space) AE_eq_constD:
  assumes "AE x in M. x = y"
  shows   "M = return M y" "y \<in> space M"
proof -
  have "AE x in M. x \<in> space M"
    by auto
  with assms have "AE x in M. y \<in> space M"
    by eventually_elim auto
  thus "y \<in> space M"
    by simp

  show "M = return M y"
  proof (rule measure_eqI)
    fix X assume X: "X \<in> sets M"
    have "AE x in M. (x \<in> X) = (x \<in> (if y \<in> X then space M else {}))"
      using assms by eventually_elim (use X \<open>y \<in> space M\<close> in auto)
    hence "emeasure M X = emeasure M (if y \<in> X then space M else {})"
      using X by (intro emeasure_eq_AE) auto
    also have "\<dots> = emeasure (return M y) X"
      using X by (auto simp: emeasure_space_1)
    finally show "emeasure M X = \<dots>" .
  qed auto
qed

lemma PiM_return:
  assumes "finite I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> {a i} \<in> sets (M i)"
  shows "PiM I (\<lambda>i. return (M i) (a i)) = return (PiM I M) (restrict a I)"
proof -
  have [simp]: "a i \<in> space (M i)" if "i \<in> I" for i
    using assms(2)[OF that] by (meson insert_subset sets.sets_into_space)
  interpret prob_space "PiM I (\<lambda>i. return (M i) (a i))"
    by (intro prob_space_PiM prob_space_return) auto
  have "AE x in PiM I (\<lambda>i. return (M i) (a i)). \<forall>i\<in>I. x i = restrict a I i"
    by (intro eventually_ball_finite ballI AE_PiM_component prob_space_return assms)
       (auto simp: AE_return)
  moreover have "AE x in PiM I (\<lambda>i. return (M i) (a i)). x \<in> space (PiM I (\<lambda>i. return (M i) (a i)))"
    by simp
  ultimately have "AE x in PiM I (\<lambda>i. return (M i) (a i)). x = restrict a I"
    by eventually_elim (auto simp: fun_eq_iff space_PiM)
  hence "Pi\<^sub>M I (\<lambda>i. return (M i) (a i)) = return (Pi\<^sub>M I (\<lambda>i. return (M i) (a i))) (restrict a I)"
    by (rule AE_eq_constD)
  also have "\<dots> = return (PiM I M) (restrict a I)"
    by (intro return_cong sets_PiM_cong) auto
  finally show ?thesis .
qed

lemma distr_PiM_finite_prob_space:
  assumes fin: "finite I"
  assumes "product_prob_space M"
  assumes "product_prob_space M'"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable (M i) (M' i)"
  shows   "distr (PiM I M) (PiM I M') (compose I f) = PiM I (\<lambda>i. distr (M i) (M' i) f)"
proof -
  interpret M: product_prob_space M by fact
  interpret M': product_prob_space M' by fact
  define N where "N = (\<lambda>i. if i \<in> I then distr (M i) (M' i) f else M' i)"
  have [intro]: "prob_space (N i)" for i
    by (auto simp: N_def intro!: M.M.prob_space_distr M'.prob_space)

  interpret N: product_prob_space N
    by (intro product_prob_spaceI) (auto simp: N_def M'.prob_space intro: M.M.prob_space_distr)

  have "distr (PiM I M) (PiM I M') (compose I f) = PiM I N"
  proof (rule N.PiM_eqI)
    have N_events_eq: "N.P.events = sets (Pi\<^sub>M I M')"
      unfolding N_def by (intro sets_PiM_cong) auto
    also have "\<dots> = sets (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f))"
      by simp
    finally show "sets (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) = N.P.events"  ..

    fix A assume A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> N.M.events i"
    have "emeasure (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) (Pi\<^sub>E I A) =
          emeasure (Pi\<^sub>M I M) (compose I f -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I M))"
    proof (intro emeasure_distr)
      show "M.P.random_variable (Pi\<^sub>M I M') (compose I f)"
        unfolding compose_def by measurable
      show "Pi\<^sub>E I A \<in> M'.P.events"
        unfolding N_events_eq [symmetric] by (intro sets_PiM_I_finite fin A)
    qed
    also have "compose I f -` Pi\<^sub>E I A \<inter> space (Pi\<^sub>M I M) = Pi\<^sub>E I (\<lambda>i. f -` A i \<inter> space (M i))"
      using A by (auto simp: space_PiM PiE_def Pi_def extensional_def N_def compose_def)
    also have "emeasure (Pi\<^sub>M I M) (Pi\<^sub>E I (\<lambda>i. f -` A i \<inter> space (M i))) =
          (\<Prod>i\<in>I. emeasure (M i) (f -` A i \<inter> space (M i)))"
      using A by (intro M.emeasure_PiM fin) (auto simp: N_def)
    also have "\<dots> = (\<Prod>i\<in>I. emeasure (distr (M i) (M' i) f) (A i))"
      using A by (intro prod.cong emeasure_distr [symmetric]) (auto simp: N_def)
    also have "\<dots> = (\<Prod>i\<in>I. emeasure (N i) (A i))"
      unfolding N_def by (intro prod.cong) (auto simp: N_def)
    finally show "emeasure (distr (Pi\<^sub>M I M) (Pi\<^sub>M I M') (compose I f)) (Pi\<^sub>E I A) = \<dots>" .
  qed fact+
  also have "PiM I N = PiM I (\<lambda>i. distr (M i) (M' i) f)"
    by (intro PiM_cong) (auto simp: N_def)
  finally show ?thesis .
qed

lemma distr_PiM_finite_prob_space':
  assumes fin: "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M' i)"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable (M i) (M' i)"
  shows   "distr (PiM I M) (PiM I M') (compose I f) = PiM I (\<lambda>i. distr (M i) (M' i) f)"
proof -
  define N where "N = (\<lambda>i. if i \<in> I then M i else return (count_space UNIV) undefined)"
  define N' where "N' = (\<lambda>i. if i \<in> I then M' i else return (count_space UNIV) undefined)"
  have [simp]: "PiM I N = PiM I M" "PiM I N' = PiM I M'"
    by (intro PiM_cong; simp add: N_def N'_def)+

  have "distr (PiM I N) (PiM I N') (compose I f) = PiM I (\<lambda>i. distr (N i) (N' i) f)"
  proof (rule distr_PiM_finite_prob_space)
    show "product_prob_space N"
      by (rule product_prob_spaceI) (auto simp: N_def intro!: prob_space_return assms)
    show "product_prob_space N'"
      by (rule product_prob_spaceI) (auto simp: N'_def intro!: prob_space_return assms)
  qed (auto simp: N_def N'_def fin)
  also have "Pi\<^sub>M I (\<lambda>i. distr (N i) (N' i) f) = Pi\<^sub>M I (\<lambda>i. distr (M i) (M' i) f)"
    by (intro PiM_cong) (simp_all add: N_def N'_def)
  finally show ?thesis by simp
qed

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


subsection \<open>Consequences of Markov's inequality: Chernoff and Chebyshev bounds\<close>

theorem integral_Markov_inequality':
  assumes [measurable]: "integrable M u" and "AE x in M. 0 \<le> u x" "0 < (c::real)"
  shows "measure M {x\<in>space M. u x \<ge> c} \<le> (\<integral>x. u x \<partial>M) / c"
proof -
  have le: "emeasure M {x\<in>space M. u x \<ge> c} \<le> ennreal ((1/c) * (\<integral>x. u x \<partial>M))"
    by (rule integral_Markov_inequality) (use assms in auto)
  also have "\<dots> < \<top>"
    by auto
  finally have "ennreal (measure M {x\<in>space M. u x \<ge> c}) = emeasure M {x\<in>space M. u x \<ge> c}"
    by (intro emeasure_eq_ennreal_measure [symmetric]) auto
  also note le
  finally show ?thesis
    by (subst (asm) ennreal_le_iff)
       (auto intro!: divide_nonneg_pos Bochner_Integration.integral_nonneg_AE assms)
qed

theorem (in prob_space) Chebyshev_inequality:
  assumes [measurable]: "random_variable borel f"
  assumes "integrable M (\<lambda>x. f x ^ 2)"
  defines "\<mu> \<equiv> expectation f"
  assumes "a > 0"
  shows "prob {x\<in>space M. a \<le> \<bar>f x - \<mu>\<bar>} \<le> variance f / a\<^sup>2"
proof -
  have integrable: "integrable M f"
    using assms by (blast dest: square_integrable_imp_integrable)
  have "{x\<in>space M. \<bar>f x - \<mu>\<bar> \<ge> a} = {x\<in>space M. (f x - \<mu>)\<^sup>2 \<ge> a\<^sup>2}"
    using \<open>a > 0\<close> by (simp flip: abs_le_square_iff)
  hence "prob {x\<in>space M. \<bar>f x - \<mu>\<bar> \<ge> a} = prob {x\<in>space M. (f x - \<mu>)\<^sup>2 \<ge> a\<^sup>2}"
    by simp
  also have "\<dots> \<le> expectation (\<lambda>x. (f x - \<mu>)\<^sup>2) / a\<^sup>2"
  proof (intro integral_Markov_inequality')
    show "integrable M (\<lambda>x. (f x - \<mu>)\<^sup>2)"
      using assms integrable unfolding power2_eq_square ring_distribs
      by (intro Bochner_Integration.integrable_diff) auto
  qed (use \<open>a > 0\<close> in auto)
  also have "expectation (\<lambda>x. (f x - \<mu>)\<^sup>2) = variance f"
    by (simp add: \<mu>_def)
  finally show ?thesis .
qed

lemma (in prob_space) Chernoff_ineq_nn_integral_ge:
  assumes s: "s > 0" and [measurable]: "A \<in> events"
  assumes [measurable]: "random_variable borel f"
  shows   "emeasure M ({x\<in>space M. f x \<ge> a} \<inter> A) \<le>
           ennreal (exp (-s * a)) * set_nn_integral M A (\<lambda>x. ennreal (exp (s * f x)))"
proof -
  have "{x\<in>space M. f x \<ge> a} \<inter> A = {x\<in>space M. ennreal (exp (-s * a)) * ennreal (exp (s * f x)) \<ge> 1} \<inter> A"
    using s by (auto simp: exp_minus field_simps simp flip: ennreal_mult)
  also have "emeasure M \<dots> \<le> ennreal (exp (- s * a)) * (\<integral>\<^sup>+x\<in>A. ennreal (exp (s * f x))\<partial>M)"
    by (rule order.trans[OF nn_integral_Markov_inequality]) auto
  finally show ?thesis .
qed

lemma (in prob_space) Chernoff_ineq_nn_integral_le:
  assumes s: "s > 0" and [measurable]: "A \<in> events"
  assumes [measurable]: "random_variable borel f"
  shows   "emeasure M ({x\<in>space M. f x \<le> a} \<inter> A) \<le>
           ennreal (exp (s * a)) * set_nn_integral M A (\<lambda>x. ennreal (exp (-s * f x)))"
  using Chernoff_ineq_nn_integral_ge[of s A "\<lambda>x. -f x" "-a"] assms by simp

lemma (in prob_space) Chernoff_ineq_ge:
  assumes s: "s > 0"
  assumes integrable: "integrable M (\<lambda>x. exp (s * f x))"
  shows   "prob {x\<in>space M. f x \<ge> a} \<le> exp (-s * a) * expectation (\<lambda>x. exp (s * f x))"
proof -
  have "{x\<in>space M. f x \<ge> a} = {x\<in>space M. exp (s * f x) \<ge> exp (s * a)}"
    using s by auto
  also have "prob \<dots> \<le> expectation (\<lambda>x. exp (s * f x)) / exp (s * a)"
    by (intro integral_Markov_inequality' assms) auto
  finally show ?thesis 
    by (simp add: exp_minus field_simps)
qed

lemma (in prob_space) Chernoff_ineq_le:
  assumes s: "s > 0"
  assumes integrable: "integrable M (\<lambda>x. exp (-s * f x))"
  shows   "prob {x\<in>space M. f x \<le> a} \<le> exp (s * a) * expectation (\<lambda>x. exp (-s * f x))"
proof -
  have "{x\<in>space M. f x \<le> a} = {x\<in>space M. exp (-s * f x) \<ge> exp (-s * a)}"
    using s by auto
  also have "prob \<dots> \<le> expectation (\<lambda>x. exp (-s * f x)) / exp (-s * a)"
    by (intro integral_Markov_inequality' assms) auto
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

lemma Hoeffdings_lemma_aux:
  fixes h p :: real
  assumes "h \<ge> 0" and "p \<ge> 0"
  defines "L \<equiv> (\<lambda>h. -h * p + ln (1 + p * (exp h - 1)))"
  shows   "L h \<le> h\<^sup>2 / 8"
proof (cases "h = 0")
  case False
  hence h: "h > 0"
    using \<open>h \<ge> 0\<close> by simp
  define L' where "L' = (\<lambda>h. -p + p * exp h / (1 + p * (exp h - 1)))"
  define L'' where "L'' = (\<lambda>h. -(p\<^sup>2) * exp h * exp h / (1 + p * (exp h - 1))\<^sup>2 +
                              p * exp h / (1 + p * (exp h - 1)))"
  define Ls where "Ls = (\<lambda>n. [L, L', L''] ! n)"

  have [simp]: "L 0 = 0" "L' 0 = 0"
    by (auto simp: L_def L'_def)

  have L': "(L has_real_derivative L' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have "1 + p * (exp x - 1) > 0"
      using \<open>p \<ge> 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    thus ?thesis
      unfolding L_def L'_def by (auto intro!: derivative_eq_intros)
  qed

  have L'': "(L' has_real_derivative L'' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have *: "1 + p * (exp x - 1) > 0"
      using \<open>p \<ge> 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      unfolding L'_def L''_def
      by (insert *, (rule derivative_eq_intros refl | simp)+) (auto simp: divide_simps; algebra)
  qed

  have diff: "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> (Ls m has_real_derivative Ls (Suc m) t) (at t)"
    using L' L'' by (auto simp: Ls_def nth_Cons split: nat.splits)
  from Taylor[of 2 Ls L 0 h 0 h, OF _ _ diff]
    obtain t where t: "t \<in> {0<..<h}" "L h = L'' t * h\<^sup>2 / 2"
      using \<open>h > 0\<close> by (auto simp: Ls_def lessThan_nat_numeral)
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
qed (auto simp: L_def)


locale interval_bounded_random_variable = prob_space +
  fixes f :: "'a \<Rightarrow> real" and a b :: real
  assumes random_variable [measurable]: "random_variable borel f"
  assumes AE_in_interval: "AE x in M. f x \<in> {a..b}"
begin

lemma integrable [intro]: "integrable M f"
proof (rule integrable_const_bound)
  show "AE x in M. norm (f x) \<le> max \<bar>a\<bar> \<bar>b\<bar>"
    by (intro eventually_mono[OF AE_in_interval]) auto
qed (fact random_variable)

text \<open>
  We first show Hoeffding's lemma for distributions whose expectation is 0. The general
  case will easily follow from this later.
\<close>
lemma Hoeffdings_lemma_nn_integral_0:
  assumes "l > 0" and E0: "expectation f = 0"
  shows   "nn_integral M (\<lambda>x. exp (l * f x)) \<le> ennreal (exp (l\<^sup>2 * (b - a)\<^sup>2 / 8))"
proof (cases "AE x in M. f x = 0")
  case True
  hence "nn_integral M (\<lambda>x. exp (l * f x)) = nn_integral M (\<lambda>x. ennreal 1)"
    by (intro nn_integral_cong_AE) auto
  also have "\<dots> = ennreal (expectation (\<lambda>_. 1))"
    by (intro nn_integral_eq_integral) auto
  finally show ?thesis by (simp add: prob_space)
next
  case False
  have "a < 0"
  proof (rule ccontr)
    assume a: "\<not>(a < 0)"
    have "AE x in M. f x = 0"
    proof (subst integral_nonneg_eq_0_iff_AE [symmetric])
      show "AE x in M. f x \<ge> 0"
        using AE_in_interval by eventually_elim (use a in auto)
    qed (use E0 in \<open>auto simp: id_def integrable\<close>)
    with False show False by contradiction
  qed

  have "b > 0"
  proof (rule ccontr)
    assume b: "\<not>(b > 0)"
    have "AE x in M. -f x = 0"
    proof (subst integral_nonneg_eq_0_iff_AE [symmetric])
      show "AE x in M. -f x \<ge> 0"
        using AE_in_interval by eventually_elim (use b in auto)
    qed (use E0 in \<open>auto simp: id_def integrable\<close>)
    with False show False by simp
  qed
    
  have "a < b"
    using \<open>a < 0\<close> \<open>b > 0\<close> by linarith

  define p where "p = -a / (b - a)"
  define L where "L = (\<lambda>t. -t* p + ln (1 - p + p * exp t))"
  define z where "z = l * (b - a)"
  have "z > 0"
    unfolding z_def using \<open>a < b\<close> \<open>l > 0\<close> by auto
  have "p > 0"
    using \<open>a < 0\<close> \<open>a < b\<close> unfolding p_def by (intro divide_pos_pos) auto

  have "(\<integral>\<^sup>+x. exp (l * f x) \<partial>M) \<le>
        (\<integral>\<^sup>+x. (b - f x) / (b - a) * exp (l * a) + (f x - a) / (b - a) * exp (l * b) \<partial>M)"
  proof (intro nn_integral_mono_AE eventually_mono[OF AE_in_interval] ennreal_leI)
    fix x assume x: "f x \<in> {a..b}"
    define y where "y = (b - f x) / (b-a)"
    have y: "y \<in> {0..1}"
      using x \<open>a < b\<close> by (auto simp: y_def)
    have conv: "convex_on UNIV (\<lambda>x. exp(l*x))"
      by (intro convex_on_exp) fact+
    have "exp (l * ((1 - y) *\<^sub>R b + y *\<^sub>R a)) \<le> (1 - y) * exp (l * b) + y * exp (l * a)"
      using y \<open>l > 0\<close> by (intro convex_onD[OF convex_on_exp]) auto
    also have "(1 - y) *\<^sub>R b + y *\<^sub>R a = f x"
      using \<open>a < b\<close> by (simp add: y_def divide_simps) (simp add: algebra_simps)?
    also have "1 - y = (f x - a) / (b - a)"
      using \<open>a < b\<close> by (simp add: field_simps y_def)
    finally show "exp (l * f x) \<le> (b - f x) / (b - a) * exp (l*a) + (f x - a)/(b-a) * exp (l*b)"
      by (simp add: y_def)
  qed
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (b - f x) * exp (l * a) / (b - a) +
                        ennreal (f x - a) * exp (l * b) / (b - a) \<partial>M)"
    using \<open>a < 0\<close> \<open>b > 0\<close>
    by (intro nn_integral_cong_AE eventually_mono[OF AE_in_interval])
       (simp add: ennreal_plus ennreal_mult flip: divide_ennreal)
  also have "\<dots> = ((\<integral>\<^sup>+ x. ennreal (b - f x) \<partial>M) * ennreal (exp (l * a)) +
                   (\<integral>\<^sup>+ x. ennreal (f x - a) \<partial>M) * ennreal (exp (l * b))) / ennreal (b - a)"
    by (simp add: nn_integral_add nn_integral_divide nn_integral_multc add_divide_distrib_ennreal)
  also have "(\<integral>\<^sup>+ x. ennreal (b - f x) \<partial>M) = ennreal (expectation (\<lambda>x. b - f x))"
    by (intro nn_integral_eq_integral Bochner_Integration.integrable_diff
              eventually_mono[OF AE_in_interval] integrable_const integrable) auto
  also have "expectation (\<lambda>x. b - f x) = b"
    using assms by (subst Bochner_Integration.integral_diff) (auto simp: prob_space)
  also have "(\<integral>\<^sup>+ x. ennreal (f x - a) \<partial>M) = ennreal (expectation (\<lambda>x. f x - a))"
    by (intro nn_integral_eq_integral Bochner_Integration.integrable_diff
              eventually_mono[OF AE_in_interval] integrable_const integrable) auto
  also have "expectation (\<lambda>x. f x - a) = (-a)"
    using assms by (subst Bochner_Integration.integral_diff) (auto simp: prob_space)
  also have "(ennreal b * (exp (l * a)) + ennreal (-a) * (exp (l * b))) / (b - a) =
             ennreal (b * exp (l * a) - a * exp (l * b)) / ennreal (b - a)"
    using \<open>a < 0\<close> \<open>b > 0\<close>
    by (simp flip: ennreal_mult ennreal_plus add: mult_nonpos_nonneg divide_ennreal mult_mono)
  also have "b * exp (l * a) - a * exp (l * b) = exp (L z) * (b - a)"
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

    have "exp (L z) * (b - a) = exp (-z * p) * (1 - p + p * exp z) * (b - a)"
      using pos by (simp add: exp_add L_def exp_diff exp_minus divide_simps)
    also have "\<dots> = b * exp (l * a) - a * exp (l * b)" using \<open>a < b\<close>
      by (simp add: p_def z_def divide_simps) (simp add:  exp_diff algebra_simps)?
    finally show ?thesis by simp
  qed
  also have "ennreal (exp (L z) * (b - a)) / ennreal (b - a) = ennreal (exp (L z))"
    using \<open>a < b\<close> by (simp add: divide_ennreal)
  also have "L z = -z * p + ln (1 + p * (exp z - 1))"
    by (simp add: L_def algebra_simps)
  also have "\<dots> \<le> z\<^sup>2 / 8"
    unfolding L_def by (rule Hoeffdings_lemma_aux[where p = p]) (use \<open>z > 0\<close> \<open>p > 0\<close> in simp_all)
  hence "ennreal (exp (-z * p + ln (1 + p * (exp z - 1)))) \<le> ennreal (exp (z\<^sup>2 / 8))"
    by (intro ennreal_leI) auto
  finally show ?thesis
    by (simp add: z_def power_mult_distrib)
qed

context
begin

interpretation shift: interval_bounded_random_variable M "\<lambda>x. f x - \<mu>" "a - \<mu>" "b - \<mu>"
  rewrites "b - \<mu> - (a - \<mu>) \<equiv> b - a"
  by unfold_locales (auto intro!: eventually_mono[OF AE_in_interval])

lemma expectation_shift: "expectation (\<lambda>x. f x - expectation f) = 0"
  by (subst Bochner_Integration.integral_diff) (auto simp: integrable prob_space)

lemmas Hoeffdings_lemma_nn_integral = shift.Hoeffdings_lemma_nn_integral_0[OF _ expectation_shift]

end

end


subsection \<open>Hoeffding's Inequality\<close>

text \<open>
  Consider \<open>n\<close> independent real random variables $X_1, \ldots, X_n$ that each almost surely lie
  in a compact interval $[a_i, b_i]$. Hoeffding's inequality states that the distribution of the
  sum of the $X_i$ is tightly concentrated around the sum of the expected values: the probability
  of it being above or below the sum of the expected values by more than some \<open>\<epsilon>\<close> decreases
  exponentially with \<open>\<epsilon>\<close>.
\<close>

locale indep_interval_bounded_random_variables = prob_space +
  fixes I :: "'b set" and X :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  fixes a b :: "'b \<Rightarrow> real"
  assumes fin: "finite I"
  assumes indep: "indep_vars (\<lambda>_. borel) X I"
  assumes AE_in_interval: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<in> {a i..b i}"
begin

lemma random_variable [measurable]:
  assumes i: "i \<in> I"
  shows "random_variable borel (X i)"
  using i indep unfolding indep_vars_def by blast

lemma bounded_random_variable [intro]:
  assumes i: "i \<in> I"
  shows   "interval_bounded_random_variable M (X i) (a i) (b i)"
  by unfold_locales (use AE_in_interval[OF i] i in auto)

end


locale Hoeffding_ineq = indep_interval_bounded_random_variables +
  fixes \<mu> :: real
  defines "\<mu> \<equiv> (\<Sum>i\<in>I. expectation (X i))"
begin

lemma Hoeffding_ineq_ge:
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  define d where "d = (\<Sum>i\<in>I. (b i - a i)\<^sup>2)"
  define l :: real where "l = 4 * \<epsilon> / d"
  have d: "d > 0"
    using assms by (simp add: d_def)
  have l: "l > 0"
    using \<epsilon> d by (simp add: l_def)
  define \<mu>' where "\<mu>' = (\<lambda>i. expectation (X i))"

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} = {x\<in>space M. (\<Sum>i\<in>I. X i x) - \<mu> \<ge> \<epsilon>} \<inter> space M"
    by (simp add: algebra_simps)
  hence "ennreal (prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>}) = emeasure M \<dots>"
    by (simp add: emeasure_eq_measure)
  also have "\<dots> \<le> ennreal (exp (-l*\<epsilon>)) * (\<integral>\<^sup>+x\<in>space M. exp (l * ((\<Sum>i\<in>I. X i x) - \<mu>)) \<partial>M)"
    by (intro Chernoff_ineq_nn_integral_ge l) auto
  also have "(\<lambda>x. (\<Sum>i\<in>I. X i x) - \<mu>) = (\<lambda>x. (\<Sum>i\<in>I. X i x - \<mu>' i))"
    by (simp add: \<mu>_def sum_subtractf \<mu>'_def)
  also have "(\<integral>\<^sup>+x\<in>space M. exp (l * ((\<Sum>i\<in>I. X i x - \<mu>' i))) \<partial>M) =
             (\<integral>\<^sup>+x. (\<Prod>i\<in>I. ennreal (exp (l * (X i x - \<mu>' i)))) \<partial>M)"
    by (intro nn_integral_cong)
       (simp_all add: sum_distrib_left ring_distribs exp_diff exp_sum fin prod_ennreal)
  also have "\<dots> = (\<Prod>i\<in>I. \<integral>\<^sup>+x. ennreal (exp (l * (X i x - \<mu>' i))) \<partial>M)"
    by (intro indep_vars_nn_integral fin indep_vars_compose2[OF indep]) auto
  also have "ennreal (exp (-l * \<epsilon>)) * \<dots> \<le>
               ennreal (exp (-l * \<epsilon>)) * (\<Prod>i\<in>I. ennreal (exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)))"
  proof (intro mult_left_mono prod_mono_ennreal)
    fix i assume i: "i \<in> I"
    from i interpret interval_bounded_random_variable M "X i" "a i" "b i" ..
    show "(\<integral>\<^sup>+x. ennreal (exp (l * (X i x - \<mu>' i))) \<partial>M) \<le> ennreal (exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8))"
      unfolding \<mu>'_def by (rule Hoeffdings_lemma_nn_integral) fact+
  qed auto
  also have "\<dots> = ennreal (exp (-l*\<epsilon>) * (\<Prod>i\<in>I. exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)))"
    by (simp add: prod_ennreal prod_nonneg flip: ennreal_mult)
  also have "exp (-l*\<epsilon>) * (\<Prod>i\<in>I. exp (l\<^sup>2 * (b i - a i)\<^sup>2 / 8)) = exp (d * l\<^sup>2 / 8 - l * \<epsilon>)"
    by (simp add: exp_diff exp_minus sum_divide_distrib sum_distrib_left
                  sum_distrib_right exp_sum fin divide_simps mult_ac d_def)
  also have "d * l\<^sup>2 / 8 - l * \<epsilon> = -2 * \<epsilon>\<^sup>2 / d"
    using d by (simp add: l_def field_simps power2_eq_square)
  finally show ?thesis
    by (subst (asm) ennreal_le_iff) (simp_all add: d_def)
qed

corollary Hoeffding_ineq_le:
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  interpret flip: Hoeffding_ineq M I "\<lambda>i x. -X i x" "\<lambda>i. -b i" "\<lambda>i. -a i" "-\<mu>"
  proof unfold_locales
    fix i assume "i \<in> I"
    then interpret interval_bounded_random_variable M "X i" "a i" "b i" ..
    show "AE x in M. - X i x \<in> {- b i..- a i}"
      by (intro eventually_mono[OF AE_in_interval]) auto
  qed (auto simp: fin \<mu>_def sum_negf intro: indep_vars_compose2[OF indep])

  have "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>} = prob {x\<in>space M. (\<Sum>i\<in>I. -X i x) \<ge> -\<mu> + \<epsilon>}"
    by (simp add: sum_negf algebra_simps)
  also have "\<dots> \<le> exp (- 2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
    using flip.Hoeffding_ineq_ge[OF \<epsilon>] assms(2) by simp
  finally show ?thesis .
qed

corollary Hoeffding_ineq_abs_ge:
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes "(\<Sum>i\<in>I. (b i - a i)\<^sup>2) > 0"
  shows   "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu>\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
proof -
  have "{x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu>\<bar> \<ge> \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} \<union> {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>}"
    by auto
  also have "prob \<dots> \<le> prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> + \<epsilon>} +
                       prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> - \<epsilon>}"
    by (intro measure_Un_le) auto
  also have "\<dots> \<le> exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2)) + exp (-2 * \<epsilon>\<^sup>2 / (\<Sum>i\<in>I. (b i - a i)\<^sup>2))"
    by (intro add_mono Hoeffding_ineq_ge Hoeffding_ineq_le assms)
  finally show ?thesis by simp
qed

end


subsection \<open>Hoeffding's inequality for i.i.d. bounded random variables\<close>

subsection \<open>
  If we have \<open>n\<close> even identically-distributed random variables, the statement of Hoeffding's
  lemma simplifies a bit more: it shows that the probability that the average of the $X_i$
  is more than \<open>\<epsilon>\<close> above the expected value is no greater than $e^{\frac{-2ny^2}{(b-a)^2}}$.

  This essentially gives us a more concrete version of the weak law of large numbers: the law
  states that the probability vanishes for \<open>n \<rightarrow> \<infinity>\<close> for any \<open>\<epsilon> > 0\<close>. Unlike Hoeffding's inequality,
  it does not assume the variables to have bounded support, but it does not provide concrete bounds.
\<close>

locale iid_interval_bounded_random_variables = prob_space +
  fixes I :: "'b set" and X :: "'b \<Rightarrow> 'a \<Rightarrow> real" and Y :: "'a \<Rightarrow> real"
  fixes a b :: real
  assumes fin: "finite I"
  assumes indep: "indep_vars (\<lambda>_. borel) X I"
  assumes distr_X: "i \<in> I \<Longrightarrow> distr M borel (X i) = distr M borel Y"
  assumes rv_Y [measurable]: "random_variable borel Y"
  assumes AE_in_interval: "AE x in M. Y x \<in> {a..b}"
begin

lemma random_variable [measurable]:
  assumes i: "i \<in> I"
  shows "random_variable borel (X i)"
  using i indep unfolding indep_vars_def by blast

sublocale X: indep_interval_bounded_random_variables M I X "\<lambda>_. a" "\<lambda>_. b"
proof
  fix i assume i: "i \<in> I"
  have "AE x in M. Y x \<in> {a..b}"
    by (fact AE_in_interval)
  also have "?this \<longleftrightarrow> (AE x in distr M borel Y. x \<in> {a..b})"
    by (subst AE_distr_iff) auto
  also have "distr M borel Y = distr M borel (X i)"
    using i by (simp add: distr_X)
  also have "(AE x in \<dots>. x \<in> {a..b}) \<longleftrightarrow> (AE x in M. X i x \<in> {a..b})"
    using i by (subst AE_distr_iff) auto
  finally show "AE x in M. X i x \<in> {a..b}" .
qed (simp_all add: fin indep)

lemma expectation_X [simp]:
  assumes i: "i \<in> I"
  shows "expectation (X i) = expectation Y"
proof -
  have "expectation (X i) = lebesgue_integral (distr M borel (X i)) (\<lambda>x. x)"
    using i by (intro integral_distr [symmetric]) auto
  also have "distr M borel (X i) = distr M borel Y"
    using i by (rule distr_X)
  also have "lebesgue_integral \<dots> (\<lambda>x. x) = expectation Y"
    by (rule integral_distr) auto
  finally show "expectation (X i) = expectation Y" .
qed

end


locale Hoeffding_ineq_iid = iid_interval_bounded_random_variables +
  fixes \<mu> :: real
  defines "\<mu> \<equiv> expectation Y"
begin

sublocale X: Hoeffding_ineq M I X "\<lambda>_. a" "\<lambda>_. b" "real (card I) * \<mu>"
  by unfold_locales (simp_all add: \<mu>_def)

lemma 
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes "a < b" "I \<noteq> {}"
  defines "n \<equiv> card I"
  shows   Hoeffding_ineq_ge:
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> n * \<mu> + \<epsilon>} \<le>
               exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?le)
    and   Hoeffding_ineq_le:
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> n * \<mu> - \<epsilon>} \<le>
               exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?ge)
    and   Hoeffding_ineq_abs_ge:
            "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - n * \<mu>\<bar> \<ge> \<epsilon>} \<le>
               2 * exp (-2 * \<epsilon>\<^sup>2 / (n * (b - a)\<^sup>2))" (is ?abs_ge)
proof -
  have pos: "(\<Sum>i\<in>I. (b - a)\<^sup>2) > 0"
    using \<open>a < b\<close> \<open>I \<noteq> {}\<close> fin by (intro sum_pos) auto
  show ?le
    using X.Hoeffding_ineq_ge[OF \<epsilon> pos] by (simp add: n_def)
  show ?ge
    using X.Hoeffding_ineq_le[OF \<epsilon> pos] by (simp add: n_def)
  show ?abs_ge
    using X.Hoeffding_ineq_abs_ge[OF \<epsilon> pos] by (simp add: n_def)
qed

lemma 
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes "a < b" "I \<noteq> {}"
  defines "n \<equiv> card I"
  shows   Hoeffding_ineq_ge':
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<ge> \<mu> + \<epsilon>} \<le>
               exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?ge)
    and   Hoeffding_ineq_le':
            "prob {x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<le> \<mu> - \<epsilon>} \<le>
               exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?le)
    and   Hoeffding_ineq_abs_ge':
            "prob {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) / n - \<mu>\<bar> \<ge> \<epsilon>} \<le>
               2 * exp (-2 * n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" (is ?abs_ge)
proof -
  have "n > 0"
    using assms fin by (auto simp: field_simps)
  have \<epsilon>': "\<epsilon> * n > 0"
    using \<open>n > 0\<close> \<open>\<epsilon> > 0\<close> by auto
  have eq: "- (2 * (\<epsilon> * real n)\<^sup>2 / (real (card I) * (b - a)\<^sup>2)) =
            - (2 * real n * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)"
    using \<open>n > 0\<close> by (simp add: power2_eq_square divide_simps n_def)

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<ge> \<mu> + \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<ge> \<mu> * n + \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_ge[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?ge
    by (simp add: n_def mult_ac)

  have "{x\<in>space M. (\<Sum>i\<in>I. X i x) / n \<le> \<mu> - \<epsilon>} =
        {x\<in>space M. (\<Sum>i\<in>I. X i x) \<le> \<mu> * n - \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_le[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?le
    by (simp add: n_def mult_ac)

  have "{x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) / n - \<mu>\<bar> \<ge> \<epsilon>} =
        {x\<in>space M. \<bar>(\<Sum>i\<in>I. X i x) - \<mu> * n\<bar> \<ge> \<epsilon> * n}"
    using \<open>n > 0\<close> by (intro Collect_cong conj_cong refl) (auto simp: field_simps)
  with Hoeffding_ineq_abs_ge[OF \<epsilon>' \<open>a < b\<close> \<open>I \<noteq> {}\<close>] \<open>n > 0\<close> eq show ?abs_ge
    by (simp add: n_def mult_ac)
qed

end


subsection \<open>Hoeffding's Inequality for the Binomial distribution\<close>

text \<open>
  We can now apply Hoeffding's inequality to the Binomial distribution, which can be seen
  as the sum of \<open>n\<close> i.i.d. coin flips (the support of each of which is contained in $[0,1]$).
\<close>

locale binomial_distribution =
  fixes n :: nat and p :: real
  assumes p: "p \<in> {0..1}"
begin

context
  fixes coins :: "(nat \<Rightarrow> bool) pmf" and \<mu>
  assumes n: "n > 0"
  defines "coins \<equiv> Pi_pmf {..<n} False (\<lambda>_. bernoulli_pmf p)"
begin

lemma coins_component:
  assumes i: "i < n"
  shows   "distr (measure_pmf coins) borel (\<lambda>f. if f i then 1 else 0) =
             distr (measure_pmf (bernoulli_pmf p)) borel (\<lambda>b. if b then 1 else 0)"
proof -
  have "distr (measure_pmf coins) borel (\<lambda>f. if f i then 1 else 0) =
        distr (measure_pmf (map_pmf (\<lambda>f. f i) coins)) borel (\<lambda>b. if b then 1 else 0)"
    unfolding map_pmf_rep_eq by (subst distr_distr) (auto simp: o_def)
  also have "map_pmf (\<lambda>f. f i) coins = bernoulli_pmf p"
    unfolding coins_def using i by (subst Pi_pmf_component) auto
  finally show ?thesis
    unfolding map_pmf_rep_eq .
qed

lemma prob_binomial_pmf_conv_coins:
  "measure_pmf.prob (binomial_pmf n p) {x. P (real x)} = 
   measure_pmf.prob coins {x. P (\<Sum>i<n. if x i then 1 else 0)}"
proof -
  have eq1: "(\<Sum>i<n. if x i then 1 else 0) = real (card {i\<in>{..<n}. x i})" for x
  proof -
    have "(\<Sum>i<n. if x i then 1 else (0::real)) = (\<Sum>i\<in>{i\<in>{..<n}. x i}. 1)"
      by (intro sum.mono_neutral_cong_right) auto
    thus ?thesis by simp
  qed
  have eq2: "binomial_pmf n p = map_pmf (\<lambda>v. card {i\<in>{..<n}. v i}) coins"
    unfolding coins_def by (rule binomial_pmf_altdef') (use p in auto)
  show ?thesis
    by (subst eq2) (simp_all add: eq1)
qed

interpretation Hoeffding_ineq_iid
  coins "{..<n}" "\<lambda>i f. if f i then 1 else 0" "\<lambda>f. if f 0 then 1 else 0" 0 1 p
proof unfold_locales
  show "prob_space.indep_vars (measure_pmf coins) (\<lambda>_. borel) (\<lambda>i f. if f i then 1 else 0) {..<n}"
    unfolding coins_def
    by (intro prob_space.indep_vars_compose2[OF _ indep_vars_Pi_pmf])
       (auto simp: measure_pmf.prob_space_axioms)
next
  have "measure_pmf.expectation coins (\<lambda>f. if f 0 then 1 else 0 :: real) =
        measure_pmf.expectation (map_pmf (\<lambda>f. f 0) coins) (\<lambda>b. if b then 1 else 0 :: real)"
    by (simp add: coins_def)
  also have "map_pmf (\<lambda>f. f 0) coins = bernoulli_pmf p"
    using n by (simp add: coins_def Pi_pmf_component)
  also have "measure_pmf.expectation \<dots> (\<lambda>b. if b then 1 else 0) = p"
    using p by simp
  finally show "p \<equiv> measure_pmf.expectation coins (\<lambda>f. if f 0 then 1 else 0)" by simp
qed (auto simp: coins_component)

corollary
  fixes \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> > 0"
  shows prob_ge: "measure_pmf.prob (binomial_pmf n p) {x. x \<ge> n * p + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    and prob_le: "measure_pmf.prob (binomial_pmf n p) {x. x \<le> n * p - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    and prob_abs_ge:
          "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x - n * p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * \<epsilon>\<^sup>2 / n)"
proof -
  have [simp]: "{..<n} \<noteq> {}"
    using n by auto
  show "measure_pmf.prob (binomial_pmf n p) {x. x \<ge> n * p + \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_ge[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. x \<le> n * p - \<epsilon>} \<le> exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_le[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x - n * p\<bar> \<ge> \<epsilon>} \<le> 2 *  exp (-2 * \<epsilon>\<^sup>2 / n)"
    using Hoeffding_ineq_abs_ge[of \<epsilon>]
    by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
qed

corollary
  fixes \<epsilon> :: real
  assumes \<epsilon>: "\<epsilon> > 0"
  shows prob_ge': "measure_pmf.prob (binomial_pmf n p) {x. x / n \<ge> p + \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    and prob_le': "measure_pmf.prob (binomial_pmf n p) {x. x / n \<le> p - \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    and prob_abs_ge':
          "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x / n - p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * n * \<epsilon>\<^sup>2)"
proof -
  have [simp]: "{..<n} \<noteq> {}"
    using n by auto
  show "measure_pmf.prob (binomial_pmf n p) {x. x / n \<ge> p + \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_ge'[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. x / n \<le> p - \<epsilon>} \<le> exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_le'[of \<epsilon>] by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
  show "measure_pmf.prob (binomial_pmf n p) {x. \<bar>x / n - p\<bar> \<ge> \<epsilon>} \<le> 2 * exp (-2 * n * \<epsilon>\<^sup>2)"
    using Hoeffding_ineq_abs_ge'[of \<epsilon>]
    by (subst prob_binomial_pmf_conv_coins) (use assms in simp_all)
qed

end

end

end