\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory PMF_expectation
  imports Main  "HOL-Probability.Probability"
begin


paragraph \<open>Summary\<close>
text \<open>In this theory we prove lemmas connected to 
integrals and expectation of measures and in most cases pmf_measures.
Lebesgue integral  and Non-negative lebesgue integral  
are considered.
 \<close>

paragraph \<open>Main Theorems\<close>
text \<open>
\<^item> about restriction of function over a set
\<^item> about indicators about a function over a set
\<^item> \<open>integrable_pair_pmf\<close> for two pmf_measures p and q and a non_negative 
function f, if f is integrable over q for every element f p \<Longrightarrow> 
nn_integral of f over q is integrable over p \<Longleftrightarrow>
f is integrable over (pair_pmf p q)
\<^item> \<open>not_integrable_sum\<close> for a non-negative set of functions:
exists a function that is not integrable over a pmf_set M \<Longleftrightarrow>
then the sum of the functions is not integrable over the set M
\<close>


lemma restrict_integral:
  "integral\<^sup>L M f = integral\<^sup>L M   (restrict f (space M))" 
  by (metis Bochner_Integration.integral_cong restrict_apply)

lemma restrict_nn_integral:
  "integral\<^sup>N M f = integral\<^sup>N M   (restrict f (space M))" 
  by (metis nn_integral_cong restrict_apply)

lemma integral_measure_pmf_real_indicator:
  fixes f :: "'e \<Rightarrow> real"
  shows "(\<integral>x. f x \<partial>measure_pmf M) =  (\<integral>x. f x * indicator M x \<partial>measure_pmf M)"
  by (intro integral_cong_AE) 
    (auto split: split_indicator simp: AE_measure_pmf_iff)

lemma nn_integral_measure_pmf_real_indicator:
  fixes f :: "'e \<Rightarrow> real"
  shows "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf M) =  (\<integral>\<^sup>+ x. f x * indicator M x \<partial>measure_pmf M)"
  by (intro nn_integral_cong_AE)
    (auto split: split_indicator simp: AE_measure_pmf_iff)

lemma integral_restrict_space_same:
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>L (restrict_space M M) f = integral\<^sup>L M f" 
  by (simp add: integral_pmf_restrict)

lemma integral_restrict_space_eq_restrict_fun: 
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>L (restrict_space M M) f = integral\<^sup>L M (restrict f (set_pmf M))"
  using  integral_restrict_space_same restrict_integral 
  by (metis FuncSet.restrict_restrict space_restrict_space)

lemma pmf_restrict:
  fixes f :: "'e \<Rightarrow> real"
  shows "measure_pmf.expectation M (\<lambda> x. f x) = measure_pmf.expectation M (\<lambda> x\<in>M. f x)" 
  by (metis integral_restrict_space_eq_restrict_fun integral_restrict_space_same)

lemma nn_integral_pmf_restrict:
  fixes f::"'e \<Rightarrow> real"
  shows "(\<integral>\<^sup>+ x. f x \<partial>measure_pmf M) = (\<integral>\<^sup>+ x. f x \<partial>restrict_space M M)"
  by (auto intro!: nn_integral_cong_AE simp add: nn_integral_restrict_space AE_measure_pmf_iff)

lemma nn_integral_restrict_space_same: 
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>N (restrict_space M M) f = integral\<^sup>N M (restrict f (set_pmf M))"
  by (smt UNIV_I nn_integral_cong nn_integral_pmf_restrict restrict_apply' 
      sets_measure_pmf space_restrict_space2)

lemma nn_integral_restrict_space_eq_restrict_fun:
  fixes f :: "'e \<Rightarrow> real"
  fixes M :: " 'e pmf"
  shows "integral\<^sup>N M (restrict f (set_pmf M)) = integral\<^sup>N M f"
  using nn_integral_pmf_restrict nn_integral_restrict_space_same by metis

lemma same_integral_restricted[simp]:
  fixes f ::"( 'a \<Rightarrow> real)"
  fixes g ::"( 'a \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>L M f = integral\<^sup>L M g"
  by (metis Bochner_Integration.integral_cong Int_iff assms 
        integral_restrict_space_same space_restrict_space)
 

lemma same_nn_integral_restricted:
  fixes f ::"('a \<Rightarrow> real)"
  fixes g ::"('a \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
  by (metis (mono_tags, lifting) assms ennreal_0 mult_not_zero nn_integral_cong 
      nn_integral_measure_pmf pmf_eq_0_set_pmf)

lemma same_nn_integral_restricted_ennreal:
  fixes f ::"(  'a \<Rightarrow> ennreal)"
  fixes g ::"(  'a \<Rightarrow> ennreal)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
  by (metis (mono_tags, lifting) assms ennreal_0 mult_not_zero nn_integral_cong 
      nn_integral_measure_pmf pmf_eq_0_set_pmf)

lemma integrable_pair_pmf:
  fixes f ::"( 'a \<times> 'b \<Rightarrow> real)"
  assumes f_nn: "AE S in (measure_pmf p). AE z in (measure_pmf q). f (S, z) \<ge> 0"
  assumes integrable_q: "\<forall> S \<in> p. integrable q (\<lambda> x. f (S, x))"
  shows "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) \<longleftrightarrow>
      integrable (pair_pmf p q) f"
proof -
  let ?N = "(pair_pmf p q)"

  have 1:" \<integral>\<^sup>+ x. f x \<partial> ?N =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.(f (x,y)) \<partial>q \<partial>p" 
    using nn_integral_pair_pmf' by auto

  have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>q \<partial>p  =  
    \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f (x,y) \<partial>q \<partial>p"
  proof -
    have "AE S in p. AE z in q. (\<lambda> x. ennreal (norm (f x)) =  f x ) (S,z)"
      using f_nn  by (simp add: AE_measure_pmf_iff)
    then have "AE x in p. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>q =
          \<integral>\<^sup>+ y.(f (x,y)) \<partial>q" 
    proof
      have "\<forall> x \<in> p. 
       (AE z in  q. ennreal (norm (f (x, z))) = ennreal (f (x, z))) \<longrightarrow>
                   \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> q =
                   \<integral>\<^sup>+ xa. ennreal (f (x, xa)) \<partial> q" using nn_integral_cong_AE by auto

      then show " AE x in p. (AE z in  q. ennreal (norm (f (x, z))) = (f (x, z))) \<longrightarrow>
    \<integral>\<^sup>+ y. ennreal (norm (f (x, y))) \<partial> q = \<integral>\<^sup>+ xa.  (f (x, xa)) \<partial> q"
        using AE_measure_pmf_iff nn_integral_cong_AE by blast
    qed

    then show ?thesis 
      by (simp add: nn_integral_cong_AE)
  qed
  then have 2: "\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial> ?N = \<integral>\<^sup>+ x. f x \<partial> ?N"
    using nn_integral_pair_pmf'  by (smt nn_integral_cong)

  have " \<forall> S \<in> p. (\<integral>\<^sup>+ x. (f (S,x)) \<partial>q) < top"  
    using integrable_q   
    by (metis (mono_tags, lifting) AE_measure_pmf_iff ennreal_less_top
        f_nn nn_integral_cong nn_integral_eq_integral)

  then have "integral\<^sup>N p ((\<lambda> S.  (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))) =
               integral\<^sup>N p (\<lambda> S.  (\<integral>\<^sup>+ x. f (S, x) \<partial>q))"
    by (simp add:  AE_measure_pmf_iff nn_integral_cong_AE)


  then have " ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) \<in> borel_measurable p \<and>
      ( \<integral>\<^sup>+ S. ennreal (norm ((\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f (S,x) \<partial>q)) S ))\<partial>p) < \<infinity>) \<longleftrightarrow>
       (f \<in> borel_measurable ?N \<and> (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>?N) < \<infinity>)"
    using 1 2 by auto

  then show ?thesis  using integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed

lemma integrable_pair_pmf':
  fixes f ::"( 'a \<Rightarrow> 'b \<Rightarrow> real)"
  assumes f_nn: "AE S in (measure_pmf p) . AE z in (measure_pmf q). f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (f S)"
  shows "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f S x \<partial>q)) \<longleftrightarrow>
      integrable (pair_pmf p q) (\<lambda> (S,z). f S z)"
  using integrable_pair_pmf[of  "(\<lambda> (S,z). f S z)"] assms by auto

lemma expectation_pair_pmf:
  fixes f ::"( 'a \<times> 'b \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf p). \<forall> z \<in> (set_pmf q). f (S,z) \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (\<lambda> z. f (S, z))"
  shows  "measure_pmf.expectation (pair_pmf p q) f
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda>y. f (x, y)))"
proof -
  let ?pair = "(pair_pmf p q)"
  have 1:"\<forall>S\<in> p.  ennreal (integral\<^sup>L  q (\<lambda> z. f (S, z))) = 
        (\<integral>\<^sup>+ x. f (S, x) \<partial>q)"  
  proof 
    fix S
    assume "S \<in> p"
    then have "AE x in q. 0 \<le> f (S,x)" using  f_nn  by (simp add: AE_measure_pmf_iff)
    then have "(\<integral>\<^sup>+ x.  f (S,x) \<partial>q) = (integral\<^sup>L  q (\<lambda> z. f (S,z)))" 
      using  nn_integral_eq_integral `S \<in> p`  integrable_D by blast
    then show "  ennreal (integral\<^sup>L q (\<lambda> z. f (S,z))) = (\<integral>\<^sup>+ x. f (S, x) \<partial>q)" by auto
  qed
  then have 2: "\<forall>S \<in> p. (integral\<^sup>L  q (\<lambda> z. f (S,z))) = 
        enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)" using  enn2real_ennreal 
    by (metis (mono_tags, lifting) AE_measure_pmf_iff f_nn integral_nonneg_AE)  
  then have 3: " (integral\<^sup>L p (\<lambda> S. integral\<^sup>L q (\<lambda> z. f (S,z)))) =
         (integral\<^sup>L p (\<lambda> S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))"
    using pmf_restrict same_integral_restricted by fastforce 
  have "\<forall>S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q) \<ge> 0" by auto
  then have 4: "AE S in p. (\<lambda> S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)) S \<ge> 0" 
    by blast

  show ?thesis
  proof(cases "integrable p  (\<lambda> S. enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q))")
    case True
    have "AE S in p. AE z in q. f (S, z) \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have integrable_pair: "integrable ?pair f"
      using  integrable_pair_pmf integrable_D True  by auto 

    have 11: "integral\<^sup>N p ((\<lambda> S. ennreal (enn2real (\<integral>\<^sup>+ x. f (S, x) \<partial>q)))) =
               integral\<^sup>N p (\<lambda> S. (\<integral>\<^sup>+ x. f (S, x) \<partial>q))"
      by (smt "1" "2" AE_measure_pmf_iff nn_integral_cong_AE)

    have 12: " integral\<^sup>N ?pair f =
         (\<integral>\<^sup>+ S. (\<integral>\<^sup>+ x. f (S,x) \<partial>q) \<partial>p)"
      using nn_integral_pair_pmf'[of "p" q "f"] by blast

    have "\<forall> Sx \<in> ?pair.  f Sx \<ge> 0" 
      using map_fst_pair_pmf  map_snd_pair_pmf f_nn by fastforce
    then  have "AE Sx in ?pair.  f Sx \<ge> 0"
      using  AE_measure_pmf_iff by blast
    then show ?thesis 
      by (metis "11" "12" "3" "4" True ennreal_inj integrable_pair
          integral_nonneg_AE  nn_integral_eq_integral) 
  next
    case False
    have "AE S in p. AE z in q. f (S, z) \<ge> 0" using f_nn 
      by (simp add: AE_measure_pmf_iff)
    then have not_integrable_pair: "\<not> integrable ?pair f"
      using integrable_pair_pmf  integrable_D False  by auto 
    then show ?thesis 
      using "3" False integral_eq_cases by auto
  qed
qed

lemma expectation_pair_pmf':
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf p). \<forall> z \<in> (set_pmf q). f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (\<lambda> z. f S z)"
  shows  "measure_pmf.expectation (pair_pmf p q) (\<lambda> (x,y). f x y)
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda> y. f x y))"
  using expectation_pair_pmf[of p q "(\<lambda> (x,y). f x y)"] assms by auto

lemma not_integrable_sum:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin : "finite I"
  assumes not_int: "\<exists> i \<in> I. \<not> integrable M (f i)"
  shows  " \<not> integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
proof -
  have 0: "\<forall> i \<in> I. f i \<in> borel_measurable M" by auto

  then have 1:" (\<Sum>i\<in>I. \<integral>\<^sup>+ x. (f i x) \<partial> M) = 
   \<integral>\<^sup>+ x. (\<Sum>i\<in>I. ennreal (f i x))  \<partial> M " using nn_integral_sum[of I f M] by auto
  have "\<forall> x \<in> M. ennreal (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. ennreal (f i x))" 
    using f_nn by auto

  then have 2: " \<integral>\<^sup>+ x. (\<Sum>i\<in>I. (f i x)) \<partial>M = (\<Sum>i\<in>I. integral\<^sup>N M (f i))"
    using 1 same_nn_integral_restricted
    by (smt ennreal_mult_left_cong ennreal_neg nn_integral_cong nn_integral_measure_pmf pmf_eq_0_set_pmf)

  have "\<exists> i \<in> I. integral\<^sup>N M (f i) = \<infinity>" 
  proof -
    obtain i where "i\<in>I" and " \<not> integrable M (f i)" using not_int by auto
    have " (\<lambda> x \<in> M. f i x) = (\<lambda> x \<in> M. norm (f i x))" using f_nn `i \<in> I` by auto
    then have " integral\<^sup>N M (f i) =  integral\<^sup>N M (\<lambda> x. norm ((f i) x))"
      by (metis nn_integral_restrict_space_eq_restrict_fun)
    then have "\<not> integral\<^sup>N M (f i) < \<infinity>"
      using `\<not> integrable M (f i)` 0 integrableI_bounded `i \<in> I` by metis
    then have "integral\<^sup>N M (f i) = \<infinity>"
      by (metis ennreal_cases ennreal_less_top infinity_ennreal_def)
    then show ?thesis using `i\<in>I` by auto
  qed

  then have "(\<Sum>i\<in>I. integral\<^sup>N M (f i)) = \<infinity>" using sum_Inf[of "(\<lambda> i. enn2ereal ( integral\<^sup>N M (f i)))" I]
      fin  by simp
  then have "\<integral>\<^sup>+ x. (\<Sum>i\<in>I. f i x) \<partial>M = \<infinity>" using 2 by auto

  then show "\<not> integrable M (\<lambda> x. (\<Sum>i\<in>I. f i x))" by auto
qed

lemma integrable_sum_iff:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin_I : "finite I"
  shows "(\<forall> i \<in> I.  integrable M (f i)) \<longleftrightarrow> 
      integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
proof(cases "(\<forall> i \<in> I.  integrable M (f i))")
  case True
  then show ?thesis using integrable_sum by auto
next
  case False
  then have "\<exists> i \<in> I. \<not> integrable M (f i)" by auto
  then show ?thesis using not_integrable_sum[of M I f] assms by blast
qed

lemma swap_set_expectation:
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "\<forall> S \<in> (set_pmf M). \<forall> i \<in> I. f i S \<ge> 0"
  assumes fin_I : "finite I"
  assumes non_empty : " I \<noteq> {}"
  assumes I_swap: 
    "\<forall> i\<in> I. \<forall> j \<in> I. measure_pmf.expectation M (\<lambda> S. f i S) =
       measure_pmf.expectation M (\<lambda> S. f j S)"
  shows " integral\<^sup>L M  (\<lambda> S. integral\<^sup>L (pmf_of_set I)  (\<lambda> i. f i S)) =
      integral\<^sup>L (pmf_of_set I) (\<lambda> i. integral\<^sup>L M (\<lambda> S. f i S))"
proof -
  have 1: "(\<forall> i \<in> I.  integrable M (f i)) \<longleftrightarrow> 
      integrable (measure_pmf M) (\<lambda> x. (\<Sum>i\<in>I. f i x))" 
    using f_nn fin_I integrable_sum_iff[of M I f] by auto
  have " integral\<^sup>L M  (\<lambda> S. sum (\<lambda> i. f i S) I) = sum (\<lambda> i. integral\<^sup>L M (\<lambda> S. f i S)) I "
  proof (cases "(\<forall> i \<in> I.  integrable M (f i))")
    case True
    then show ?thesis using integrable_sum by auto
  next
    case False
    have 2: "\<not> integrable ( M) (\<lambda> x. (\<Sum>i\<in>I. f i x))"
      using False 1 by blast
    then have 3: "measure_pmf.expectation M 
          (\<lambda> Sz. sum (\<lambda> i. f i Sz) I) = 0"
      by (simp add: not_integrable_integral_eq)
    then  have "\<forall> i\<in> I. integral\<^sup>L M (f i) = 0" using False
      by (metis "1" I_swap integral_eq_cases)
    then have "sum (\<lambda> i. measure_pmf.expectation M (f i)) I = 0" 
      by simp
    then show ?thesis 
      using 3 by linarith
  qed
  then show ?thesis using  non_empty fin_I
    by (simp add: integral_pmf_of_set)
qed

lemma integral_bellow_const:
  fixes f :: "'a \<Rightarrow> real"
  assumes smaller_a: "AE x in M.  f x \<le> (a::real) "
  assumes pos_a: "a\<ge>0" 
  assumes M_finite: "finite_measure M"
  shows " integral\<^sup>L M f \<le> measure M (space M) *\<^sub>R a"
proof(cases "integrable M f")
  case True
  have const_integrable: "integrable M (\<lambda> y. a)"
    using finite_measure.integrable_const M_finite by auto
  have "integral\<^sup>L M (\<lambda>y. a) = (\<integral>x. a \<partial>M)" by simp
  then have "integral\<^sup>L M (\<lambda>y. a) = measure M (space M) *\<^sub>R a"
    using lebesgue_integral_const by auto
  then have "AE x in M.  f x \<le> (\<lambda> y. a) x " 
    using smaller_a  by auto
  then have " integral\<^sup>L M f \<le> integral\<^sup>L M (\<lambda>y. a)"
    using integral_mono_AE const_integrable  True by blast
  then show ?thesis
    using \<open>LINT y|M. a = Sigma_Algebra.measure M (space M) *\<^sub>R a\<close> by linarith
next
  case False
  have "integral\<^sup>L M f = 0" using False 
    by (simp add: not_integrable_integral_eq)
  then show ?thesis 
    by (simp add: pos_a)
qed

lemma sum_bounded_const:
  fixes t::nat
  fixes f :: "nat \<Rightarrow> real"
  fixes a :: "real"
  shows "\<forall> i \<in> {0..<t}. f i \<le> a \<Longrightarrow> sum f {0..<t} \<le> t * a"
proof (induct t)
  case 0
  then show ?case by auto
next
  case (Suc t)
  have "\<forall>i\<in>{0..<Suc t}. f i \<le> a" using Suc.prems by auto
  have "sum f {0..<t} \<le> t * a"  using Suc.prems Suc.hyps by auto
  then have "sum f {0..<t} + f t \<le> t * a + f t" using Suc.prems by auto
  also have "t * a + f t \<le> t * a + a" using Suc.prems by auto
  also have "t * a + a = (Suc t) * a"  by (simp add: semiring_normalization_rules(2))
  finally show ?case by auto
qed

end