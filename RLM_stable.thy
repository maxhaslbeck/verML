\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory RLM_stable
  imports  "RLM_learn" "Expectation_over_samples"
begin


paragraph \<open>Summary\<close>
text \<open>In this theorem we prove that regularized learning minimization is stable.
This means that small changes in the dataset won't change the result much.
Later we consider the loss function l to be lipschitz and integrable. We then prove 
The oracle inequality as shown in corollary 13.8 in @{cite UnderstandingML}.\<close>

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


locale ridge_and_convex_loss = learning_basics_loss + 
assumes convl : "\<forall>y \<in> D. convex_on H (\<lambda> h. l h y)"
begin

text\<open>Show the connection between the loss for S and the loss for S_(i)\<close>
lemma fun_upd_error : 
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes i_in_int: "i\<in>{0..<n}"
  shows "train_err_loss S n l v =
    train_err_loss (S (i:= z)) n l v + (l v (S i))/n - (l v z)/n"
proof -
  let ?S_i = "(S (i:= z))"
  let ?I = "{0..<n}"
  have "?S_i i = z" by  auto
  moreover have  " sum (\<lambda>j. l v (S j)) ?I - sum (\<lambda>j. l v (?S_i j) ) ?I =
      sum (\<lambda>j. l v (S j) - l v (?S_i j)) ?I"
    by (simp add: sum_subtractf)
  moreover  have "sum (\<lambda>j. l v (S j) - l v (?S_i j)) ?I = 
             l v (S i) - l v (?S_i i)" 
    using fun_upd_similar i_in_int sum_split by auto
  moreover have "sum (\<lambda>j. l v (S j) ) ?I = sum (\<lambda>j. l v (?S_i j) ) ?I 
      +  (l v (S i)) - (l v z)" using `?S_i i = z` 
    using calculation(2) calculation(3) by auto
  ultimately have "sum (\<lambda>j. l v (S j) ) ?I/n = sum (\<lambda>j. l v (?S_i j) ) ?I/n 
      +  (l v (S i))/n - (l v z)/n"
    by (simp add:  add_divide_distrib diff_divide_distrib)

  then show ?thesis by (metis (mono_tags, lifting) sum.cong train_err_loss_def)
qed



text\<open>Equation 13.7\<close>
lemma ridge_diff_ge_dist: 
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes v_in_H: "v \<in> H" 
  assumes w_is_argmin: "w \<in> (ridge_argmin S k)"
  shows "ridge_fun S k v - ridge_fun S k w \<ge>  k * norm(v - w)^2"
proof -
  let ?f = "ridge_fun S k"
  have  "w \<in> H"   using w_is_argmin ridge_argmin_def 
    by (simp add: is_arg_min_def)
  have  "\<forall>y\<in>H. (?f w \<le> ?f y)"
    using is_arg_min_linorder w_is_argmin ridge_argmin_def 
    by (simp add: is_arg_min_linorder)
  then have "?f v - ?f w \<ge>  2*k/2*(norm (v - w))\<^sup>2" 
    using strongly_convex_min[of H ?f "2*k" w v]  
    using ridge_convex  `w \<in> H` convH assms ridge_strong_convex by blast
  then show "?f v - ?f w \<ge> k*norm (v - w)^2" by auto
qed

text\<open>Equation 13.8\<close>
lemma ridge_fun_diff:
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes "i\<in>{0..<n}"
  assumes "v \<in> H"
  assumes "u\<in> H" 
  shows "ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S(i:=z)) k v - ridge_fun (S(i:=z)) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n "
proof -
  have "ridge_fun S k v - ridge_fun S k u = 
     (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v - 
      (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u" by auto
  also have "\<dots> = 
       train_err_loss (S(i:=z)) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S(i:=z)) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2" using fun_upd_error
    using \<open>i \<in> {0..<n}\<close> assms by auto
  also have "\<dots> =
        (train_err_loss (S(i:=z)) n l v) +  k * (norm v)^2 
    - (train_err_loss (S(i:=z)) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n"
    by (smt add_divide_distrib)
  also have " \<dots> =
  (train_err_loss (S(i:=z)) n l v) +  k * (norm v)^2 
    - (train_err_loss (S(i:=z)) n l u) - k * (norm u)^2
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
    by (smt add_divide_distrib)
  finally show ?thesis by auto 
qed

text\<open>Equation 13.9\<close>
lemma ridge_min_diff :
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes "i\<in>{0..<n}"
  assumes v_Si_argmin: "v \<in> ridge_argmin (S(i:=z)) k"
  assumes u_S_argmin: "u \<in> ridge_argmin S k"
  shows " ridge_fun S k v - ridge_fun S k u \<le> 
              (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof -
  have "v \<in> H" 
    using assms ridge_argmin_def by (simp add: is_arg_min_def)
  have "u \<in> H"
    using assms ridge_argmin_def by (simp add: is_arg_min_def)
  have "is_arg_min (ridge_fun (S(i:=z)) k) (\<lambda>s. s\<in>H) v"
    using v_Si_argmin ridge_argmin_def by auto 
  then have "ridge_fun (S(i:=z)) k v \<le> ridge_fun (S(i:=z)) k u"
    by (metis \<open>u \<in> H\<close> is_arg_min_linorder)
  then have diff_le_0: " ridge_fun (S(i:=z)) k v - ridge_fun (S(i:=z)) k u \<le> 0" by auto

  have "ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S(i:=z)) k v - ridge_fun (S(i:=z)) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
    using ` i \<in> {0..<n}` ridge_fun_diff `v \<in> H` `u \<in> H` assms by blast
  then show ?thesis using diff_le_0 by linarith
qed


text\<open>Equation 13.10\<close>
lemma ridge_stable:
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes "i\<in>{0..<n}"
  assumes v_Si_argmin: "v \<in> ridge_argmin (S(i:=z)) k"
  assumes u_S_argmin: "u \<in> ridge_argmin S k"
  shows "k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof -
  have "v \<in> H" using v_Si_argmin ridge_argmin_def  by (simp add: is_arg_min_def)
  then have "  k * norm(v - u)^2 \<le> ridge_fun S k v - ridge_fun S k u" 
    using u_S_argmin ridge_diff_ge_dist assms by blast
  also have " \<dots> \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
    using `i\<in> {0..<n}` u_S_argmin v_Si_argmin ridge_min_diff assms by blast
  finally show ?thesis by auto
qed

end

text \<open>We extend the convex loss locale by assuming the loss function is \<rho>-lipschitz 
and integrable.\<close>
locale lipschitz_ridge_and_convex_loss =
  ridge_and_convex_loss +
  fixes \<rho> :: real
  assumes rho_pos: "\<rho> > 0"
  assumes lipschitz : "\<forall>y\<in>D . \<rho>-lipschitz_on H  (\<lambda> h. l h y)"
  assumes integrable_l: "\<forall>h\<in>H. integrable D (\<lambda> z. l h z)"
begin

text \<open>One changed data point in our set of samples, result in small change that is 
bounded from above by (2*\<rho>^2)/(k*n)\<close>
lemma lipschitz_loss_diff_bounded: 
  fixes S
  assumes "S \<in> Samples n D"
  assumes "i\<in>{0..<n}"
  assumes "z\<in>D" 
  shows "(l (ridge_mine (S(i:=z)) k)  (S i)) - (l (ridge_mine S k) (S i)) \<le> (2*\<rho>^2)/(k*n)"
proof -
  let ?v = "(ridge_mine (S(i:=z)) k)"
  let ?u = "ridge_mine S k"
  show ?thesis
  proof (cases "?u=?v")
    case True
    then show ?thesis
      using k_pos by auto
  next
    case False
    have  assm1: "?v \<in> ridge_argmin (S(i:=z)) k"
      using k_pos  fun_upd_is_samples  assms by (simp add: ridge_min_el_is_argmin)
    have assm2: "?u \<in> ridge_argmin S k"
      using ridge_min_el_is_argmin k_pos assms  by blast
    let ?loss_zi = "(\<lambda> h. l h (S i))"
    let ?loss_z =  "(\<lambda> h. l h z)"
    have "\<rho> \<ge> 0"  
      using lipschitz  lipschitz_on_def \<open>z \<in> set_pmf D\<close> by blast
    have assm3: " \<rho>-lipschitz_on H  (\<lambda> h. l h z)" 
      using lipschitz \<open>z \<in> set_pmf D\<close>  by auto
    have "S i \<in> D" using element_of_sample_in_dataset assms `i \<in> {0..<n}` by simp
    then have assm4:" \<rho>-lipschitz_on H  (\<lambda> h. l h (S i))" using assm3 lipschitz by auto
    have " norm(?v-?u) > 0" using `?u \<noteq> ?v`  by auto

    have "?u \<in> H"
      using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "?v \<in> H"
      using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have " dist (?loss_zi ?v) (?loss_zi ?u) \<le> \<rho> * dist ?v ?u" 
      using `?v\<in>H` `?u\<in>H` assm4 lipschitz_onD by fastforce
    moreover have "(?loss_zi ?v) - (?loss_zi ?u) \<le> dist (?loss_zi ?v)  (?loss_zi ?u)" 
      by (simp add: dist_norm)
    ultimately  have 1:"(?loss_zi ?v) - (?loss_zi ?u) \<le>  \<rho> * dist ?v ?u" by auto

    have " dist (?loss_z ?u) (?loss_z ?v) \<le> \<rho> * dist ?u ?v" 
      using `?v\<in>H` `?u\<in>H` assm3 lipschitz_onD by fastforce
    moreover have "(?loss_z ?u) - (?loss_z ?v) \<le> dist (?loss_z ?u) (?loss_z ?v)" 
      by (simp add: dist_norm)
    moreover have "l (ridge_mine S k) z - l (ridge_mine (S(i:=z)) k) z \<le>
                   \<rho> * dist (ridge_mine S k) (ridge_mine (S(i:=z)) k)"
      using dual_order.trans calculation(1) calculation(2) by blast
    ultimately  have 2: "(?loss_z ?u) - (?loss_z ?v) \<le>  \<rho> * dist ?v ?u" 
      by (simp add: dist_commute)

    then have "(?loss_zi ?v) - (?loss_zi ?u) + (?loss_z ?u) - (?loss_z ?v) \<le>
                 2 * \<rho> * dist ?v ?u" using 1 2 by auto
    then have "(((?loss_zi ?v) - (?loss_zi ?u)) + ((?loss_z ?u) - (?loss_z ?v))) / n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" using n_pos by (simp add: divide_right_mono)

    then have "((?loss_zi ?v) - (?loss_zi ?u))/n + ((?loss_z ?u) - (?loss_z ?v)) / n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" by (simp add: add_divide_distrib)
    then have " k * norm(?v - ?u)^2  \<le> (2 * \<rho> * dist ?v ?u) / n" using ridge_stable assms
      by (smt \<open>i \<in> {0..<n}\<close> assm1 assm2)
    then have " k * norm(?v - ?u)^2/k \<le> (2 * \<rho> * norm(?v - ?u) / n) / k" 
      using k_pos  divide_right_mono dist_norm by smt
    then have  " norm(?v - ?u)^2 \<le> 2 * \<rho> * norm(?v - ?u) / (n * k)"
      using k_pos by auto
    then have "norm(?v - ?u)^2 /norm(?v - ?u) \<le> (2 * \<rho> * norm(?v - ?u)/(n * k)) / norm(?v - ?u)"
      using  `norm(?v - ?u) > 0` by (metis divide_le_cancel norm_not_less_zero)
    then have "norm (?v - ?u)* (norm(?v - ?u)/norm(?v - ?u)) \<le> 
            2 * \<rho> * (norm(?v - ?u)/norm(?v-?u)) / (n*k)"
      by (smt \<open>0 < norm (ridge_mine (S(i:=z)) k - ridge_mine S k)\<close> nonzero_mult_div_cancel_left
          power2_eq_square times_divide_eq_right)
    then have "norm (?v - ?u) \<le>  2 * \<rho>  / (n*k)" using \<open>0 < norm (?v - ?u)\<close> by auto
    then have "\<rho> * norm (?v - ?u) \<le> \<rho> * 2 * \<rho>  / (n*k)" using `\<rho> \<ge> 0`
      by (metis mult_left_mono semiring_normalization_rules(18) times_divide_eq_right)
    then have "\<rho> * norm (?v - ?u) \<le>  2 * \<rho> * \<rho>  / (n*k)"
      by (simp add: semiring_normalization_rules(7))
    then have "\<rho> * norm (?v - ?u) \<le>  2 * \<rho> ^2  / (n*k)" using power2_eq_square
      by (metis mult.commute semiring_normalization_rules(19))
    then show " (l ?v (S i)) - (l ?u (S i)) \<le> (2*\<rho>^2)/(k*n)" using 1 
      by (simp add: dist_norm mult.commute)
  qed
qed

text \<open>Since the loss function is integrable --> the minimums of l over D is integrable\<close>
lemma loss_min_over_samples_integrable:
  assumes "S \<in> (Samples n D)"
  shows "integrable D (\<lambda> z. l (ridge_mine S k) z)" 
proof -
  have "(ridge_mine S k) \<in> H" 
    using argmin_in_hypotheis_set assms by blast
  then show "integrable D (\<lambda> z. l (ridge_mine S k) z)" 
    using integrable_l by auto
qed

text \<open>prediction error is integrable over the possible samples, 
because it is a constant in it\<close>
lemma pred_err_over_samples_integrable:
  "integrable (Samples n D) (\<lambda> S. pred_err_loss D l h)" 
  unfolding pred_err_loss_def by auto


lemma expect_as_last:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  shows " measure_pmf.expectation (Samples m D) (\<lambda> S.  l h (S (m-1))) =
                      measure_pmf.expectation D (\<lambda> z. l h z)"
proof -
  let ?f = "(\<lambda> S z. l h z)"
  have f_nn : "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. ?f S z \<ge> 0" 
    using l_nn `h\<in>H` by auto
  have 1:"measure_pmf.expectation (Samples (m-1) D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. ?f S z)) =
      measure_pmf.expectation (Samples m D) (\<lambda> Sz. ?f (trunc_fun Sz (m-1)) (Sz (m-1)))"
    using add_sample_expectation[of "m-1" ?f] f_nn assms(2) integrable_l  l_nn
    by (simp add: m_pos)
  have "measure_pmf.expectation (Samples m D)(\<lambda>S. measure_pmf.expectation D (l h)) =
       measure_pmf.expectation D (l h)" by auto
  then show ?thesis using 1 by simp
qed

lemma integrable_as_last:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  shows "integrable (Samples m D) (\<lambda> S.  l h (S (m-1))) =
                     integrable D (\<lambda> z. l h z)"
proof -
  let ?f = "(\<lambda> S z. l h z)"
  have f_nn : "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. ?f S z \<ge> 0" using l_nn `h\<in>H` by auto
  have 1:"integrable (Samples (m-1) D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. ?f S z)) =
      integrable (Samples m D) (\<lambda> Sz. ?f (trunc_fun Sz (m-1)) (Sz (m-1)))"
    using add_sample_integrable[of "m-1" ?f] using  f_nn
    using assms(2) integrable_l l_nn
    by (simp add: m_pos)
  then show ?thesis using 1 
    using assms(2) integrable_l by blast
qed

text \<open>The expectaion over a datapoint from D and a datapoint from the sample set is the same\<close>
lemma expect_over_dataset_eq_sample_over_samples: 
  assumes "h\<in>H"
  assumes "i \<in> {0..<n}"
  shows "measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) =
                      measure_pmf.expectation D (\<lambda> z. l h z)"
proof -
  have "\<forall> S \<in> (Samples n D). S i \<in> D"
    using \<open>i \<in> {0..<n}\<close> element_of_sample_in_dataset by blast
  have "\<forall> z \<in> D. \<exists> S \<in> (Samples n D). S i = z"
  proof
    fix z
    assume "z\<in>D"
    obtain S where "S\<in> Samples n D"  
      by (meson set_pmf_not_empty some_in_eq)
    then have 1:"(S(i:= z)) \<in> Samples n D" 
      using fun_upd_is_samples \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    then have " (S(i:=z)) i = z" by auto
    then show "\<exists> S \<in> (Samples n D). S i = z" 
      using "1" by blast
  qed
  then show "measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) = 
                      measure_pmf.expectation D (\<lambda> z. l h z)"
    using expect_sample_same[of n h] expect_as_last[of n h] `h\<in>H`    
    using \<open>i \<in> {0..<n}\<close> n_pos by metis
qed

lemma integrable_over_dataset_eq_sample_over_samples: 
  assumes "h\<in>H"
  assumes "i \<in> {0..<n}"
  shows "integrable (Samples n D) (\<lambda> S.  l h (S i)) =
                      integrable D (\<lambda> z. l h z)"
proof -
  have "\<forall> S \<in> (Samples n D). S i \<in> D"
    using \<open>i \<in> {0..<n}\<close> element_of_sample_in_dataset by blast
  have "\<forall> z \<in> D. \<exists> S \<in> (Samples n D). S i = z"
  proof 
    fix z
    assume "z\<in>D"
    obtain S where "S\<in> Samples n D"  
      by (meson set_pmf_not_empty some_in_eq)
    then have 1:"(S(i:=z)) \<in> Samples n D" 
      using fun_upd_is_samples \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    then have " (S(i:=z)) i = z"  by auto
    then show "\<exists> S \<in> (Samples n D). S i = z" 
      using "1" by blast
  qed
  then show "integrable (Samples n D) (\<lambda> S.  l h (S i)) = 
                      integrable D (\<lambda> z. l h z)"
    using integrable_sample_same[of n h] integrable_as_last[of n h] `h\<in>H`    
    using \<open>i \<in> {0..<n}\<close> n_pos by metis
qed

lemma train_err_integrable_fixed_hypotheis:
  assumes "h\<in>H"
  shows "integrable (Samples n D) (\<lambda> S. train_err_loss S n l h)"
  unfolding train_err_loss_def
proof -
  let ?f = " (\<lambda> i S. l h (S i))"
  let ?M = " (Samples n D)"
  have "finite {0..<n}" by auto
  have 1: "\<forall>S\<in>set_pmf ?M. \<forall>i\<in>{0..<n}. 0 \<le> ?f i S "
    using l_nn `h\<in>H`  element_of_sample_in_dataset by blast
  have "\<forall> i \<in> {0..<n}. integrable (Samples n D) (?f i) =
                      integrable D (\<lambda> z. l h z)"
    using integrable_over_dataset_eq_sample_over_samples `h\<in>H` by auto
  then have "\<forall> i \<in> {0..<n}. integrable (Samples n D) (\<lambda> x. (?f i) x)" 
    using integrable_l  using assms by blast
  then have " integrable (Samples n D) (\<lambda>x. \<Sum>i\<in>{0..<n}. (?f i) x)"
    using integrable_sum_iff[of ?M "{0..<n}" ?f] by auto
  then show "integrable (Samples n D) (\<lambda>x. (\<Sum>i\<in>{0..<n}. (?f i) x) / n)"
    by auto
qed

text \<open>The expectation of the training error is equal to the prediction error!\<close>
lemma expectation_train_err:
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D) (\<lambda> S. train_err_loss S n l h) =
           pred_err_loss D l h"
proof -
  let ?I = "{0..<n}"
  let ?Dn = "Samples n D"
  let ?f = "(\<lambda> i. (\<lambda> S. l h (S i)))"
  have fin_I: "finite ?I" by auto
  have non_empty_I: "?I \<noteq> {}" using n_pos by auto

  have "measure_pmf.expectation ?Dn (\<lambda> S. train_err_loss S n l h) = 
   measure_pmf.expectation ?Dn (\<lambda> S. sum (\<lambda>i. l h (S i)) ?I / n)"
    unfolding train_err_loss_def by auto
  also have " \<dots> = measure_pmf.expectation ?Dn
     (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l h (S i)))"
    using  non_empty_I by (simp add: integral_pmf_of_set)
  also have " \<dots> = measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i)))"
  proof -
    have I_swap: 
      "\<forall> i\<in> ?I. \<forall> j \<in> ?I. measure_pmf.expectation ?Dn (\<lambda> S. ?f i S) =
       measure_pmf.expectation ?Dn (\<lambda> S. ?f j S)"
      using expect_over_dataset_eq_sample_over_samples `h\<in>H` 
      by auto
    have  f_nn: "\<forall> S \<in> (set_pmf ?Dn). \<forall> i \<in> ?I. ?f i S \<ge> 0"
      using   element_of_sample_in_dataset l_nn `h\<in>H` by blast
    show ?thesis
      using swap_set_expectation[of ?Dn ?I ?f] I_swap f_nn fin_I non_empty_I
      by blast
  qed
  also have "\<dots> = sum  (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i))) ?I / card ?I" 
    using integral_pmf_of_set non_empty_I by blast
  also have "\<dots> = sum (\<lambda> i. measure_pmf.expectation D (\<lambda> z. l h z)) ?I / card ?I"
    using expect_over_dataset_eq_sample_over_samples `h\<in>H` by auto
  also have "\<dots> = measure_pmf.expectation D (\<lambda> z. l h z)" 
    using non_empty_I by auto
  finally show ?thesis unfolding pred_err_loss_def  by auto 
qed

text \<open>The training error is integrable.\<close>
lemma train_err_integrable:
  shows " integrable (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k))"
proof -
  from nnH obtain h where "h\<in>H" by blast 
  let ?f = " (\<lambda> i S. l (ridge_mine S k) (S i))"
  let ?g = "(\<lambda> S  z. l (ridge_mine S k) z)"
  let ?M = "(Samples n D)"
  have nn: "\<And>S. S\<in>set_pmf ?M \<Longrightarrow> \<forall>i\<in>{0..<n}. 0 \<le> ?f i S "
    using l_nn element_of_sample_in_dataset argmin_in_hypotheis_set by blast

  {
    fix S
    assume S: "S\<in>Samples n D"
    have *: "train_err_loss S n l (ridge_mine S k)
                 \<le> train_err_loss S n l h +  k * norm ( h )^2" 
    proof -
      let ?w = " (ridge_mine S k)"
      have " train_err_loss S n l ?w \<le> train_err_loss S n l h + k * norm ( h )^2"
      proof -
        have "is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) (ridge_mine S k)"
          unfolding ridge_mine_def unfolding ridge_argmin_def 
          by (metis S mem_Collect_eq ridge_argmin_def ridge_min_el_is_argmin verit_sko_ex_indirect)

        then have "(ridge_fun S k)  (ridge_mine S k) \<le> (ridge_fun S k) h" 
          using `h\<in>H` 
          by (simp add: is_arg_min_linorder)
        then have "train_err_loss S n l ?w  + k* norm((ridge_mine S k))^2
                   \<le> train_err_loss S n l h + k * norm ( h )^2"
          unfolding ridge_fun.simps by auto
        then show "train_err_loss S n l ?w 
                  \<le> train_err_loss S n l h + k * norm ( h )^2" using k_pos
          by (smt mult_nonneg_nonneg zero_le_power2)
      qed
      then show "train_err_loss S n l (ridge_mine S k) \<le>
                                train_err_loss S n l h +  k * norm ( h )^2"
        by blast
    qed
    have " train_err_loss S n l (ridge_mine S k) \<ge> 0" 
      by (simp add: train_err_loss_nn nn S)
    then have  "(train_err_loss S n l (ridge_mine S k)) =
          (norm (train_err_loss S n l (ridge_mine S k)))" 
      by simp
    then have 12:" (norm (train_err_loss S n l (ridge_mine S k)))
      \<le> norm (train_err_loss S n l h + k * (norm h)\<^sup>2)" 
      using * by auto
  } note bounded = this
  then have integrable_ridge_fun:"integrable ?M (\<lambda> S.  train_err_loss S n l h + k * norm ( h )^2)" 
    apply(intro Bochner_Integration.integrable_add) 
    subgoal by(rule train_err_integrable_fixed_hypotheis[OF `h\<in>H`])
    subgoal by auto
    done
  show "integrable (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k))" 
    apply(rule Bochner_Integration.integrable_bound)
      apply(rule integrable_ridge_fun)
    using bounded
    by (auto intro: AE_pmfI )   
qed


lemma  samples_small_update_bounded:
  assumes i_in_I: "i\<in>{0..<n}"
  assumes  "S\<in> (Samples (n+1) D)"
  shows "(l (ridge_mine (swapped_fun S i n) k) (S i)) - (l (ridge_mine S k) (S i)) \<le> (2*\<rho>^2)/(k*n)"
proof -
  let ?const = "(2*\<rho>^2)/(k*n)"
  let ?Dn1 = "(Samples (n+1) D)"
  let ?trunc_upd = "(trunc_fun S n)(i := (S n))"
  let ?ridge_min = "(\<lambda> f. (l (ridge_mine f k) (S i)))"
  have "i \<in> {0..<n+1}" using `i\<in>{0..<n}` by auto

  have 2:"(trunc_fun S n i) = S i" using `i\<in> {0..<n}`
    unfolding trunc_fun_def by auto
  have "n \<in> {0..< n+1}" by auto

  then have "S n \<in> D" 
    using element_of_sample_in_dataset `S \<in> ?Dn1` 
    by blast
  moreover have " ?ridge_min ?trunc_upd - ?ridge_min (trunc_fun S n) \<le> ?const"
    using  lipschitz_loss_diff_bounded 
 assms 2  trunc_fun_in_smaller_samples calculation(1) by metis
  moreover have "?ridge_min ?trunc_upd = ?ridge_min (S(i := (S n)))" 
    using "2" fun_upd_triv fun_upd_twist trunc_fun_def 
    by (metis (mono_tags, hide_lams) fun_upd_upd truncated_fun_has_same_min)
  moreover have "?ridge_min (trunc_fun S n) = ?ridge_min S"
    by (metis  truncated_fun_has_same_min)
  ultimately show "?ridge_min (swapped_fun S i n) - ?ridge_min S \<le> ?const"
    by (simp add: ridge_index_swap_same)
qed

text \<open>We have the loss function with minimum value is replace one stable for each index i.\<close>
lemma replace_one_stable: 
  assumes i_in_I: "i\<in>{0..<n}"
  shows "measure_pmf.expectation (Samples (n+1) D) 
  (\<lambda> S. (l (ridge_mine (swapped_fun S i n) k) (S i)) - (l (ridge_mine S k) (S i))) \<le> (2*\<rho>^2)/(k*n)"
proof -
  let ?ridge_min_S = "(\<lambda> S f. (l (ridge_mine f k) (S i)))"
  let ?const = "(2*\<rho>^2)/(k*n)"
  let ?Dn1 = "(Samples (n+1) D)"

  have finite_M:"finite_measure ?Dn1" by simp
  have measure_M:"measure ?Dn1 (space ?Dn1) = 1" by simp
  have pos_const: "(2*\<rho>^2)/(k*n) \<ge> 0" using k_pos by auto

  have "(2*\<rho>^2)/k \<ge> 0"  using k_pos by auto
  then have "(2*\<rho>^2)/(k*(n+1)) \<le> ?const" 
    using n_pos frac_le by fastforce

  have "AE S in ?Dn1.  
          ?ridge_min_S S (swapped_fun S i n) - ?ridge_min_S S S \<le>  ?const "
    using  samples_small_update_bounded AE_measure_pmf_iff assms by blast

  then have "integral\<^sup>L ?Dn1 (\<lambda> S. ?ridge_min_S S (swapped_fun S i n) - ?ridge_min_S S S) \<le> ?const" 
    using finite_M measure_M pos_const 
      integral_bellow_const[of "(\<lambda> S. ?ridge_min_S S (swapped_fun S i n) - ?ridge_min_S S S)"
        "?const" "?Dn1"] by simp
  then show ?thesis by auto
qed


text \<open>Corollary 13.6 part 1:
The Ridge loss minimization is  on-average-replace-one-stable\<close>
lemma replace_one_stable_expectation:
      "measure_pmf.expectation (Samples (n+1) D)
         (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n})
         (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) - (l  (ridge_mine S k) (S i)))) \<le> 
                        (2*\<rho>^2)/(k*n)"
proof -
  let ?Dn1 = "(Samples (n+1) D)"
  let ?f = "(\<lambda> S. (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))))" 
  let ?const = "(2*\<rho>^2)/(k*n)"
  have M_finite: "finite_measure ?Dn1" by auto
  have measure_M:"measure (Samples (n+1) D) (space (Samples (n+1) D)) = 1" by simp
  have pos_const: "?const \<ge> 0" using k_pos by auto
  have "\<forall> S \<in> ?Dn1.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> ?const"
  proof (rule)
    fix S
    assume "S\<in> ?Dn1"
    have "{0..<n} \<noteq> {}" using n_pos by auto
    have "\<forall> i \<in> {0..<n}. ?f S i \<le> ?const"
      using samples_small_update_bounded `S\<in> ?Dn1` by auto
    then have "\<forall> i \<in> {0..<n}. ?f S i \<le> ?const" 
      using n_pos  by (simp add: frac_le k_pos)
    then have "sum (\<lambda> i. ?f S i) {0..<n} \<le> n * ?const"
      using sum_bounded_const[of n "(\<lambda> i. ?f S i)" "?const"] `{0..<n} \<noteq> {}` 
      by auto
    then have "sum (\<lambda> i. ?f S i) {0..<n} / n \<le> n * ?const / n"
      using divide_right_mono of_nat_0_le_iff by blast
    then have "sum (\<lambda> i. ?f S i) {0..<n} / card {0..<n} \<le> ?const"
      using n_pos by auto
    then show " integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> ?const"
      by (metis (no_types, lifting) \<open>{0..<n} \<noteq> {}\<close> finite_atLeastLessThan integral_pmf_of_set)

  qed
  then have "AE S in (Samples (n+1) D).  
     integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> ?const"
    using AE_measure_pmf_iff by blast

  then show " integral\<^sup>L (Samples (n+1) D)
     (\<lambda> S.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i)) \<le> ?const" 
    using M_finite measure_M pos_const 
      integral_bellow_const[of " (\<lambda> S. integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i))"
        ?const ?Dn1] by simp
qed

lemma integrable_swap_same:
  assumes "i \<in> {0..<n}"
  assumes pred_err_integrable:
    "integrable (Samples n D) (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  shows "integrable (Samples (n+1) D) (\<lambda> S. l (ridge_mine (swapped_fun S i n) k) (S i))"
proof -
  let ?Dn = "Samples n D"
  let ?Dn1 = "Samples (n+1) D"
  let ?I = "{0..<n}"
  let ?l_swapped = "(\<lambda> i. (\<lambda> S. l (ridge_mine (swapped_fun S i n) k) (S i)))"
  let ?l_trunc = "(\<lambda> S. (\<lambda> z. l (ridge_mine (trunc_fun S n) k) z))"
  let ?l_Si = "(\<lambda> S. (\<lambda>i. l (ridge_mine S k) (S i)))"
  let ?pred_err = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"

  have "integrable ?Dn (\<lambda>S. measure_pmf.expectation D (\<lambda> z. l (ridge_mine S k) z))" 
    using pred_err_integrable
    unfolding pred_err_loss_def by auto
  then have "integrable ?Dn1 (\<lambda> S. ?l_trunc S (S n))"
    using add_sample_integrable[of n "(\<lambda> S z. l (ridge_mine S k) z)"]
      l_nn by (simp add: argmin_in_hypotheis_set loss_min_over_samples_integrable)
  then have "integrable  ?Dn1 (\<lambda> S. ?l_Si S n)"
    by (simp add: truncated_fun_has_same_min)
  then have "integrable (measure_pmf (Samples (n + 1) D))
     (\<lambda>x. l (ridge_mine (swapped_fun x i (n + 1 - 1)) k) (swapped_fun x i (n + 1 - 1) n))" 
    using integrable_func_swap_same[of "n+1" "(\<lambda> S. ?l_Si S n)" i]
    using \<open>i \<in> {0..<n}\<close> l_nn min_of_Dn1_in_H element_of_sample_in_dataset by auto
  then show " integrable ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)" unfolding swapped_fun_def
    by auto
qed

text \<open>Corollary 13.6 part 2:
from lemma 13.2 and that the RLM rule is on-average-replace-one-stable 
we can conclude oracles inequality:
The expectation of prediction and training loss of argmins is bounded from above: 
  E_Dm [L_D (A(S))− L_S (A(S))] \<le> (2*\<rho>^2)/(k*n)\<close>
lemma lipschitz_stable:
  assumes pred_err_integrable:
    "integrable (Samples n D) (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  shows "measure_pmf.expectation (Samples n D) 
        (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k))
                        \<le> (2*\<rho>^2)/(k*n)"
proof -
  let ?Dn = "Samples n D"
  let ?Dn1 = "Samples (n+1) D"
  let ?I = "{0..<n}"
  let ?pmfI = "(pmf_of_set ?I)"
  let ?l_swapped = "(\<lambda> i. (\<lambda> S. l (ridge_mine (swapped_fun S i n) k) (S i)))"
  let ?l_trunc = "(\<lambda> S. (\<lambda> z. l (ridge_mine (trunc_fun S n) k) z))"
  let ?l_Si = "(\<lambda> S. (\<lambda>i. l (ridge_mine S k) (S i)))"
  let ?pred_err = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  have fin_I:"finite ?I" by auto
  have non_empty_I:"?I \<noteq> {}" 
    using n_pos by auto

  have "(\<forall> i \<in> ?I.  integrable ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)) \<longleftrightarrow> 
      integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x))"
    using  integrable_sum_iff[of ?Dn1 ?I "(\<lambda> i Sz. ?l_swapped i Sz)"] 
      fin_I l_nn pmf_swapped_fun_values_same  learning_basics_loss_axioms
    by (smt add_diff_cancel_right' atLeastLessThan_iff element_of_sample_in_dataset
        min_of_Dn1_in_H n_pos set_pmf_iff trans_less_add1)

  then have "integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x))" 
    using integrable_swap_same assms  by auto
  then have 4:"integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x)/card ?I)"
    by auto
  have "(\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x)/card ?I) =  (\<lambda> x. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i x))"
    using  fin_I non_empty_I
    by (simp add: integral_pmf_of_set[of ?I ]) 

  then have 5:"integrable ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )" 
    using 4 by auto

  have "\<forall>S. \<forall>i\<in>?I. (trunc_fun S n) i = S i"  using  trunc_fun_def by auto 
  then  have  "\<forall>S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (trunc_fun S n i)) =
               integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))" 
    by (metis (no_types, lifting) fin_I non_empty_I same_integral_restricted set_pmf_of_set)
  then have 6:"(\<lambda> S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (trunc_fun S n i))) =
            (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))) " by auto

  then have 7: "integrable ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> _.  integral\<^sup>L ?pmfI (?l_Si S))) =
      integrable ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (trunc_fun S n i)))"
    using 
      integrable_uniform uniform_nn add_sample_integrable[of n " (\<lambda> S. (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S)))"]   by blast

  have "card ?I = n" by auto
  then have "\<forall> S. integral\<^sup>L ?pmfI (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (?l_Si S) ?I) / card ?I"
    using integral_pmf_of_set `finite ?I` `?I \<noteq> {}` by blast
  then have "\<forall> S. train_err_loss S n l (ridge_mine S k) = integral\<^sup>L ?pmfI (?l_Si S)" 
    using `card ?I = n` train_err_loss_def by force

  then have "integrable ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))" using
      train_err_integrable 6 7 truncated_fun_has_same_min by auto

  then have integrable_Si:"integrable (Samples (n+1) D) 
      (\<lambda> S.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
    by auto
  have integrable_swapped: "integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i))))"
    using 5 by auto
  show ?thesis
    using train_val_diff replace_one_stable_expectation  integrable_Si integrable_swapped 
      pred_err_integrable  
      train_err_integrable 
    using loss_min_over_samples_integrable by presburger
qed

text \<open>corollary 13.8 - Oracle inequality
if we think of w* as a hypothesis with low risk, the bound tells us how many examples are needed so
 that A(S) will be almost as good as w*, had we known the norm of w*. In practice, however, 
we usually do not know the norm of w*\<close>
lemma oracle_inequality:
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D) (\<lambda> S.  pred_err_loss D l (ridge_mine S k)) \<le>
    pred_err_loss D l h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)"
proof -
  let ?pred_min = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  let ?train_min = "(\<lambda> S.  train_err_loss S n l (ridge_mine S k))"
  let ?Dn = "(Samples n D)"
  show ?thesis
  proof(cases "integrable ?Dn ?pred_min")
    case True
    have 1: "integral\<^sup>L ?Dn ?pred_min =
    integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) + integral\<^sup>L ?Dn  (\<lambda> S. ?pred_min S - ?train_min S)"
      using True train_err_integrable by simp
    have "integrable ?Dn ?train_min"
      using train_err_integrable by blast
    have 11:"\<forall> S \<in> ?Dn. ?train_min S \<le> train_err_loss S n l h + k * norm (h)^2"
    proof
      fix S
      assume "S\<in> ?Dn"
      have "is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) (ridge_mine S k)"
        unfolding ridge_mine_def
        unfolding ridge_argmin_def 
        by (metis `S\<in> ?Dn`  mem_Collect_eq ridge_argmin_def ridge_min_el_is_argmin someI_ex)
      then have 1: "(ridge_fun S k) (ridge_mine S k) \<le> (ridge_fun S k) h" 
        using `h\<in>H` 
        by (simp add: is_arg_min_linorder)
      then have "?train_min S  + k * norm((ridge_mine S k))^2 \<le>
               train_err_loss S n l h + k * norm ( h )^2"
        unfolding ridge_fun.simps by auto
      then show "?train_min S \<le> train_err_loss S n l h + k * norm (h)^2"
        using k_pos
        by (smt mult_nonneg_nonneg zero_le_power2)
    qed

    then have "integrable ?Dn (\<lambda> S. train_err_loss S n l h + k * norm (h)^2)" 
      using train_err_integrable_fixed_hypotheis `h\<in>H` Bochner_Integration.integrable_add by blast

    then have 2:"integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
            integral\<^sup>L ?Dn (\<lambda> S. train_err_loss S n l h + k * norm (h)^2)"
      using  train_err_integrable integral_mono_AE AE_measure_pmf_iff 11 by blast

    have "integral\<^sup>L ?Dn (\<lambda> S. train_err_loss S n l h + k * norm (h)^2) =
       integral\<^sup>L ?Dn (\<lambda> S. train_err_loss S n l h) +  integral\<^sup>L ?Dn (\<lambda> S. k * norm (h)^2)"
      using  train_err_integrable_fixed_hypotheis `h\<in>H` Bochner_Integration.integral_add by blast


    then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le> 
            integral\<^sup>L ?Dn (\<lambda> S. train_err_loss S n l h) +  integral\<^sup>L ?Dn (\<lambda> S. k * norm (h)^2)"
      using 2  by linarith

    then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
             pred_err_loss D l h + k * norm (h)^2" using expectation_train_err `h\<in>H`
      by auto
    then have "integral\<^sup>L ?Dn (\<lambda> S. ?pred_min S) \<le>
    pred_err_loss D l h + k * norm (h)^2  + integral\<^sup>L ?Dn  (\<lambda> S. ?pred_min S - ?train_min S)"
      using 1 expectation_train_err `h\<in>H` by linarith

    then show ?thesis using lipschitz_stable True by smt
  next
    case False
    have pred_expect_0:"measure_pmf.expectation ?Dn ?pred_min = 0"
      using False  not_integrable_integral_eq by blast
    have "pred_err_loss D l h \<ge> 0"
      using pred_err_loss_nn `h\<in>H` l_nn by metis

    then have "0 \<le> pred_err_loss D l h  + k * norm (h)^2  + (2*\<rho>^2)/(k*n)" 
      using k_pos by auto
    then show ?thesis using pred_expect_0 by auto
  qed
  qed

end
end