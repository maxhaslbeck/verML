theory RLM_stable
  imports  "RLM_learn" "rlm_13_02_lemma"
begin

locale ridge_and_convex_loss = learning_basics1 + 
  
assumes convl : "\<forall>y \<in> D. convex_on H (\<lambda> h. l h y)"

begin

text\<open>Show the connection between the loss for S and the loss for S_(i)\<close>
lemma S_index_error : 
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>i\<in>{0..<n}. train_err_loss S n l v =
    train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n"
proof 
  fix i assume "i \<in> {0..<n}" 
  then show "train_err_loss S n l v = 
    train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n"
  proof -
    have "(S_index S i z) i = z" unfolding S_index_def by auto
    have 1: " sum (\<lambda>j. l v (S j) ) {0..<n} - sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} =
      sum (\<lambda>j. l v (S j) - l v ((S_index S i z) j) ) {0..<n}"
      by (simp add: sum_subtractf)
    then have "sum (\<lambda>j. l v (S j) - l v ((S_index S i z) j))  {0..<n} = 
             l v (S i) - l v ((S_index S i z) i)" 
      using S_index_similar\<open>i \<in> {0..<n}\<close> sum_split by auto
    then have 2: "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} 
      +  l v (S i) - l v ((S_index S i z) i)" using 1 by auto

    then have "sum (\<lambda>j. l v (S j) ) {0..<n} = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n} 
      +  (l v (S i)) - (l v z)" using `(S_index S i z) i = z` by auto
    then have "sum (\<lambda>j. l v (S j) ) {0..<n}/n = sum (\<lambda>j. l v ((S_index S i z) j) ) {0..<n}/n 
      +  (l v (S i))/n - (l v z)/n"
      by (simp add:  add_divide_distrib diff_divide_distrib)

    then show ?thesis by (metis (mono_tags, lifting) sum.cong train_err_loss_def)
  qed
qed

lemma S_index_is_sample: 
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>i\<in>{0..<n}.\<forall>z\<in>D. S_index S i z \<in> Samples n D"
proof
  fix i
  assume "i\<in>{0..<n}"
  have "finite {0..<n}" by auto
  show "\<forall> z \<in> D. S_index S i z \<in> Samples n D"
  proof
    fix z
    assume "z\<in>D" 
    show "S_index S i z \<in> Samples n D"
    proof -
      have "pmf D z > 0" using `z\<in>D`  by (simp add: pmf_positive)
      have "pmf (Samples n D) S > 0" using S_in_D pmf_pos by (simp add: pmf_positive)
      then have " \<forall>j. j \<notin> {0..<n} \<longrightarrow> S j = undefined" using pmf_pos n_pos 
        by (meson less_le_trans zero_less_one)
      then have "\<forall>j. j \<notin> {0..<n} \<longrightarrow> (S_index S i z) j = undefined" unfolding S_index_def
        using \<open>i \<in> {0..<n}\<close> by auto
      then have 1:"pmf (Samples n D) (S_index S i z) = (\<Prod>x\<in>{0..<n}. pmf D ((S_index S i z) x))"
        unfolding Samples_def using  pmf_Pi' `finite {0..<n}` 
        by (metis (mono_tags, lifting) prod.cong)
      have "(\<Prod>x\<in>{0..<n}. pmf D ((S_index S i z) x)) > 0" 
        by (smt Probability_Mass_Function.pmf_pos S_in_D S_index_def \<open>0 < pmf D z\<close> fun_upd_other fun_upd_same prod_pos sample_in_D set_pmf_iff)
      then show ?thesis using 1 
        using set_pmf_iff by force
    qed
  qed
qed

lemma train_err_loss_convex:
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "convex_on H (train_err_loss S n l)"
  using train_err_loss_if_convex convl
  using S_in_D train_err_loss_convex by blast

lemma ridge_convex: 
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "strong_convex_on H (ridge_fun S k) (2*k)"
proof -
  have "strong_convex_on H (\<lambda> w. k * (norm w)*(norm w)) (2*k)" using sq_norm_strong_convex 
    by blast
  moreover  have  "(\<lambda> w. k * (norm w)*(norm w)) = (\<lambda> w. k * (norm w)^2)" using power2_eq_square 
    by (simp add: semiring_normalization_rules(17) semiring_normalization_rules(29))

  ultimately  have "strong_convex_on H (\<lambda> w. k * (norm w)^2) (2*k)" using 
      strong_conv_if_eq by auto

  then have "strong_convex_on H (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) (2*k)" 
    using strong_convex_sum train_err_loss_convex add.commute
    by (metis assms)
  then show ?thesis by auto
qed

text\<open>Equation 13.7\<close>
lemma ridge_stable1: 
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>v \<in> H. w \<in> (ridge_argmin S k) \<longrightarrow>
    ridge_fun S k v - ridge_fun S k w \<ge>  k * norm(v - w)^2"
proof
  let ?f = "ridge_fun S k"
  fix v
  assume 1:"v \<in> H"
  show "w \<in> (ridge_argmin S k) \<longrightarrow> 
      ?f v - ?f w \<ge>  k * norm(v - w)^2"
  proof 
    assume "w \<in> (ridge_argmin S k)"
    show "?f v - ?f w \<ge>  k * norm(v - w)^2"
    proof -
      have 2:"is_arg_min ?f (\<lambda>s. s\<in>H) w"  using `w \<in> (ridge_argmin S k)` ridge_argmin_def by blast
      then have 3: "w \<in> H"  by (simp add: is_arg_min_def)
      have 4: "\<forall>y\<in>H. (?f w \<le> ?f y)" using is_arg_min_linorder 2 by metis
      have "?f v - ?f w \<ge>  2*k/2*(norm (v - w))\<^sup>2" 
        using strongly_convex_min[of H ?f "2*k" w v]  ridge_convex 3 4 1 convH assms  by blast
      then show "?f v - ?f w \<ge> k*norm (v - w)^2" by auto
    qed
  qed
qed

text\<open>Equation 13.8\<close>
lemma ridge_fun_diff:
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>i\<in>{0..<n}. \<forall>v \<in> H. \<forall> u\<in> H. \<forall>z.
    ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n "
proof (rule)+
  fix i assume "i \<in> {0..<n}"
  fix v assume "v \<in> H" 
  fix u assume "u \<in> H" 
  fix z 
  show "ridge_fun S k v - ridge_fun S k u = 
      ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n " 
  proof -
    have "ridge_fun S k v = (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v" by simp
    moreover have "ridge_fun S k u = (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u" by simp

    ultimately  have "ridge_fun S k v - ridge_fun S k u = 
     (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v - 
      (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u" by auto
    also have "(train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) v - 
      (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) u = 
      (train_err_loss S n l v - train_err_loss S n l u) +
      k * (norm v)^2  -  k * (norm u)^2" by auto
    also have "(train_err_loss S n l v - train_err_loss S n l u) +
      k * (norm v)^2  -  k * (norm u)^2 = 
       train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index S i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2" using S_index_error
      using \<open>i \<in> {0..<n}\<close> assms by auto
    also have "train_err_loss (S_index S i z) n l v + (l v (S i))/n - (l v z)/n 
       - (train_err_loss (S_index S i z) n l u + (l u (S i))/n - (l u z)/n)   
      +  k * (norm v)^2  -  k * (norm u)^2 = 
       (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n"by simp
    also have "  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z)/n - (l v z)/n =
        (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    also have "  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i))/n - (l u (S i))/n  + (l u z - l v z)/n =
  (train_err_loss (S_index S i z) n l v) +  k * (norm v)^2 
    - (train_err_loss (S_index S i z) n l u) - k * (norm u)^2
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      by (smt add_divide_distrib)
    finally show ?thesis by auto 
  qed
qed

text\<open>Equation 13.9\<close>
lemma ridge_min_diff :
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>i\<in>{0..<n}. \<forall>z.
                        v \<in> ridge_argmin (S_index S i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                        ridge_fun S k v - ridge_fun S k u \<le> 
                        (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index S i z) k"
  assume assm2: "u \<in> ridge_argmin S k"
  show "ridge_fun S k v - ridge_fun S k u \<le> 
         (l v (S i) - l u (S i))/n  + (l u z - l v z)/n" 
  proof -
    have "v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "ridge_fun (S_index S i z) k v \<le> ridge_fun (S_index S i z) k u"
    proof - 
      have "is_arg_min (ridge_fun (S_index S i z) k) (\<lambda>s. s\<in>H) v"
        using `v \<in> ridge_argmin (S_index S i z) k` ridge_argmin_def by auto 
      then show ?thesis 
        by (metis \<open>u \<in> H\<close> is_arg_min_linorder)
    qed
    then have 1: " ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u \<le> 0" by auto
    have "ridge_fun S k v - ridge_fun S k u = 
    ridge_fun (S_index S i z) k v - ridge_fun (S_index S i z) k u
    + (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      using ` i \<in> {0..<n}` ridge_fun_diff `v \<in> H` `u \<in> H` assms by blast
    then show ?thesis using 1 by linarith
  qed
qed

text\<open>Equation 13.10\<close>
lemma ridge_stable:
fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
assumes S_in_D: "S \<in> Samples n D"
shows "\<forall>i\<in>{0..<n}. \<forall>z.
                        v \<in> ridge_argmin (S_index S i z) k \<longrightarrow>
                        u \<in> ridge_argmin S k \<longrightarrow>
                k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z
  assume assm1: "v \<in> ridge_argmin (S_index S i z) k"
  assume assm2: "u \<in> ridge_argmin S k"
  show "k * norm(v - u)^2 \<le> (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
  proof -
    have "u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    then have "  k * norm(v - u)^2 \<le>ridge_fun S k v - ridge_fun S k u" 
      using assm2 ridge_stable1 assms by blast
    also have " ridge_fun S k v - ridge_fun S k u \<le> 
                        (l v (S i) - l u (S i))/n  + (l u z - l v z)/n"
      using `i\<in> {0..<n}` assm1 assm2 ridge_min_diff assms by blast
    finally show ?thesis by auto
  qed
qed
end

locale lipschitz_ridge_and_convex_loss =
  ridge_and_convex_loss +
  fixes \<rho> :: real
  assumes rho_pos: "\<rho> > 0"
  assumes lipschitz : "\<forall>y\<in>D . \<rho>-lipschitz_on H  (\<lambda> h. l h y)"
  assumes integrable_l: "\<forall>h\<in>H. integrable D (\<lambda> z. l h z)"
begin

lemma lipschitz_loss_diff_bounded: 
  fixes S
  assumes "S \<in> Samples n D"
  shows "\<forall>i\<in>{0..<n}. \<forall>z\<in>D.
                        (l (ridge_mine (S_index S i z) k)  (S i)) - 
            (l (ridge_mine S k) (S i))
                         \<le> (2*\<rho>^2)/(k*n)"
proof (rule)+
  fix i assume " i \<in> {0..<n}"
  fix z assume " z \<in> D"
  let ?v = "(ridge_mine (S_index S i z) k)"
  let ?u = "ridge_mine S k"

  show "(l ?v (S i)) - (l ?u (S i)) \<le> (2*\<rho>^2)/(k*n)"
  proof (cases "?u=?v")
    case True
    then show ?thesis  using k_pos by auto
  next
    case False
    have  assm1: "?v \<in> ridge_argmin (S_index S i z) k" using k_pos in_argmin S_index_is_sample
      using \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> assms by blast
    have assm2: "?u \<in> ridge_argmin S k" using in_argmin k_pos  
      using \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> assms  by blast
    let ?loss_zi = "(\<lambda> h. l h (S i))"
    let ?loss_z =  "(\<lambda> h. l h z)"
    have " \<rho> \<ge> 0"  using lipschitz  lipschitz_on_def
      using \<open>z \<in> set_pmf D\<close> by blast
    have assm3: " \<rho>-lipschitz_on H  (\<lambda> h. l h z)" using lipschitz \<open>z \<in> set_pmf D\<close>
      by auto
    have "S i \<in> D" using sample_in_D assms `i \<in> {0..<n}` by simp
    then have assm4:" \<rho>-lipschitz_on H  (\<lambda> h. l h (S i))" using assm3 lipschitz by auto
    have " norm(?v-?u) > 0" using `?u \<noteq> ?v`  by auto
    have "n > 0"  using \<open>i \<in> {0..<n}\<close> by auto
    have "?u \<in> H" using assm2 ridge_argmin_def  by (simp add: is_arg_min_def)
    have "?v \<in> H" using assm1 ridge_argmin_def  by (simp add: is_arg_min_def)
    have " dist (?loss_zi ?v)  (?loss_zi ?u) \<le> \<rho> * dist ?v ?u" 
      using `?v\<in>H` `?u\<in>H` assm4 lipschitz_onD by fastforce
    moreover have "(?loss_zi ?v) - (?loss_zi ?u) \<le> dist (?loss_zi ?v)  (?loss_zi ?u)" 
      by (simp add: dist_norm)
    ultimately  have 1:"(?loss_zi ?v) - (?loss_zi ?u) \<le>  \<rho> * dist ?v ?u" by auto

    have " dist (?loss_z ?u)  (?loss_z ?v) \<le> \<rho> * dist ?u ?v" 
      using `?v\<in>H` `?u\<in>H` assm3 lipschitz_onD by fastforce
    moreover have "(?loss_z ?u) - (?loss_z ?v) \<le> dist (?loss_z ?u)  (?loss_z ?v)" 
      by (simp add: dist_norm)
    ultimately  have 2: "(?loss_z ?u) - (?loss_z ?v) \<le>  \<rho> * dist ?v ?u" 
    proof -
      have "l (ridge_mine S k) z - l (ridge_mine (S_index S i z) k) z \<le> \<rho> * dist (ridge_mine S k) (ridge_mine (S_index S i z) k)"
        using \<open>dist (l (ridge_mine S k) z) (l (ridge_mine (S_index S i z) k) z) \<le> \<rho> * dist (ridge_mine S k) (ridge_mine (S_index S i z) k)\<close> \<open>l (ridge_mine S k) z - l (ridge_mine (S_index S i z) k) z \<le> dist (l (ridge_mine S k) z) (l (ridge_mine (S_index S i z) k) z)\<close> dual_order.trans by blast
      then show ?thesis
        by (simp add: dist_commute)
    qed
    then have "(?loss_zi ?v) - (?loss_zi ?u) + (?loss_z ?u) - (?loss_z ?v) \<le>
                 2 * \<rho> * dist ?v ?u" using 1 2 by auto
    then have "(((?loss_zi ?v) - (?loss_zi ?u)) + ((?loss_z ?u) - (?loss_z ?v)))/n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" using `n>0` by (simp add: divide_right_mono)

    then have "((?loss_zi ?v) - (?loss_zi ?u))/n + ((?loss_z ?u) - (?loss_z ?v))/n \<le>
                 (2 * \<rho> * dist ?v ?u)/n" by (simp add: add_divide_distrib)
    then have " k * norm(?v - ?u)^2  \<le> (2 * \<rho> * dist ?v ?u)/n" using ridge_stable assms
      by (smt \<open>i \<in> {0..<n}\<close> assm1 assm2)
    then have " k * norm(?v - ?u)^2/k \<le> (2 * \<rho> * norm(?v - ?u)/ n)/ k" 
      using k_pos  divide_right_mono dist_norm by smt
    then have  " norm(?v - ?u)^2 \<le> 2 * \<rho> * norm(?v - ?u)/(n * k)"
      using k_pos by auto

    then have "norm(?v - ?u)^2 /norm(?v - ?u) \<le> (2 * \<rho> * norm(?v - ?u)/(n * k))/ norm(?v - ?u)"
      using  `norm(?v-?u) > 0` by (metis divide_le_cancel norm_not_less_zero)
    then have "norm (?v - ?u)* (norm(?v-?u)/norm(?v-?u)) \<le>  2 * \<rho> * (norm(?v-?u)/norm(?v-?u)) / (n*k)"
      by (smt \<open>0 < norm (ridge_mine (S_index S i z) k - ridge_mine S k)\<close> nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_right)

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

end

lemma integral_bellow_const:
  fixes f :: "'a \<Rightarrow> real"
  assumes smaller_a: "AE x in M.  f x \<le> (a::real) "
  assumes pos_a: "a\<ge>0" 
  assumes M_finite: "finite_measure M"
  shows " integral\<^sup>L M f \<le> measure M (space M) *\<^sub>R a"
proof(cases "integrable M f")
  case True
  have 1: "integrable M (\<lambda> y. a)" using finite_measure.integrable_const M_finite by auto
  have "integral\<^sup>L M (\<lambda>y. a) = (\<integral>x. a \<partial>M)" by simp
  then have "integral\<^sup>L M (\<lambda>y. a) = measure M (space M) *\<^sub>R a" using lebesgue_integral_const by auto
  then have "AE x in M.  f x \<le> (\<lambda> y. a) x " using smaller_a 1 by auto
  then have " integral\<^sup>L M f \<le> integral\<^sup>L M (\<lambda>y. a)" using integral_mono_AE 1 
    using True by blast
  then show ?thesis
    using \<open>LINT y|M. a = Sigma_Algebra.measure M (space M) *\<^sub>R a\<close> by linarith
next
  case False
  have "integral\<^sup>L M f = 0" using False 
    by (simp add: not_integrable_integral_eq)
  then show ?thesis 
    by (simp add: pos_a)
qed

lemma univ_to_exist: "A\<noteq>{} \<Longrightarrow> \<forall>x\<in>A. P x \<Longrightarrow> \<exists>x\<in>A. P x" 
  by blast

context lipschitz_ridge_and_convex_loss
begin



lemma integrable_D:"\<forall> S \<in> (Samples n D). integrable D (\<lambda> z. l (ridge_mine S k) z)" 
proof
  fix S
  assume "S\<in> Samples n D"
  have "(ridge_mine S k) \<in> H" using min_in_H 
    using \<open>S \<in> set_pmf (Samples n D)\<close> by blast
  then show "integrable D (\<lambda> z. l (ridge_mine S k) z)" 
    using integrable_l by auto
qed


lemma pred_err_integrable_h:
 "integrable (Samples n D) (\<lambda> S. pred_err_loss D l h)" 
  unfolding pred_err_loss_def by auto

lemma agh:
"integrable (Samples n D) (\<lambda>S. measure_pmf.expectation D (l (ridge_mine S k)))"
proof -
  let ?f = "(\<lambda>  S x. l (ridge_mine S k) x)"
  have  f_nn: "\<forall>S\<in> (Samples n D). \<forall>z\<in>D. ?f S z \<ge> 0"
    using l_pos min_in_H by blast
  have integrable_f: "\<forall> S \<in> (Samples n D). integrable D (?f S)" using integrable_D 
    by auto
  have "integrable (Samples n D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. ?f S z)) =
      integrable (Samples (n+1) D) (\<lambda> Sz. ?f (truncated_S Sz n) (Sz n))"
    using f_nn integrable_f add_sample_integrable[of n ?f] by blast
  have " integrable (Samples (n+1) D) (\<lambda> Sz. ?f (truncated_S Sz n) (Sz n))" 
    oops




lemma expect_as_last:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  shows " measure_pmf.expectation (Samples m D) (\<lambda> S.  l h (S (m-1))) =
                      measure_pmf.expectation D (\<lambda> z. l h z)"
proof -
  let ?f = "(\<lambda> S z. l h z)"
    have f_nn : "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. ?f S z \<ge> 0" using l_pos `h\<in>H` by auto
  have 1:"measure_pmf.expectation (Samples (m-1) D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. ?f S z)) =
      measure_pmf.expectation (Samples m D) (\<lambda> Sz. ?f (truncated_S Sz (m-1)) (Sz (m-1)))"
    using add_sample_expectation[of "m-1" ?f] using  f_nn
    using assms(2) integrable_l  l_pos
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
    have f_nn : "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. ?f S z \<ge> 0" using l_pos `h\<in>H` by auto
  have 1:"integrable (Samples (m-1) D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. ?f S z)) =
      integrable (Samples m D) (\<lambda> Sz. ?f (truncated_S Sz (m-1)) (Sz (m-1)))"
    using add_sample_integrable[of "m-1" ?f] using  f_nn
    using assms(2) integrable_l  l_pos
    by (simp add: m_pos)
  then show ?thesis using 1 
    using assms(2) integrable_l by blast
qed

lemma expect_sample_same:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  shows "\<forall> i \<in> {0..<m}. measure_pmf.expectation (Samples (m) D) (\<lambda> S.  l h (S (m-1))) = 
  measure_pmf.expectation (Samples (m) D) (\<lambda> S.  l h (S i))"
proof 
  fix i
  assume "i\<in>{0..<m}"
  let ?f = "(\<lambda> S. l h (S (m-1)))"
  have "measure_pmf.expectation (Samples m D) ?f  = 
           measure_pmf.expectation  (Samples m D) (\<lambda> x. ?f (swapped_S x i (m-1)))"
    using expect_f_swap_same[of m i ?f] m_pos `i\<in>{0..<m}` by auto
  then show "measure_pmf.expectation (Samples m D) (\<lambda>S. l h (S (m - 1))) =
     measure_pmf.expectation (Samples m D) (\<lambda>S. l h (S i))" unfolding swapped_S_def
    by simp
qed

lemma integrable_sample_same:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  shows "\<forall> i \<in> {0..<m}. integrable (Samples m D) (\<lambda> S.  l h (S (m-1))) = 
  integrable (Samples m D) (\<lambda> S.  l h (S i))"
proof 
  fix i
  assume "i\<in>{0..<m}"
  let ?f = "(\<lambda> S. l h (S (m-1)))"
    have "(m - 1) \<in> {0..<m}" using m_pos by auto
  have "integrable (Samples m D) ?f  = 
          integrable  (Samples m D) (\<lambda> x. ?f (swapped_S x i (m-1)))"
    using integrable_f_swap_same[of m  ?f i] m_pos `i\<in>{0..<m}` l_pos 
    using \<open>m - 1 \<in> {0..<m}\<close> assms(2) sample_in_D by blast 
  then show "integrable (Samples m D) (\<lambda>S. l h (S (m - 1))) =
     integrable (Samples m D) (\<lambda>S. l h (S i))" unfolding swapped_S_def
    by simp
qed


lemma expect_over_D: 
  assumes "h\<in>H"
  shows "\<forall> i \<in> {0..<n}. measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) =
                      measure_pmf.expectation D (\<lambda> z. l h z)"
proof 
  fix i
  assume "i\<in> {0..<n}" 
  have "\<forall> S \<in> (Samples n D). S i \<in> D"
    using \<open>i \<in> {0..<n}\<close> sample_in_D by blast
  have "\<forall> z \<in> D. \<exists> S \<in> (Samples n D). S i = z"
  proof
    fix z
    assume "z\<in>D"
    obtain S where "S\<in> Samples n D"  
      by (meson set_pmf_not_empty some_in_eq)
    then have 1:"S_index S i z \<in> Samples n D" 
      using S_index_is_sample \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    then have " (S_index S i z) i = z" unfolding S_index_def by auto
    then show "\<exists> S \<in> (Samples n D). S i = z" using 1 by auto
  qed
  have "n>0" using n_pos by auto
  then show "measure_pmf.expectation (Samples n D) (\<lambda> S.  l h (S i)) = 
                      measure_pmf.expectation D (\<lambda> z. l h z)"
    using expect_sample_same[of n h] expect_as_last[of n h] `h\<in>H`    
    using \<open>i \<in> {0..<n}\<close> by metis
qed

lemma integrable_over_D: 
  assumes "h\<in>H"
  shows "\<forall> i \<in> {0..<n}. integrable (Samples n D) (\<lambda> S.  l h (S i)) =
                      integrable D (\<lambda> z. l h z)"
proof 
  fix i
  assume "i\<in> {0..<n}" 
  have "\<forall> S \<in> (Samples n D). S i \<in> D"
    using \<open>i \<in> {0..<n}\<close> sample_in_D by blast
  have "\<forall> z \<in> D. \<exists> S \<in> (Samples n D). S i = z"
  proof
    fix z
    assume "z\<in>D"
    obtain S where "S\<in> Samples n D"  
      by (meson set_pmf_not_empty some_in_eq)
    then have 1:"S_index S i z \<in> Samples n D" 
      using S_index_is_sample \<open>i \<in> {0..<n}\<close> \<open>z \<in> set_pmf D\<close> by blast
    then have " (S_index S i z) i = z" unfolding S_index_def by auto
    then show "\<exists> S \<in> (Samples n D). S i = z" using 1 by auto
  qed
  have "n>0" using n_pos by auto
  then show "integrable (Samples n D) (\<lambda> S.  l h (S i)) = 
                      integrable D (\<lambda> z. l h z)"
    using integrable_sample_same[of n h] integrable_as_last[of n h] `h\<in>H`    
    using \<open>i \<in> {0..<n}\<close> by metis
qed

lemma train_err_integrable1:
 assumes "h\<in>H"
 shows " integrable (Samples n D) (\<lambda> S. train_err_loss S n l h)"
  unfolding train_err_loss_def
proof -
  let ?f = " (\<lambda> i S. l h (S i))"
  let ?M = " (Samples n D)"
  have "finite {0..<n}" by auto
  have 1: "\<forall>S\<in>set_pmf ?M. \<forall>i\<in>{0..<n}. 0 \<le> ?f i S " using l_pos `h\<in>H` 
    using sample_in_D by blast
have "\<forall> i \<in> {0..<n}. integrable (Samples n D) (?f i) =
                      integrable D (\<lambda> z. l h z)" using integrable_over_D `h\<in>H` by auto
  then have "\<forall> i \<in> {0..<n}. integrable (Samples n D) (\<lambda> x. (?f i) x)" 
    using integrable_l  using assms by blast
  then have " integrable (Samples n D) (\<lambda>x. \<Sum>i\<in>{0..<n}. (?f i) x)"
    using integrable_sum_iff[of ?M "{0..<n}" ?f] by auto
  then show " integrable (Samples n D) (\<lambda>x. (\<Sum>i\<in>{0..<n}. (?f i) x)/n )"
    by auto
qed


lemma expectation_train_err:
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D)
                              (\<lambda> S. train_err_loss S n l h) =
                            pred_err_loss D l h"
proof -
  let ?I = "{0..<n}"
  let ?Dn = "Samples n D"
  let ?f = "(\<lambda> i. (\<lambda> S. l h (S i)))"
  have fin_I: "finite ?I" by auto
  have non_empty_I: "?I \<noteq> {}" using n_pos by auto


 have "measure_pmf.expectation (Samples n D) 
                              (\<lambda> S. train_err_loss S n l h) = 
   measure_pmf.expectation (Samples n D) 
                              (\<lambda> S.  sum (\<lambda>i. l h (S i) ) {0..<n} / n)"
   unfolding train_err_loss_def by auto

  also have " \<dots> =
  measure_pmf.expectation ?Dn
     (\<lambda>S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l h (S i)))"
     using  non_empty_I   by (simp add: integral_pmf_of_set)

  also have " \<dots> =
    measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i)))"
  proof -
    have I_swap: 
    "\<forall> i\<in> ?I. \<forall> j \<in> ?I. measure_pmf.expectation ?Dn (\<lambda> S. ?f i S) =
       measure_pmf.expectation ?Dn (\<lambda> S. ?f j S)" using expect_over_D `h\<in>H` 
      by auto
    have  f_nn: "\<forall> S \<in> (set_pmf ?Dn). \<forall> i \<in> ?I. ?f i S \<ge> 0"
      using   sample_in_D[of n] l_pos `h\<in>H`  by blast

  
   show ?thesis
      using swap_set_expectation[of ?Dn ?I ?f] I_swap f_nn fin_I non_empty_I
      by blast
  qed
  also have "measure_pmf.expectation (pmf_of_set {0..<n})
     (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i))) =
  sum  (\<lambda>i. measure_pmf.expectation ?Dn (\<lambda>S. l h (S i))) ?I / card ?I" 
    using integral_pmf_of_set non_empty_I by blast
  also have " \<dots> =  sum (\<lambda> i.  measure_pmf.expectation D (\<lambda> z. l h z)) ?I/ card ?I"
  using expect_over_D `h\<in>H` by auto
 
 also have "... = measure_pmf.expectation D (\<lambda> z. l h z)" 
   using non_empty_I by auto
   
  finally show ?thesis unfolding pred_err_loss_def  by auto 
qed
 


lemma train_err_integrable:

 shows " integrable (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k))"
proof -
  let ?f = " (\<lambda> i S. l (ridge_mine S k) (S i))"
  let ?g = "(\<lambda> S  z. l (ridge_mine S k) z)"
  let ?M = " (Samples n D)"
  have "finite {0..<n}" by auto
  have "\<forall>S\<in>?M. (ridge_mine S k) \<in> H" using min_in_H by auto
  then have 1: "\<forall>S\<in>set_pmf ?M. \<forall>i\<in>{0..<n}. 0 \<le> ?f i S " using l_pos 
    using sample_in_D by blast
  have " \<forall>S \<in>?M.\<exists>h\<in>H.  l (ridge_mine S k) (S (n-1)) \<le> l h (S (n-1))"
    using learning_basics1.min_in_H learning_basics1_axioms by blast
  
  let ?A = "{h. \<exists>S\<in>?M. l (ridge_mine S k) (S (n-1)) \<le> l h (S (n-1))}"

  have "\<forall>h\<in>H. \<forall>S \<in> Samples n D. train_err_loss S n l (ridge_mine S k) \<le>
                                train_err_loss S n l h +  k * norm ( h )^2" 
  proof(rule)+
    fix h
    fix S
    assume "h\<in>H"
    assume "S\<in>Samples n D" 
    let ?w = " (ridge_mine S k)"
     have " train_err_loss S n l ?w \<le> train_err_loss S n l h + k * norm ( h )^2"
  proof -
    have "is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) (ridge_mine S k)"
      unfolding ridge_mine_def unfolding ridge_argmin_def 
      by (metis (full_types) \<open>S \<in> set_pmf (Samples n D)\<close> in_argmin k_pos mem_Collect_eq ridge_argmin_def tfl_some)
    then have 1: "(ridge_fun S k)  (ridge_mine S k) \<le> (ridge_fun S k) h" 
      using `h\<in>H` 
      by (simp add: is_arg_min_linorder)
    then have " train_err_loss S n l ?w  + k* norm((ridge_mine S k))^2 \<le>
   train_err_loss S n l h + k * norm ( h )^2"
      using 1 unfolding ridge_fun.simps by auto
    then show " train_err_loss S n l ?w   \<le>
   train_err_loss S n l h + k * norm ( h )^2" using k_pos
      by (smt mult_nonneg_nonneg zero_le_power2)
  qed
  then show "train_err_loss S n l (ridge_mine S k) \<le>
                                train_err_loss S n l h +  k * norm ( h )^2"
    by blast
qed
 
  then have "\<exists>h\<in>H. \<forall>S \<in> Samples n D. train_err_loss S n l (ridge_mine S k) \<le>
                                train_err_loss S n l h +  k * norm ( h )^2"
    using nnH   by blast
  then obtain h where "h\<in>H" " \<forall>S \<in> Samples n D. train_err_loss S n l (ridge_mine S k) \<le>
                                train_err_loss S n l h +  k * norm ( h )^2" by auto
  let ?u = "(\<lambda> S. ennreal (norm (train_err_loss S n l (ridge_mine S k))))" 
  let ?v = "(\<lambda> S. ennreal (norm (train_err_loss S n l h +  k * norm ( h )^2)))"
  have "\<forall>S \<in> Samples n D. train_err_loss S n l (ridge_mine S k) \<ge> 0" 
      by (simp add: train_err_loss_nn "1")
    then have  "\<forall>S \<in> Samples n D. (train_err_loss S n l (ridge_mine S k)) =
          (norm (train_err_loss S n l (ridge_mine S k)))" 
      by simp
    then have 12:"\<forall>S \<in> Samples n D.  (norm (train_err_loss S n l (ridge_mine S k)))
    \<le> train_err_loss S n l h + k * (norm h)\<^sup>2" 
      using \<open>\<forall>S\<in>set_pmf (Samples n D).
     train_err_loss S n l (ridge_mine S k) 
  \<le> train_err_loss S n l h + k * (norm h)\<^sup>2\<close> by auto

    have "\<forall>S\<in> Samples n D. train_err_loss S n l h + k * (norm h)\<^sup>2 \<le>
     norm ( train_err_loss S n l h + k * (norm h)\<^sup>2)" by auto
    then have "\<forall>S\<in> Samples n D. ennreal (norm (train_err_loss S n l (ridge_mine S k))) \<le>
  ennreal (norm ( train_err_loss S n l h + k * (norm h)\<^sup>2))" using 
      12 by auto
  then have "AE x in ?M. ?u x \<le> ?v x"
    using AE_measure_pmf_iff by blast

  then have 5:"integral\<^sup>N ?M ?u \<le> integral\<^sup>N ?M ?v"
    using  nn_integral_mono_AE[of  ?u ?v ?M] by blast
 
   have 4:"integrable ?M (\<lambda> S.  k * norm ( h )^2)" by auto
  then have 2:"integrable ?M (\<lambda> S.  train_err_loss S n l h +
         k * norm ( h )^2)"  using train_err_integrable1[of h] `h\<in>H`
    using Bochner_Integration.integrable_add[of ?M "(\<lambda> S. train_err_loss S n l h)"
                                              "(\<lambda> S.  k * norm ( h )^2)"] 
    by blast
  then have "integral\<^sup>N ?M ?v < \<infinity>" using  integrable_iff_bounded by metis
  then have 6:"integral\<^sup>N ?M ?u < \<infinity>" using 5 by auto

  have "(\<lambda> S. (train_err_loss S n l (ridge_mine S k))) \<in> borel_measurable ?M" by auto
   have "integrable ?M  (\<lambda> S. (train_err_loss S n l (ridge_mine S k)))" 
    using 6 integrable_iff_bounded[of ?M "(\<lambda> S. (train_err_loss S n l (ridge_mine S k)))"]
    by simp
  then show "integrable (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k))" 
    by auto
qed



lemma replace_one_stable: "\<forall>i\<in>{0..<n}.
                        measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le> 
                        (2*\<rho>^2)/(k*n)"
proof (rule)
  fix i
  assume " i \<in> {0..<n}"
  show "measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le> 
                        (2*\<rho>^2)/(k*n)"
  proof -
    have 1:"\<forall>S\<in> (Samples (n+1) D). (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n)"
    proof
      fix S
      assume " S \<in> (Samples (n+1) D)"
      have "i \<in> {0..<n+1}" using `i\<in>{0..<n}` by auto
     
       have "(truncated_S S n) \<in> Samples n D" using
           truncated_S_in_Dn using `S \<in> (Samples (n+1) D)`  by auto
       have 2:"(truncated_S S n i) = S i" using `i\<in> {0..<n}` unfolding truncated_S_def by auto
      have "n \<in> {0..< n+1}" by auto
     
      then have " S n \<in> D" using sample_in_D[of "n+1"] `S \<in> (Samples (n+1) D)` 
        by blast
      then have 3:" (l (ridge_mine (S_index (truncated_S S n)i (S n)) k) (S i)) - 
                         (l  (ridge_mine (truncated_S S n) k) (S i)) \<le>  (2*\<rho>^2)/(k*n)"
        using 
         lipschitz_loss_diff_bounded[of "(truncated_S S n)"] 
          ` i \<in> {0..<n+1}` ` S \<in> (Samples (n+1) D)` 2 
        using \<open>i \<in> {0..<n}\<close> \<open>truncated_S S n \<in> set_pmf (Samples n D)\<close> by fastforce
      have 4:"(l (ridge_mine (S_index (truncated_S S n)i (S n)) k) (S i)) =
        (l (ridge_mine (S_index S i (S n)) k) (S i))" 
        by (metis (mono_tags, lifting) "2" S_index_def fun_upd_triv fun_upd_twist truncated_S_def truncated_same_min)
      have "(l  (ridge_mine (truncated_S S n) k) (S i)) = (l  (ridge_mine S k) (S i))"
        by (metis  truncated_same_min)
      then show "(l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n)" using 3 4 
        by (simp add: ridge_index_swap_same)
    qed

    have finite_M:"finite_measure (Samples (n+1) D)" by simp
    have measure_M:"measure (Samples (n+1) D) (space (Samples (n+1) D)) = 1" by simp
    have pos_const: "(2*\<rho>^2)/(k*n) \<ge> 0" using k_pos by auto

    have "n \<ge> 1" using \<open>i \<in> {0..<n}\<close> by auto
    have "(2*\<rho>^2)/k \<ge> 0" 
      using k_pos by auto
    then have "(2*\<rho>^2)/(k*(n+1)) \<le> (2*\<rho>^2)/(k*n)"  using \<open>1 \<le> n\<close> frac_le by fastforce
    then have "\<forall>S\<in> (Samples (n+1) D). (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n)" using 1 by auto
    then have "AE S in (Samples (n+1) D).  (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n) "
      using AE_measure_pmf_iff by blast
    then have "AE S in (Samples (n+1) D).  (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) S \<le>  (2*\<rho>^2)/(k*n)" 
      by blast

    then have " integral\<^sup>L (Samples (n+1) D) (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))) \<le>  (2*\<rho>^2)/(k*n)" 
      using finite_M measure_M pos_const 
        integral_bellow_const[of "(\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                                   (l  (ridge_mine S k) (S i)))"
          " (2*\<rho>^2)/(k*n)"
          "(Samples (n+1) D)"] by simp
    then show ?thesis by auto
  qed
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

lemma sum_bounded_const1:
  fixes t::nat
  fixes f :: "nat \<Rightarrow> real"
  fixes a :: "real"
  assumes "\<forall> i \<in> {0..<t}. f i \<le> a"
  shows "sum f {0..<t} \<le> t * a"
  using sum_bounded_const 
  using assms by blast

lemma replace_one_stable1: " 
                        measure_pmf.expectation (pmf_of_set {0..<n})
                       (\<lambda> i. measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)))) \<le> 
                        (2*\<rho>^2)/(k*n)"
proof -
  let ?f = "(\<lambda> i. measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))))" 
  have "sum ?f {0..<n} \<le> n * (2*\<rho>^2)/(k*n)" 
    using replace_one_stable sum_bounded_const[of n ?f "(2*\<rho>^2)/(k*n)"] by simp
  then have "sum ?f {0..<n} / n \<le>  n * (2*\<rho>^2)/(k*n) / n"
    using divide_right_mono of_nat_0_le_iff by blast
  then have "sum ?f {0..<n} / n \<le>  (2*\<rho>^2)/(k*n) " 
    using n_pos by auto
  then show ?thesis 
    by (metis (no_types, lifting) card_atLeastLessThan card_empty diff_zero finite_atLeastLessThan integral_pmf_of_set le_zero_eq n_pos zero_neq_one)
qed

lemma replace_one_stable2: " 
                        measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S. measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda> i. 
                      (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)))) \<le> 
                        (2*\<rho>^2)/(k*n)"
proof -
  let ?Dn1 = "(Samples (n+1) D)"
  let ?f = "(\<lambda> S. (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i))))" 
  have M_finite: "finite_measure ?Dn1" by auto
  have measure_M:"measure (Samples (n+1) D) (space (Samples (n+1) D)) = 1" by simp
  have pos_const: "(2*\<rho>^2)/(k*n) \<ge> 0" using k_pos by auto

  have 1:"\<forall>S\<in> (Samples (n+1) D). \<forall> i \<in> {0..<n}.
          ?f S i \<le>  (2*\<rho>^2)/(k*n)"
  proof (rule)+
    fix S
    fix i
    assume " S \<in> (Samples (n+1) D)"
    assume " i \<in> {0..<n}"
 have "i \<in> {0..<n+1}" using `i\<in>{0..<n}` by auto
     
       have "(truncated_S S n) \<in> Samples n D" using
           truncated_S_in_Dn using `S \<in> (Samples (n+1) D)`  by auto
       have 2:"(truncated_S S n i) = S i" using `i\<in> {0..<n}` unfolding truncated_S_def by auto
      have "n \<in> {0..< n+1}" by auto
     
      then have " S n \<in> D" using sample_in_D[of "n+1"] `S \<in> (Samples (n+1) D)` 
        by blast
      then have 3:" (l (ridge_mine (S_index (truncated_S S n)i (S n)) k) (S i)) - 
                         (l  (ridge_mine (truncated_S S n) k) (S i)) \<le>  (2*\<rho>^2)/(k*n)"
        using 
         lipschitz_loss_diff_bounded[of "(truncated_S S n)"] 
          ` i \<in> {0..<n+1}` ` S \<in> (Samples (n+1) D)` 2 
        using \<open>i \<in> {0..<n}\<close> \<open>truncated_S S n \<in> set_pmf (Samples n D)\<close> by fastforce
      have 4:"(l (ridge_mine (S_index (truncated_S S n)i (S n)) k) (S i)) =
        (l (ridge_mine (S_index S i (S n)) k) (S i))" 
        by (metis (mono_tags, lifting) "2" S_index_def fun_upd_triv fun_upd_twist truncated_S_def truncated_same_min)
      have "(l  (ridge_mine (truncated_S S n) k) (S i)) = (l  (ridge_mine S k) (S i))"
        by (metis  truncated_same_min)
      then show "(l (ridge_mine (swapped_S S i n) k) (S i)) - 
                         (l  (ridge_mine S k) (S i)) \<le>  (2*\<rho>^2)/(k*n)" using 3 4 
        by (simp add: ridge_index_swap_same)
  qed
  have "\<forall> S \<in> ?Dn1. 
        integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> (2*\<rho>^2)/(k*n)"
  proof (rule)
    fix S
    assume "S\<in> ?Dn1"
    have " {0..<n} \<noteq> {}" using n_pos by auto
    have 2:  "(2*\<rho>^2)/(k*(n+1)) \<le> (2*\<rho>^2)/(k*n)" using n_pos 
      by (simp add: frac_le k_pos)
    have " \<forall> i \<in> {0..<n}. ?f S i \<le>  (2*\<rho>^2)/(k*n)" using 1 `S\<in> ?Dn1` by auto
    then have " \<forall> i \<in> {0..<n}. ?f S i \<le>  (2*\<rho>^2)/(k*n)"  using 2 by auto
    then have " sum (\<lambda> i. ?f S i) {0..<n} \<le> n * ((2*\<rho>^2)/(k*n))"
      using sum_bounded_const1[of n "(\<lambda> i. ?f S i)" "(2*\<rho>^2)/(k*n)"] `{0..<n} \<noteq> {}` 
      by auto
    then have "sum (\<lambda> i. ?f S i) {0..<n} / n \<le> n * ((2*\<rho>^2)/(k*n)) / n"
      using divide_right_mono of_nat_0_le_iff by blast
    then have "sum (\<lambda> i. ?f S i) {0..<n} / card {0..<n} \<le> ((2*\<rho>^2)/(k*n))"
      using n_pos by auto
    then show " integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> (2*\<rho>^2)/(k*n)"
      by (metis (no_types, lifting) \<open>{0..<n} \<noteq> {}\<close> finite_atLeastLessThan integral_pmf_of_set)

  qed
  then have "AE S in (Samples (n+1) D).  
     integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i) \<le> (2*\<rho>^2)/(k*n) "
    using AE_measure_pmf_iff by blast

  then show " integral\<^sup>L (Samples (n+1) D)
     (\<lambda> S.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i)) \<le>  (2*\<rho>^2)/(k*n)" 
    using M_finite measure_M pos_const 
      integral_bellow_const[of " (\<lambda> S.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda> i. ?f S i))"
        " (2*\<rho>^2)/(k*n)" ?Dn1] by simp
qed

lemma lipschitz_stable:
  assumes pred_err_integrable:
 "integrable (Samples n D) (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
shows " measure_pmf.expectation (Samples n D) (\<lambda> S.
                       pred_err_loss D l (ridge_mine S k) -
           train_err_loss S n l (ridge_mine S k))
                        \<le>  (2*\<rho>^2)/(k*n)"
proof -
  let ?Dn = "Samples n D"
  let ?Dn1 = "Samples (n+1) D"
  let ?I = "{0..<n}"
  let ?pmfI = "(pmf_of_set ?I)"
  let ?l_swapped = "(\<lambda> i. (\<lambda> S. l (ridge_mine (swapped_S S i n) k) (S i)))"
  let ?l_trunc = "(\<lambda> S. (\<lambda> z. l (ridge_mine (truncated_S S n) k) z))"
  let ?l_Si = "(\<lambda> S. (\<lambda>i. l (ridge_mine S k) (S i)))"
  let ?pred_err = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  have fin_I:"finite ?I" by auto
  have non_empty_I:"?I \<noteq> {}" 
    using n_pos by auto

  have integ_swap: "\<forall> i  \<in> ?I.  integrable ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
  proof 
    fix i
    assume "i\<in> ?I"
    have 1:"integrable ?Dn  (\<lambda> S. ?pred_err S)" using pred_err_integrable by auto
    then have "integrable ?Dn  
    (\<lambda>S. measure_pmf.expectation D (\<lambda> z. l (ridge_mine S k) z))" 
      unfolding pred_err_loss_def by auto
    then  have 2:"integrable ?Dn1 (\<lambda> S. ?l_trunc S (S n))"
      using add_sample_integrable[of n "(\<lambda> S z. l (ridge_mine S k) z)"]
    l_pos min_in_H  integrable_D 
      by blast
    have "\<forall>S\<in>?Dn. ?pred_err S \<ge> 0" using min_in_H pred_err_loss_nn by auto

    have 3:"(\<lambda>S. l (ridge_mine (truncated_S S n) k)(S n)) = 
        (\<lambda>S. l (ridge_mine S k)(S n))" using  truncated_same_min by auto
    have "integrable ?Dn1 (\<lambda> S. ?l_trunc S (S n))" using 2 by auto
    then have "integrable  ?Dn1 (\<lambda> S. ?l_Si S n)" using 3 by simp
    then have " integrable (measure_pmf (Samples (n + 1) D))
     (\<lambda>x. l (ridge_mine (swapped_S x i (n + 1 - 1)) k) (swapped_S x i (n + 1 - 1) n))" 
      using integrable_f_swap_same[of "n+1" "(\<lambda> S. ?l_Si S n)" i]
      using \<open>i \<in> {0..<n}\<close> l_pos min_of_Dn1_in_H sample_in_D by auto
    then show " integrable ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)" unfolding swapped_S_def
      by auto
  qed
  have "(\<forall> i \<in> ?I.  integrable ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)) \<longleftrightarrow> 
      integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x))"
    using  integrable_sum_iff[of ?Dn1 ?I "(\<lambda> i Sz. ?l_swapped i Sz)"] 
        fin_I l_pos 
    by (smt add_diff_cancel_right' add_gr_0 atLeastLessThan_iff learning_basics1.pmf_swapped_same learning_basics1.sample_in_D learning_basics1.swapped_S_def learning_basics1_axioms less_add_same_cancel1 less_trans min_of_Dn1_in_H set_pmf_iff zero_less_one)
  then have "integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x))" 
    using integ_swap by auto
  then have 4:"integrable  ?Dn1 (\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x)/card ?I)"
    by auto
  have "(\<lambda> x. (\<Sum>i\<in>?I. ?l_swapped i x)/card ?I) =  (\<lambda> x. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i x))"
  using  fin_I non_empty_I
  by (simp add: integral_pmf_of_set[of ?I ]) 
 
  then have 5:"integrable ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )" 
    using 4 by auto

   have "\<forall>S. \<forall>i\<in>?I. (truncated_S S n) i = S i"  using  truncated_S_def by auto 
  then  have  "\<forall>S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)) =
               integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))" 
    by (metis (no_types, lifting) fin_I non_empty_I same_integral_restricted set_pmf_of_set)
  then have 7:"(\<lambda> S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i))) =
            (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))) " by auto

   have "n>0" using n_pos by auto
  then have 6: "integrable ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> _.  integral\<^sup>L ?pmfI (?l_Si S))) =
      integrable ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)))"
    using 
      integrable_uniform uniform_nn add_sample_integrable[of n " (\<lambda> S. (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S)))"]   by blast

   have "card ?I = n" by auto
  then have "\<forall> S. integral\<^sup>L ?pmfI (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (?l_Si S) ?I) / card ?I"
    using integral_pmf_of_set `finite ?I` `?I \<noteq> {}` by blast
  then have "\<forall> S. train_err_loss S n l (ridge_mine S k) = 
      integral\<^sup>L ?pmfI (?l_Si S)" 
    using `card ?I = n` train_err_loss_def by force

  then have 8:" integrable ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k)) 
            =  integrable ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))"
    using 6 7 truncated_same_min  by auto

  then have "integrable ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))" using
  train_err_integrable by auto

  then have integrable_Si:"integrable (Samples (n+1) D) 
      (\<lambda> S.  integral\<^sup>L (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
    by auto
  have integrable_swapped: "integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i))))"
    using 5 by auto
  show ?thesis
    using train_val_diff replace_one_stable2 integrable_D integrable_Si integrable_swapped 
      pred_err_integrable  
        train_err_integrable  by auto
qed


lemma oracle_inequality:
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D)
                              (\<lambda> S.  pred_err_loss D l (ridge_mine S k)) \<le>
    pred_err_loss D l h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)"
proof -
  let ?pred_min = "(\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  let ?train_min = "(\<lambda> S.  train_err_loss S n l (ridge_mine S k))"
  let ?Dn = "(Samples n D)"
  show ?thesis
  proof(cases "integrable ?Dn (\<lambda> S.  pred_err_loss D l (ridge_mine S k))")
    case True
  have 1: "integral\<^sup>L ?Dn (\<lambda> S. ?pred_min S) =
    integral\<^sup>L ?Dn (\<lambda> S. ?train_min S)  + integral\<^sup>L ?Dn  (\<lambda> S.  ?pred_min S - ?train_min S)"
    using True train_err_integrable by simp
  have "integrable ?Dn ?train_min"
    using train_err_integrable by blast
  have "\<forall> S \<in> ?Dn. ?train_min S \<le> train_err_loss S n l h + k * norm ( h )^2"
  proof
    fix S
    assume "S\<in> ?Dn"
    have "is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) (ridge_mine S k)"
      unfolding ridge_mine_def unfolding ridge_argmin_def 
      by (metis (full_types) \<open>S \<in> set_pmf (Samples n D)\<close> in_argmin k_pos mem_Collect_eq ridge_argmin_def tfl_some)
    then have 1: "(ridge_fun S k)  (ridge_mine S k) \<le> (ridge_fun S k) h" 
      using `h\<in>H` 
      by (simp add: is_arg_min_linorder)
    then have "?train_min S  + k* norm((ridge_mine S k))^2 \<le>
   train_err_loss S n l h + k * norm ( h )^2"
      using 1 unfolding ridge_fun.simps by auto
    then show "?train_min S   \<le>
   train_err_loss S n l h + k * norm ( h )^2" using k_pos
      by (smt mult_nonneg_nonneg zero_le_power2)
  qed
  have 3: "integrable ?Dn ?train_min" 
    using train_err_integrable by auto
  have 5:"integrable ?Dn (\<lambda> S. train_err_loss S n l h)" 
    using train_err_integrable1[of h] `h\<in>H` by auto
  have 4:"integrable ?Dn (\<lambda> S.  k * norm ( h )^2)" by auto
  then have 2:"integrable ?Dn (\<lambda> S.  train_err_loss S n l h +
         k * norm ( h )^2)"  using train_err_integrable1[of h] `h\<in>H`
    using Bochner_Integration.integrable_add[of ?Dn "(\<lambda> S. train_err_loss S n l h)"
                                              "(\<lambda> S.  k * norm ( h )^2)"]
  by blast
  have "AE S in ?Dn. ?train_min S \<le> train_err_loss S n l h + k * norm ( h )^2"
    using AE_measure_pmf_iff \<open>\<forall>S\<in>set_pmf (Samples n D). train_err_loss S n l (ridge_mine S k) \<le> train_err_loss S n l h + k * (norm h)\<^sup>2\<close> by blast


  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
            integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h +
         k * norm ( h )^2)" using 2 3
        integral_mono_AE[of ?Dn ?train_min "(\<lambda> S.  train_err_loss S n l h +
         k * norm ( h )^2)" ] 
    by blast
  have "integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h +
         k * norm ( h )^2) = 
       integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h) + 
        integral\<^sup>L ?Dn (\<lambda> S. k * norm ( h )^2)"
    using 4 5 using Bochner_Integration.integral_add[of ?Dn "(\<lambda> S. train_err_loss S n l h)"
                                              "(\<lambda> S.  k * norm ( h )^2)"]
    by blast


  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le> 
            integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h) + 
        integral\<^sup>L ?Dn (\<lambda> S. k * norm ( h )^2)"
    using \<open>measure_pmf.expectation (Samples n D) (\<lambda>S. train_err_loss S n l (ridge_mine S k)) \<le> measure_pmf.expectation (Samples n D) (\<lambda>S. train_err_loss S n l h + k * (norm h)\<^sup>2)\<close> by linarith

  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
            integral\<^sup>L ?Dn (\<lambda> S.  train_err_loss S n l h) +   k * norm ( h )^2" by simp
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?train_min S) \<le>
             pred_err_loss D l h + k * norm ( h )^2" using expectation_train_err `h\<in>H`
    by auto
  then have "integral\<^sup>L ?Dn (\<lambda> S. ?pred_min S) \<le>
    pred_err_loss D l h + k * norm ( h )^2  + integral\<^sup>L ?Dn  (\<lambda> S.  ?pred_min S - ?train_min S)"
    using 1 by linarith

  then show ?thesis using lipschitz_stable True by smt
next
  case False
  have 1:"measure_pmf.expectation (Samples n D)
                              (\<lambda> S.  pred_err_loss D l (ridge_mine S k)) = 0"
    using False 
    using not_integrable_integral_eq by blast
  have "pred_err_loss D l h \<ge> 0" using pred_err_loss_nn `h\<in>H` by auto
  then have "0 \<le> pred_err_loss D l h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)" 
    using k_pos by auto
  then show ?thesis using 1 by auto
qed
qed


end
end