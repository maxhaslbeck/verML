\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory RLM_learn
  imports  "LearningTheory" "Strong_Convexity"
begin


paragraph \<open>Summary\<close>
text \<open>In this theory we define prediction and training loss as defined in 
@{cite UnderstandingML}. We use the definition with the usage of generalized loss
function. The loss function is non-negative and in later lemmas it will be
also convex. \<close>

paragraph \<open>Main Definitions\<close>
text \<open>Definition of strong convexity of a function over a set
in euclidean space\<close>

paragraph \<open>Main Theorems\<close>
text \<open>
\<^item> \<open>convex_on_if_strong_convex_on\<close> A function is convex if it is strongly convex
\<^item> \<open>sq_norm_strong_convex\<close>k * |w|^2 is a 2*k strong convex function
\<^item> \<open>strong_convex_sum\<close> sum of a convex and strong convex function is a strong
convex function
\<^item> \<open>strongly_convex_min\<close> For k-strongly convex f and  u minimizer of f we have:
      f(w) - f(u) >= k/2*|w - u|^2 for every w.
\<close>

section \<open>Basic definitions\<close>

text \<open>Definition of Prediction and Training error using a loss function. It was used the 
definition from @{cite UnderstandingML}
\<^item> \<open>pred_err_loss \<close>Given the whole set D of possible values  what is the expectation of the 
  loss for a given hypothesis h
\<^item> \<open>train_err_loss\<close> Given a finite dataset S what is the expected loss for a 
hypothesis h. Since it is a finite dataset we can get the mean over S\<close>


definition pred_err_loss :: "('a \<times> 'b) pmf \<Rightarrow>  ('c  \<Rightarrow> ('a \<times> 'b) \<Rightarrow>  real)
 \<Rightarrow> 'c \<Rightarrow> real" where
  "pred_err_loss D l h = measure_pmf.expectation D (\<lambda> z. (l h z))"

definition train_err_loss :: " (nat \<Rightarrow> ('a * 'b)) \<Rightarrow> nat \<Rightarrow>
('c \<Rightarrow> ('a \<times> 'b) \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow>  real" where
  "train_err_loss S n l h = sum (\<lambda>i. l h (S i) ) {0..<n} / n"


text \<open>The train error is non-negative, when l is non-negative function\<close>
lemma train_err_loss_nn: 
  assumes "(\<forall>i\<in>{0..<n}. l h (S i) \<ge> 0)"
  shows "train_err_loss S n l h \<ge> 0"
proof - 
  have "0 \<le> (\<Sum>i\<in>{0..<n}. l h (S i))"  by (meson assms sum_nonneg) 
  then show ?thesis unfolding train_err_loss_def  by simp
qed


text \<open>The Prediction error is non-negative, when l is non-negative function.\<close>
lemma pred_err_loss_nn:
  fixes D :: "('b \<times> 'c) pmf"
  assumes "h\<in>H"
  assumes l_nn: "\<forall>h\<in>H. \<forall>z\<in>D. l h z \<ge> 0"
  shows "pred_err_loss D l h \<ge> 0"
  unfolding pred_err_loss_def
proof - 
  have "\<forall>z\<in>D. l h z \<ge> 0" using l_nn `h\<in>H` by auto
  then show "integral\<^sup>L D (\<lambda> z. l h z) \<ge> 0"
    by (simp add: AE_measure_pmf_iff integral_nonneg_AE)
qed

lemma sum_of_funcs_is_func:
  fixes n :: nat
  shows "(\<Sum>i = 0..<n.(\<lambda>x. f i x)) = (\<lambda>x. \<Sum>i = 0..<n. f i x)"
  proof(induct n) 
    case 0
    then show ?case 
      by (simp add: zero_fun_def)
  next
    case (Suc n)
    then show ?case
      by (simp add: Suc.hyps Suc.prems)
  qed

lemma sum_of_convex_funcs_is_convex:
  fixes n :: nat
  assumes "\<forall>i \<in>{0..<n} . convex_on H (f i)"
  shows "convex_on H (\<lambda>x. \<Sum>i = 0..<n. f i x)"
proof -
  have "convex_on H (\<Sum>i\<in>{0..<n}. f i)" using assms
 proof(induction n)
    case 0
    then show ?case 
      by (simp add: convex_on_def zero_fun_def)
  next
    case (Suc n)
    then show  "convex_on H (\<Sum>i = 0..<Suc n.(f i))"
      by (simp add: convex_fun_add)
  qed
  then show ?thesis
    using sum_of_funcs_is_func[of f n] by auto
qed

text\<open>With L_s(w) we refer to the train error for a hypothesis w. 
We show L_s(w) is convex over H, when the loss function is convex over H\<close>
lemma train_err_loss_convex_if_loss_convex:
  fixes n :: nat
  assumes "(\<forall>i \<in>{0..<n} . convex_on H (\<lambda> h. l h (S i)))"
  shows "convex_on H (train_err_loss S n l)"
proof -
  have " (1/n)\<ge> 0" by auto
  have " convex_on H (\<lambda>h. \<Sum>i = 0..<n. l h (S i))" 
    using sum_of_convex_funcs_is_convex[of n H ] assms
    by auto
  then have "convex_on H  (\<lambda> h. (1/n)*(sum (\<lambda>i. l h (S i)) {0..<n}))"
    using convex_on_cmul `(1/n)\<ge> 0`
    by blast
  then show ?thesis
    unfolding train_err_loss_def
    by auto
qed

text\<open>Define a locale for learning with a loss function.
\<^item> H - non-empty convex set of hypothesis (regularly just a vector with weights)
\<^item> D - set from which we take the data
\<^item> n - number of data points taken from D
\<^item> l - non-negative loss function (convex over D)
\<^item> k - positive regularization constant 
\<close>

locale learning_basics_loss =

fixes H :: "'a::{euclidean_space} set"
  and D :: "('b \<times> 'c) pmf"
  and n :: "nat"
  and l :: "('a  \<Rightarrow> ('b \<times> 'c) \<Rightarrow> real)"
  and k :: "real" 
assumes nnH: "H \<noteq> {}" 
  and  convH: "convex H"
  and l_nn: "\<forall>h\<in>H. \<forall>z\<in>D. l h z \<ge> 0"
  and convll : "\<forall>z \<in> D. convex_on H (\<lambda> h. l h z)"
  and n_pos: "n > 0"
  and k_pos : "k > 0"
begin

text \<open>"Regularized Loss Minimization" 
RLM refers to learning using loss function with regularization function.
Here we 
Its learning rule RLMe chooses for a given training set S an Hypothesis h from H
which minimizes the training error + regularisation function. 
Special case of RLM is ridge regression. 
\<close>

section \<open>Main definitions about regularized loss minimization\<close>

text \<open>RLM is the set of all minimizers of a general regularized loss minimization.
This is the argmin of general training error + regularization function (r in this context)\<close>
definition RLM :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set" where
  "RLM S' r = {h. is_arg_min (train_err_loss S' n l + r) (\<lambda>s. s\<in>H) h}"

text \<open>We select one minimizer that is argmin of the regularizied loss minimization\<close>
definition RLMe :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space" where 
  "RLMe S' r = (SOME h. h\<in> RLM S' r)"

text \<open>ridge_fun is the Ridge regression loss function, which is a special case 
of regularized loss minimization. Here r(w) = k*|w|^2, where k is regularization constant.\<close>
fun ridge_fun :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real)" where
  "ridge_fun S' k' = (train_err_loss S' n l + (\<lambda> w. k' * (norm w)^2))" 

text \<open>All minimizers of the ridge regression function.\<close>
definition ridge_argmin :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> 'a::euclidean_space set" where
  "ridge_argmin S' k' = {h. is_arg_min (ridge_fun S' k') (\<lambda>s. s\<in>H) h}"

text \<open>Select one of the minimizers of the ridge regression\<close>
definition ridge_mine :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> real \<Rightarrow> 'a::euclidean_space" where
  "ridge_mine S' k' = (SOME h. h \<in> ridge_argmin S' k')"

text \<open>swap two values of a function. This will be useful when we show 
what is the difference in ridge regression for small changes in the dataset\<close>
definition swapped_fun :: "(nat \<Rightarrow> ('b * 'c)) \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "swapped_fun S' i m =  S'(i:= S' m, m:= S' i) "  

text \<open>Make the result for some value undefined. This will be useful, when
we make connection between dataset with with and without one element.\<close>
definition trunc_fun :: "(nat \<Rightarrow> ('b * 'c))  \<Rightarrow> nat \<Rightarrow>(nat \<Rightarrow> ('b * 'c))" where
  "trunc_fun S' m =  S'(m := undefined) "

text\<open>S_index is a set where the i-th data point in S is replaced with an arbitrary one
definition S_index :: "(nat \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) \<Rightarrow> (nat \<Rightarrow> ('b * 'c))" where
  "S_index S' i z = S'(i := z)"

lemma "S_index x i z = x(i:=z)" 
\<close>


section \<open>Basic lemmas about ridge regression\<close>

text \<open>This was written different theory by Max Halsberk, but only this is 
needed.\<close>
lemma set_pmf_Pi_pmf: "\<And>S i. finite A \<Longrightarrow> S \<in> set_pmf (Pi_pmf A dflt Q)
                   \<Longrightarrow> i \<in> A \<Longrightarrow> S i \<in> set_pmf (Q i)" 
  apply(subst set_pmf_iff)
  apply(subst (asm) set_pmf_iff) 
  apply(subst (asm) pmf_Pi) apply simp apply auto
  using prod_zero by metis 


lemma element_of_sample_in_dataset: 
  assumes " S \<in> (Samples m D)"
  shows " \<And>i. i \<in> {0..<m} \<Longrightarrow> S i \<in>  D" 
  using  set_pmf_Pi_pmf assms
  by (metis Samples_def finite_atLeastLessThan)

lemma train_err_loss_convex: 
  assumes " S \<in> (Samples n D)"
  shows "convex_on H (train_err_loss S n l)"
  using train_err_loss_convex_if_loss_convex convll
    element_of_sample_in_dataset assms by blast

text\<open>Shows that ridge regression with regularization constant k
is 2*k-strongly convex\<close>
lemma ridge_strong_convex:
  assumes " S \<in> (Samples n D)"
  shows "strong_convex_on H (ridge_fun S k) (2*k)"
proof -
  have "strong_convex_on H (\<lambda> w. k * (norm w)*(norm w)) (2*k)"
    using sq_norm_strong_convex 
    by blast
  moreover  have  "(\<lambda> w. k * (norm w)*(norm w)) = (\<lambda> w. k * (norm w)^2)"
    by (simp add: power2_eq_square mult.assoc)

  ultimately  have "strong_convex_on H (\<lambda> w. k * (norm w)^2) (2*k)" using 
      strong_conv_if_eq by auto

  then have "strong_convex_on H (train_err_loss S n l + (\<lambda> w. k * (norm w)^2)) (2*k)" 
    using strong_convex_sum train_err_loss_convex add.commute  assms by metis
  then show "strong_convex_on H (ridge_fun S k) (2*k)"
    by auto
qed

lemma ridge_convex:
  assumes " S \<in> (Samples n D)" 
  shows "convex_on H (ridge_fun S k)"
  using  ridge_strong_convex k_pos convex_on_if_strong_convex_on assms
  by smt

lemma convex_has_min: 
  fixes f :: " _ \<Rightarrow> real"
  assumes "convex_on H f"
  shows "\<exists>x\<in>H. is_arg_min f (\<lambda>z. z\<in>H) x" 
  sorry

lemma ridge_min_el_is_argmin: 
  assumes " S \<in> (Samples n D)"
  shows " (ridge_mine S k) \<in> (ridge_argmin S k)"
proof -
  have "\<exists>h. is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h" using 
      ridge_convex k_pos convex_has_min nnH convH assms by auto
  then have "ridge_argmin S k \<noteq> {}" 
    unfolding ridge_argmin_def 
    using nnH convH 
    by blast
  then show  "(ridge_mine S k) \<in> (ridge_argmin S k)"
    unfolding ridge_mine_def
    using some_in_eq
    by blast
qed


lemma fun_upd_swap_same_if_truncated: 
  "trunc_fun (S (i:= (S n))) n =  trunc_fun (swapped_fun S i n) n"
  unfolding trunc_fun_def  unfolding swapped_fun_def
  by auto


lemma fun_upd_is_samples: 
  fixes S :: "(nat \<Rightarrow> ('b \<times> 'c))"
  assumes S_in_D: "S \<in> Samples n D"
  assumes z_in_D: "z \<in> D"
  assumes i_in_I: "i\<in>{0..<n}"
  shows " (S (i:= z)) \<in> Samples n D"
proof -
  let ?S_i = "(S (i:= z))"
  let ?I = "{0..<n}"
  have "finite ?I" by auto
  have "pmf D z > 0" 
    using `z\<in>D`
    by (simp add: pmf_positive)
  have "pmf (Samples n D) S > 0"
    using S_in_D pmf_pos
    by (simp add: pmf_positive)
  then have " \<forall>j. j \<notin> ?I \<longrightarrow> S j = undefined"
    using  n_pos 
    by (metis S_in_D Samples_def finite_atLeastLessThan pmf_Pi_outside pmf_eq_0_set_pmf)
  then have "\<forall>j. j \<notin> ?I \<longrightarrow> ?S_i j = undefined"
    using i_in_I by auto
  then have 1:"pmf (Samples n D) ?S_i = (\<Prod>x\<in>?I. pmf D (?S_i x))"
    unfolding Samples_def 
    using  pmf_Pi' `finite ?I` 
    by (metis (mono_tags, lifting) prod.cong)
  have "(\<Prod>x\<in>?I. pmf D (?S_i x)) > 0"  
    by (smt Probability_Mass_Function.pmf_pos S_in_D  \<open>0 < pmf D z\<close>
        fun_upd_other fun_upd_same prod_pos element_of_sample_in_dataset set_pmf_iff)
  then show ?thesis using 1 
    using set_pmf_iff by force
qed

end

end