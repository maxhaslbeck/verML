\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory hinge_loss
  imports "RLM_stable"
begin

paragraph \<open>Summary\<close>
text \<open>In this theory we define hinge loss and proove some lemmas 
that show it can be used as loss function for lipschitz convex learning\<close>

paragraph \<open>Main definitions\<close>
text \<open>
\<^item> \<open>hinge_loss\<close> a loss function :
l_hinge (w, (x,y)) = max {0, 1 - y * ( w \<bullet> x )}
Here y is either -1 or 1
and x is real vecotr.
w stands for the vector with weights, i.e. the hypothesis.
The definition follows the definition of hinge loss in UN.\<close>

paragraph \<open>Main Theorems\<close>
text \<open>
\<^item> \<open>hinge_loss_is_lipschitz\<close> We prove that for a fixed (x,y) 
the hinge loss is |x|-lipschitz
\<^item> \<open>hinge_loss_convex\<close> We prove that for a fixed (x,y) 
the hinge loss is convex
Then we can use it as a loss function in ridge regression with
convex and lipschitz function
\<close>

fun hinge_loss :: "('a:: euclidean_space  \<Rightarrow> ('a \<times> real) \<Rightarrow> real)" where
  "hinge_loss w (x,y) = (max 0 (1 - y * (w \<bullet> x)))" 

lemma hinge_loss_is_lipschitz:
  fixes A :: "'a::euclidean_space set"

assumes "abs y = 1"
shows "(norm (x))-lipschitz_on A (\<lambda> z. hinge_loss z (x,y))"
proof -
  let ?f = "(\<lambda> z. hinge_loss z (x,y))"
  have "\<forall> u \<in> A. \<forall> v \<in> A. abs (?f u - ?f v) \<le> (norm x) * norm ( u - v )"
  proof (rule)+
    fix u
    fix v
    assume "u\<in>A"
    assume "v\<in>A"
    show "abs (?f u - ?f v) \<le> (norm x) * norm ( u - v )"
    proof -
      have "abs(?f u - ?f v) \<le> abs (- y * (v \<bullet> x) + y * (u \<bullet> x))" by auto   
      also have " \<dots> =  abs ( y * ((u-v) \<bullet> x))" 
        by (simp add:right_diff_distrib inner_diff_left)
      also have "abs ( y * ((u-v) \<bullet> x)) = abs y * abs ((u-v) \<bullet> x)" 
        using abs_mult by blast
      also have "abs y * abs ((u-v) \<bullet> x) = abs ((u-v) \<bullet> x)" 
        using assms by auto
      also have "abs ((u-v) \<bullet> x) \<le> norm (u-v) * norm x"
        using Cauchy_Schwarz_ineq2 by blast
      finally show ?thesis
        by (simp add: mult.commute)
    qed
  qed
  then show ?thesis
    unfolding lipschitz_on_def
    by (simp add: dist_norm)
qed

lemma sum_of_max:
  fixes a :: real
  fixes b :: real
  shows "max 0 a + max 0 b \<ge>  max 0 (a+b)"
  by simp


lemma hinge_loss_convex:
  fixes H :: "'a::euclidean_space set"
    and D :: "('a \<times> real) pmf"
  assumes "(x,y)\<in>D"
  shows "convex_on H (\<lambda> h. hinge_loss h (x,y))"
  unfolding hinge_loss.simps
proof(rule)+
  fix t u v
  assume " 0 < (t::real)"
  assume " t < 1"
  assume " u \<in> H"
  assume " v \<in> H"
  have 1 : "(1 - t) * (1 - y * (u \<bullet> x)) =  (1 - t) - (1 - t) * y * (u \<bullet> x)" 
    by (metis inner_diff_right inner_real_def mult.assoc real_inner_1_right)
  have 2: " t * (1 - y * (v \<bullet> x)) =  t * 1 - t * y * (v \<bullet> x)"
    by (metis inner_diff_right inner_real_def mult.assoc real_inner_1_right)

  have " max 0 (1 - y * (((1 - t) *\<^sub>R u + t *\<^sub>R v) \<bullet> x)) = 
              max 0 (1 - (1 - t)* y * (u \<bullet> x) - t * y * (v \<bullet> x))"
    by (simp add: distrib_left inner_left_distrib mult.assoc mult.left_commute)
  also have " \<dots> = max 0 ((1 - t) * (1 - y * (u \<bullet> x)) + t * (1 - y * (v \<bullet> x)))"
    using  inner_diff_right inner_real_def mult.assoc real_inner_1_right
    using 1 2 by auto
  also have " \<dots> \<le> (1 - t) * max 0 (1 - y * (u \<bullet> x)) +  t * max 0 (1 - y * (v \<bullet> x))" 
    by (smt \<open>0 < t\<close> \<open>t < 1\<close> mult_left_le_imp_le mult_nonneg_nonneg)
  finally show " max 0 (1 - y * (((1 - t) *\<^sub>R u + t *\<^sub>R v) \<bullet> x)) \<le> 
            (1 - t) * max 0 (1 - y * (u \<bullet> x)) + t * max 0 (1 - y * (v \<bullet> x))"
    by blast
qed


lemma hinge_loss_pos:
  fixes H :: "'a::euclidean_space set"
    and D :: "('a \<times> real) pmf"
  shows "\<forall>h\<in>H. \<forall>z\<in>D. hinge_loss h z \<ge> 0"
  by auto



end