\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory Strong_Convexity
  imports Main "HOL-Analysis.Analysis" "HOL-Analysis.Convex" 
begin

paragraph \<open>Summary\<close>
text \<open>In this theory we define strong convexity over euclidean space similar 
to the definition of convexity already in Isabelle. Some lemmas about 
strong convexity are proven as in 
@{cite UnderstandingML}.\<close>

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

text\<open>Definition of strong convexity as defined in UN. The definition follows the
same style as the definition of convexity that already exists in Isabelle\<close>
definition strong_convex_on :: "'a::euclidean_space set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "strong_convex_on S f k \<longleftrightarrow>
    (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y) )" 

lemma strong_convex_onI:
  assumes 
    "\<And>x y u v. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow>  u\<ge>0 \<Longrightarrow>  v\<ge>0 \<Longrightarrow> u + v = 1 \<Longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y)"
  shows "strong_convex_on S f k"
  using assms
  unfolding strong_convex_on_def  
  by blast 

text\<open>Every strong convex function is a convex function\<close>
lemma convex_on_if_strong_convex_on:
  assumes k_pos: "k \<ge> 0" 
  assumes strong_convex: "strong_convex_on S f k"
  shows " convex_on S f"
proof -
  have 1:" (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y) )"
    unfolding strong_convex_on_def using strong_convex 
    by (simp add: strong_convex_on_def) 
  have "\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> (k/2) * u * v * norm(x-y) * norm(x-y) \<ge> 0"
    using k_pos  by simp
  then have "\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> 
  u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y)  \<le>
  u * f x + v * f y " by auto
  then have "(\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)" using 1 by smt
  then show "convex_on S f"  by (simp add: convex_on_def)
qed

lemma sq_norm_sum : "norm (x+y)^2 = norm x ^ 2 + 2 *\<^sub>R (x \<bullet> y) + norm y ^ 2" 
  for x y :: "'a::euclidean_space"
  by (smt inner_commute inner_left_distrib power2_norm_eq_inner scaleR_2)

lemma sq_norm_diff[simp]: "norm (x - y)^2 = norm x ^ 2 - 2 *\<^sub>R (x \<bullet> y) + norm y ^ 2" 
  for x y :: "'a::euclidean_space"
  using sq_norm_sum
  by (simp add: inner_commute inner_diff_right power2_norm_eq_inner)

lemma sq_norm_scalar: "norm (u *\<^sub>R x)^2  = u^2 * norm(x)^2"
proof -
  have "abs(u)^2 = u^2" by simp
  then show "norm (u *\<^sub>R x)^2  = u^2 * norm(x)^2" 
    using norm_scaleR power2_eq_square
    by (simp add: power_mult_distrib)
qed

lemma sq_norm_strong_convex: "strong_convex_on S (\<lambda> w. k * norm(w) * norm(w)) (2*k)"
  for S :: "'a::euclidean_space set"
proof (rule strong_convex_onI)
  let ?f = "(\<lambda> w. k * norm(w) * norm(w))"
  show "\<And> x y u v. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow>
     ?f (u *\<^sub>R x + v *\<^sub>R y) \<le>
     u * ?f x + v * ?f y - (2*k/2) * u * v * norm(x-y) * norm(x-y)"
  proof -
    fix x assume"x\<in>S"
    fix y assume"y\<in>S"
    fix u assume"(u::real) \<ge> 0"
    fix v assume"(v::real) \<ge> 0"
    assume "u+v = 1"
    then show " ?f  (u *\<^sub>R x + v *\<^sub>R y) \<le> 
             u * ?f x + v * ?f y - (2*k/2) * u * v * norm(x-y) * norm(x-y)"
    proof -   
      have  "?f  (u *\<^sub>R x + v *\<^sub>R y) = k * (norm (u  *\<^sub>R x +  v *\<^sub>R y))^2" 
        by (simp add: power2_eq_square)
      also  have "k * (norm (u  *\<^sub>R x +  v  *\<^sub>R y))^2 =
        k * (norm (u *\<^sub>R x)^2 + (2 * u * v) * (x \<bullet> y) + norm (v *\<^sub>R y)^2)" 
        by (simp add: sq_norm_sum)
      also have " \<dots> = k * (u^2 * norm (x)^2 + (2 * u * v) * (x \<bullet> y) + v^2 * norm (y)^2)"
        using sq_norm_scalar by metis
      also  have "\<dots>  = k * u * norm(x)^2 + (2 * k * u * v) * (x \<bullet> y) + k* v * norm (y)^2 
                       - k * u * v * norm(x)^2 - k * u * v * norm(y)^2" 
        using `u+v = 1` by algebra
      also have "\<dots> =  k * u * norm(x)^2 + k* v * norm (y)^2 
                       - (k * u * v) * (norm(x)^2 - 2 * (x \<bullet> y) + norm(y)^2)" 
        using distrib_left sq_norm_diff by argo
      also have "\<dots> = k * u * norm(x)^2 + k * v * norm (y)^2 - (k * u * v) * norm(x - y)^2" 
        by simp
      finally have "?f  (u *\<^sub>R x + v *\<^sub>R y) =  
                  u * ?f x + v * ?f y - (2 * k/2) * u * v * norm(x-y) * norm(x-y)"
        by  (simp add: power2_eq_square)
      then show ?thesis   by linarith
    qed
  qed
qed

instantiation "fun" :: (type, plus) plus
begin

definition fun_plus_def: "A + B = (\<lambda>x. A x + B x)"

lemma minus_apply [simp, code]: "(A + B) x = A x + B x"
  by (simp add: fun_plus_def)

instance ..

end

instantiation "fun" :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add
begin

instance proof
  fix x y z :: "'a => 'b"
  show "x + y + z = x + (y + z)"
    unfolding fun_plus_def
    by (simp add: add.assoc)
next
  fix x y :: "'a => 'b"
  show "x + y = y + x"
    unfolding fun_plus_def 
    by (simp add: add.commute)
qed
end

instantiation "fun" :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
begin

definition zero_fun_def:  "0 == (\<lambda>x. 0)"

instance proof
  fix a :: "'a => 'b"
  show "0 + a = a" 
    unfolding zero_fun_def fun_plus_def by simp
qed

end

lemma convex_fun_add:
  assumes "convex_on S f" "convex_on S g"
  shows "convex_on S (f + g)"
proof - 
  have "(f + g) = (\<lambda> x. f x + g x)" using fun_plus_def by auto
  moreover have "convex_on S (\<lambda>x. f x + g x)" using assms convex_on_add by auto
  ultimately show "convex_on S (f + g)" by auto
qed

text\<open>Sum of a convex and strong convex function is a strong convex function 
with the same parameter. The proof follows the proof in UN lemma 13.5(2).\<close>
lemma strong_convex_sum:
  assumes  "strong_convex_on S f k" "convex_on S g"   
  shows "strong_convex_on S (f + g) k"
proof (rule strong_convex_onI)
  show  "\<And> x y u v. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 \<le> u \<Longrightarrow>0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow>
     (f+g) (u *\<^sub>R x + v *\<^sub>R y) \<le> 
      u * (f+g) x + v * (f+g) y - (k/2) * u * v * norm(x-y) * norm(x-y)"
  proof -
    fix x assume"x\<in>S"
    fix y assume"y\<in>S"
    fix u assume"(u::real) \<ge> 0"
    fix v assume"(v::real) \<ge> 0"
    assume "u+v = 1"
    then show "(f+g) (u *\<^sub>R x + v *\<^sub>R y) \<le> 
      u * (f+g) x + v * (f+g) y - (k/2) * u * v * norm(x-y) * norm(x-y)"
    proof -
      have 1: "f (u *\<^sub>R x + v *\<^sub>R y) \<le> 
           u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y)"
        using  \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> \<open>u + v = 1\<close> \<open>x \<in> S\<close> \<open>y \<in> S\<close>  `strong_convex_on S f k` 
        unfolding strong_convex_on_def by blast

      have 2: " g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * g x + v * g y" 
        using \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> \<open>u + v = 1\<close> \<open>x \<in> S\<close> \<open>y \<in> S\<close> `convex_on S g ` 
        unfolding convex_on_def by blast

      have  "f (u *\<^sub>R x + v *\<^sub>R y)  +  g (u *\<^sub>R x + v *\<^sub>R y) \<le> 
           u * f x + v * f y - (k/2) * u * v * norm(x-y) * norm(x-y)  + 
       u * g x + v * g y "
        using 1 2 by linarith
      then show ?thesis  by (simp add: distrib_left)
    qed
  qed
qed

lemma func_norm_negative: 
  assumes "(l::real)<0" 
  assumes "\<forall>x. norm (f x - l) < -l"
  shows "\<forall>x. f x < 0"
proof (rule ccontr)
  assume "\<not> (\<forall>x. f x < 0)"
  then show False using assms(2) real_norm_def by smt
qed

lemma LIM_fun_less_zero:
  fixes a :: "'b::euclidean_space" and  l :: "real"
  assumes "f \<midarrow>a\<rightarrow> l" "l < 0" "\<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r"
  shows "f x < 0"
proof -
  have "\<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> norm (f x - l)< -l)" 
    using LIM_D[of f l a "-l"] assms
    by (simp add: norm_minus_commute)
  then obtain r where "0 < r" "(\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> norm (f x - l)< -l)" by auto
  then have "(\<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow>  f x < 0)" 
    using `l<0` func_norm_negative  by auto
  then show ?thesis
    using \<open>0 < r\<close> assms by blast
qed

lemma metric_LIM_le:
  fixes a :: "real"
  assumes "f \<midarrow>a\<rightarrow> (l::real)"
  assumes "a\<ge>0"
    and "\<forall>x>a. f x \<ge> 0"
  shows " l \<ge> 0" 
proof (rule ccontr)
  assume "\<not> (l \<ge> 0)"
  then have " l < 0"  by simp
  then have " \<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0"
    using assms(1) Limits.LIM_fun_less_zero by auto 
  then have "\<exists>r>0. \<forall>x>a. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0 \<and> f x \<ge> 0" 
    using assms(3) by blast
  then have "\<exists>r>0. \<forall>x>a. norm(a - x) \<ge> r" by force
  then obtain r where "r>0" and " \<forall>x>a. norm(a - x) \<ge> r" by auto
  then have 1: "\<forall>x>a. norm(a - x) \<ge> r" by auto
  have  "\<exists>k. k>0 \<and>  k <r "
    using `r>0`  by (simp add: dense)
  then obtain k where "k>0" and "k < r" by auto
  then have "\<exists> x. x>a \<and> x-a = k" by smt
  then have "\<exists> x>a. norm(a-x) < r \<and> norm(a - x) \<ge> r"
    using  `k<r`1 by auto
  then show False  by linarith
qed

lemma metric_LIM_le_zero:
  fixes a :: "real"
  assumes "f \<midarrow>a\<rightarrow> (l::real)"
  assumes "a\<ge>0"
    and "\<exists>r>0. \<forall>x>a. norm(a-x) < r \<longrightarrow> f x \<ge> 0"
  shows " l \<ge> 0" 
proof (rule ccontr)
  assume "\<not> (l \<ge> 0)"
  then have " l < 0"  by simp
  then have " \<exists>r>0. \<forall>x. x \<noteq> a \<and> norm(a - x) < r \<longrightarrow> f x < 0"
    using assms(1) Limits.LIM_fun_less_zero  by auto
  then obtain r where "r>0" and 1: "\<forall>x>a. norm(a - x) < r \<longrightarrow> f x < 0" by auto
  obtain r1 where "r1>0" and 2: "\<forall>x>a. norm(a-x) < r1 \<longrightarrow> f x \<ge> 0" 
    using assms(3)  by auto
  let ?min_r = "min r1 r"
  have 3: " r \<ge> ?min_r " by auto
  have 4: " r1 \<ge> ?min_r " by auto
  have "?min_r>0" using `r>0` `r1>0` by auto
  then have 5: "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x < 0"
    using 1 3 by auto
  then have "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x \<ge> 0"
    using 2 4 by auto
  then have "\<forall>x>a. norm(a - x) < ?min_r \<longrightarrow> f x < 0 \<and> f x \<ge> 0" 
    using 5 by blast
  then have 6: "\<forall>x>a. norm(a - x) \<ge> ?min_r" by force

  then have  "\<exists>k. k>0 \<and>  k <?min_r " 
    using `?min_r>0` dense by blast 
  then obtain k where "k>0" and "k < ?min_r" by auto
  then have "\<exists> x. x>a \<and> x-a = k" by smt
  then have "\<exists> x>a. norm(a-x) < ?min_r \<and> norm(a - x) \<ge> ?min_r"
    using  `k<?min_r` 6 by auto
  then show False using LIM_fun_less_zero 
    by linarith
qed

lemma norm_mult_const: 
  assumes "x > 0" " dist t 0 < r/x"
  shows "norm(t) * x < r" 
  using assms nonzero_mult_div_cancel_right 
    mult_less_le_imp_less[of "norm t"  "r/x" "x"  "x"] by auto


lemma real_collapse [simp]: "(1 - u) * a * b + (-1) * a * b = - u * a * b"
  for a :: "real"
  by (simp add: algebra_simps)

lemma real_left_commute: "a * b * x = b * a * x"
  for a :: real
  by (simp add: mult.commute)

text\<open>The proof of this lemma partially  follows the proof of lemma 13.5 (3).
     However it was easier to prove that the limit of the difference of the two sides
    is greater than 0.\<close>
lemma strongly_convex_min:
  assumes "strong_convex_on S f k"
  assumes "x \<in> S"
  assumes "\<forall>y\<in>S. (f x \<le> f y)"
  assumes "w \<in> S"
  assumes "convex S"
  shows "f w - f x \<ge> (k/2)*norm(w - x)^2"
proof (cases "w = x")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
  proof(cases "k = 0")
    case True
    then show ?thesis using assms(3) assms(4) by auto
  next
    case False
    then show ?thesis 
    proof -
      have "(\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y - (k/2) * u * v * norm(x-y)^2)"
        using assms(1) unfolding  strong_convex_on_def 
        by (simp add: power2_eq_square mult.commute mult.left_commute)
      then have f_convex:" \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     f (u *\<^sub>R w + v *\<^sub>R x) \<le> u * f w + v * f x - (k/2) * u * v * norm(w-x)^2"
        using assms(2) assms(4) by blast

      have  "\<forall>u>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow>
     (f (u *\<^sub>R w + (1-u) *\<^sub>R x) - f x )/u \<le> f w  - f x - (k/2) * (1-u) * norm(w-x)^2"
      proof(rule)+
        fix u assume "(u::real) > 0"
        fix v assume "(v::real) \<ge> 0"
        assume "u + v = 1"
        then show "(f (u *\<^sub>R w + (1-u) *\<^sub>R x) - f x )/u \<le> f w  - f x - (k/2) * (1-u) * norm(w-x)^2"
        proof -
          have "f (u *\<^sub>R w + (1-u) *\<^sub>R x) 
            \<le> u * f w + (1-u) * f x - (k/2) * u * (1-u) * norm(w-x)^2" using `u + v = 1` f_convex
            \<open>0 < u\<close> \<open>0 \<le> v\<close> by auto
          then have " f (u *\<^sub>R w + (1-u) *\<^sub>R x)/u \<le> 
        (u * f w + (1-u) * f x - (k/2) * u * (1-u) * norm(w-x)^2)/u" using `u>0` 
            by (meson divide_right_mono less_eq_real_def)
          then have " f (u *\<^sub>R w + (1-u) *\<^sub>R x)/u \<le> 
              (u * f w)/u + ((1-u) * f x)/u - ((k/2) * u * (1-u) * norm(w-x)^2)/u" 
            by (simp add: add_divide_distrib diff_divide_distrib)
          then have " f (u *\<^sub>R w + (1-u) *\<^sub>R x)/u \<le>
               f w + ((1-u) / u)* f x - (k/2) * (1-u) * norm(w-x)^2"
            using \<open>0 < u\<close> add_divide_distrib diff_divide_distrib by auto
          then have " f (u *\<^sub>R w + (1-u) *\<^sub>R x)/u  \<le> 
              f w + (1/u)* f x + (-u/u)*f x - (k/2) * (1-u) * norm(w-x)^2"
            by (simp add: diff_divide_distrib Groups.mult_ac(2) add_diff_eq right_diff_distrib')
          then have " f (u *\<^sub>R w + (1-u) *\<^sub>R x)/u - (1/u)* f x \<le> 
              f w  - f x - (k/2) * (1-u) * norm(w-x)^2"
            using diff_divide_distrib Groups.mult_ac(2) add_diff_eq right_diff_distrib' `u>0`
            by force
          then show ?thesis 
            by (simp add: diff_divide_distrib)
        qed
      qed
      then have 1:"\<forall>u>0. u <= 1 \<longrightarrow>
     (\<lambda> t. (f (t *\<^sub>R w + (1-t) *\<^sub>R x) - f x )/t) u \<le> 
        (\<lambda> t. f w  - f x - (k/2) * (1-t) * norm(w-x)^2) u" by smt

      have "\<forall>u>0. u <= 1 \<longrightarrow> u *\<^sub>R w + (1 - u) *\<^sub>R x \<in> S " 
        using assms(2) assms(4) assms(5) by (simp add: convex_def)
      then have "\<forall>u>0. u <= 1 \<longrightarrow>
    (\<lambda> t. (f (t *\<^sub>R w + (1-t) *\<^sub>R x) - f x )/t) u  \<ge> 0" using assms(3) 
        assms(2) assms(4) by auto
      then have 11 : "\<forall>u>0. u <= 1 \<longrightarrow>
    0 \<le> (\<lambda> t. f w  - f x - (k/2) * (1-t) * norm(w-x)^2) u" using 1 by fastforce

      let ?f = "(\<lambda> t. f w  - f x - (k/2) * (1-t) * norm(w-x)^2)"
      let ?L = "(f w  - f x - (k/2) * norm(w-x)^2)"
      have "\<forall>t. dist (?f t) ?L = norm(?f t - ?L)"
        using dist_norm by blast

      then have 2: "\<forall>t. norm(?f t - ?L) = 
       norm( (k/2) * (1-t) * norm(w-x)^2 + (-1)* (k/2) * norm(w-x)^2)" by auto

      then have 3: "\<forall>t. norm(?f t - ?L) = norm(t*(k/2) * norm(w-x)^2)" 
        using "2" real_left_commute  real_collapse real_left_commute 
        by (metis (no_types, hide_lams)  mult_minus_left norm_minus_cancel)

      then have "\<forall>t. norm(t*(k/2) * norm(w-x)^2) = norm(t) * norm(k/2) * norm(w-x)^2"
        using norm_ge_zero norm_mult power2_eq_square real_norm_def 
        by smt
      then have 5:"\<forall>t. norm(?f t - ?L) = norm(t) * norm(w-x)^2 * norm((k/2))" using 3  by simp

      have 55: "norm(w-x)^2 * norm((k/2)) > 0" using `w \<noteq> x` `k \<noteq> 0` 
        by (metis divide_eq_0_iff divide_less_eq norm_zero right_minus_eq 
            zero_less_norm_iff zero_less_power2 zero_neq_numeral)
      then have "\<forall>r. \<forall>t. t \<noteq> 0 \<and> dist t 0 < ( r/(norm(w-x)^2 * norm(k/2))) \<longrightarrow>
            norm(t) * norm(w-x)^2 * norm((k/2)) < r"
        by (simp add: norm_mult_const mult.assoc)

      then have 6: "\<forall>r. \<forall>t. t \<noteq> 0 \<and> dist t 0 < ( r/(norm(w-x)^2 * norm(k/2))) \<longrightarrow>
            dist (?f t) ?L < r" using 5 dist_norm by metis

      then have "\<forall>r>0. (r/(norm(w-x)^2 * norm(k/2))) > 0"
        using divide_pos_pos 55 by blast 
      then have "\<forall>r > 0. \<exists>S > 0. \<forall>t. t \<noteq> 0 \<and> dist t 0 < S \<longrightarrow> 
          dist (?f t) ?L < r" using 6 by auto
      then have 7:" ?f \<midarrow>0\<rightarrow> ?L" unfolding LIM_def by auto

      then have "\<forall>u>0. u <= 1 \<longrightarrow> 0 \<le> ?f u" using 11 by simp
      then have "\<exists>r>0. \<forall>u>0.  u \<le> r \<longrightarrow> 0 \<le> ?f u"  using zero_less_one by blast
      then have "\<exists>r>0.\<forall>u>0. norm (0 -u) < r \<longrightarrow> 0 \<le> ?f u" by auto 
      then have "?L \<ge> 0" using metric_LIM_le_zero using 7 by blast
      then show ?thesis by auto
    qed
  qed
qed

lemma strong_conv_if_eq: " f = g \<Longrightarrow> strong_convex_on S f k \<Longrightarrow> strong_convex_on S g k"
  using  HOL.subst by auto

end