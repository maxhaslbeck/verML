theory Subgradients
  imports "RLM_stable"
begin


definition subgradient :: "  ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set \<Rightarrow> 
          'a::euclidean_space \<Rightarrow> 'a::euclidean_space \<Rightarrow> bool " where
  "subgradient f H' w v = (w \<in> H' \<and> ( \<forall> u \<in> H'. f (u) \<ge> f(w) + (inner (u-w) v)))"

definition diff_set :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set \<Rightarrow> 
          'a::euclidean_space \<Rightarrow> 'a::euclidean_space set" where
  "diff_set f H' w = {h. subgradient f H' w h}"

fun hinge_loss :: "('a:: euclidean_space  \<Rightarrow> ('a \<times> real) \<Rightarrow> real)" where
  "hinge_loss w pair = (max 0 (1 - (snd pair) * inner w (fst pair)))" 


text\<open>Don't need to prove it, if we show it is true for the hinge loss\<close>
lemma convex_has_subgradient:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  fixes A :: "'a::euclidean_space set"
  fixes \<rho> :: "real"
  assumes "\<rho> \<ge> 0"
  assumes " open A"
  assumes "convex A"
  shows "convex_on A f \<longleftrightarrow> (\<forall> w \<in> A. \<exists> v \<in> A. \<forall> u \<in> A. f (u) \<ge> f(w) + (inner (u-w) v)) "
  sorry




lemma 147 :
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  fixes A :: "'a::euclidean_space set"
  fixes \<rho> :: "real"
  assumes "\<rho> \<ge> 0"
  assumes " open A"
  assumes "convex A"
  assumes has_subgrad: "\<forall> w \<in> A. \<exists> v. \<forall> u \<in> A. f (u) \<ge> f(w) + (inner (u-w) v)"
    and "convex_on A f"
  shows " \<rho>-lipschitz_on A f \<longleftrightarrow> (\<forall> w \<in> A. \<forall> v \<in> diff_set f A w. norm (v) \<le> \<rho>) "
proof
  assume bound_norm: "(\<forall> w \<in> A. \<forall> v \<in> diff_set f A w. norm (v) \<le> \<rho>)"
  have "\<forall>x\<in>A. \<forall>y\<in>A. dist (f x) (f y) \<le> \<rho> * dist x y"
  proof (rule)+
    fix x
    assume "x \<in> A"
    fix y
    assume " y \<in> A"

    then have "\<forall> v \<in> diff_set f A x. norm v \<le> \<rho>"
      using \<open>\<forall>w\<in>A. \<forall>v\<in>diff_set f A w. norm v \<le> \<rho>\<close> \<open>x \<in> A\<close> by blast
    have "\<forall> v \<in> diff_set f A x. subgradient f A x v"  unfolding diff_set_def by auto
    then have 1: "\<forall> u \<in> A. \<forall> v \<in> diff_set f A x. f (u) \<ge> f(x) + (inner (u-x) v)" 
      unfolding subgradient_def by auto

    then have 2: "\<forall> u \<in> A. \<forall> v \<in> diff_set f A y. f (u) \<ge> f(y) + (inner (u-y) v)" 
      unfolding diff_set_def unfolding subgradient_def by auto
    have "\<exists> v. \<forall> u \<in> A. f (u) \<ge> f(x) + (inner (u-x) v)" using has_subgrad assms 
      using \<open>x \<in> A\<close> by blast
    then have "diff_set f A x \<noteq> {}" unfolding diff_set_def unfolding subgradient_def
      using  \<open>x \<in> A\<close> by blast
    have "\<exists> v. \<forall> u \<in> A. f (u) \<ge> f(y) + (inner (u-y) v)" using has_subgrad assms 
      using \<open>y \<in> A\<close>   by blast
    then have "diff_set f A y \<noteq> {}" unfolding diff_set_def unfolding subgradient_def
      using  \<open>y  \<in> A\<close>  by blast

    have "\<forall> v \<in> diff_set f A x.  f x - f y  \<le> \<rho> * dist x y"
    proof 
      fix v
      assume "v \<in> diff_set f A x"

      then have "  f (y) \<ge> f(x) + inner (y-x) v" using `y\<in> A` 1 by auto
      then have  " f x - f y \<le> inner (x - y) v" 
        using   inner_minus_left minus_diff_eq by smt
      also have " inner (x - y) v \<le> norm ( x - y) * norm v" 
        using norm_cauchy_schwarz by blast
      also have " norm (x - y) * norm v \<le> norm (x- y) * \<rho>" 
        using bound_norm `v \<in> diff_set f A x`  \<open>x \<in> A\<close> mult_left_mono norm_ge_zero by blast
      finally have "f x - f y \<le>  \<rho> * norm (x- y)" 
        by (simp add: mult.commute)
      then show " f x - f y  \<le> \<rho> * dist x y" 
        by (simp add: dist_norm)
    qed
    then have "f x - f y  \<le> \<rho> * dist x y" using `diff_set f A x \<noteq> {}` by auto

    have "\<forall> v \<in> diff_set f A y.  f y - f x  \<le> \<rho> * dist y x"
    proof 
      fix v
      assume "v \<in> diff_set f A y"

      then have "  f (x) \<ge> f(y) + inner (x-y) v" using `x\<in> A` 2 by auto
      then have  " f y - f x \<le> inner (y - x) v" 
        using   inner_minus_left minus_diff_eq by smt
      also have " inner (y - x) v \<le> norm (y - x) * norm v" 
        using norm_cauchy_schwarz by blast
      also have " norm (y - x) * norm v \<le> norm (y - x) * \<rho>" 
        using bound_norm `v \<in> diff_set f A y`  \<open>y \<in> A\<close> mult_left_mono norm_ge_zero by blast
      finally have "f y - f x \<le>  \<rho> * norm (y- x)" 
        by (simp add: mult.commute)
      then show " f y - f x  \<le> \<rho> * dist y x" 
        by (simp add: dist_norm)
    qed
    then have "f y - f x  \<le> \<rho> * dist x y" using `diff_set f A y \<noteq> {}`
      by (simp add: diff_set_def dist_commute)
    then show " dist (f x) (f y)  \<le> \<rho> * dist x y" using `f x - f y  \<le> \<rho> * dist x y` 
      by (simp add: dist_norm)
  qed
  then show "\<rho>-lipschitz_on A f" unfolding lipschitz_on_def using `\<rho> \<ge> 0` by auto
next
  assume "\<rho>-lipschitz_on A f"
  then have 1: "\<forall>x\<in>A. \<forall>y\<in>A. dist (f x) (f y) \<le> \<rho> * dist x y"
    unfolding lipschitz_on_def using `\<rho> \<ge> 0` by auto
  show "\<forall> w \<in> A. \<forall> v \<in> diff_set f A w. norm (v) \<le> \<rho>"
  proof (rule)+
    fix w
    assume "w \<in> A"
    fix v
    assume "v \<in> diff_set f A w"
    show " norm v \<le> \<rho>"
    proof (cases "norm v = 0")
      case True
      then show ?thesis using `\<rho> \<ge> 0` by auto
    next
      case False
      then have "norm v > 0" by auto 
      have "\<exists>e>0. ball w e \<subseteq> A" using `open A` open_contains_ball 
        using \<open>w \<in> A\<close> by blast
      then obtain e where "e>0" " ball w e \<subseteq> A" by auto
      then obtain e' where "e' > 0" "e' < e" by (meson field_lbound_gt_zero)
      let ?u = "w + (e' / (norm v)) *\<^sub>R v"

      have " norm ((e' / (norm v)) *\<^sub>R v) = e'"  using `norm v > 0`  `e' > 0`  by auto
      then have "dist w ?u = e'" 
        by (simp add: dist_norm)

      then have "?u \<in> ball w e" by (simp add: \<open>e' < e\<close>)
      then have "?u \<in> A"  using \<open>ball w e \<subseteq> A\<close> by blast

      have "inner (?u - w) v = inner ((e'/norm v) *\<^sub>R v) v" by auto
      also have "\<dots> = (e'/norm v) * (inner v v)" 
        using inner_scaleR_left by blast
      also have " \<dots> = (e'/norm v) * norm v * norm v" 
        by (metis mult.assoc norm_cauchy_schwarz_eq)
      also have " \<dots> = e' * norm v" by auto
      finally have "inner (?u - w) v  = e' * norm v" by auto

      have "f ?u - f w \<ge> inner (?u - w) v" 
        using  `v \<in> diff_set f A w` unfolding diff_set_def unfolding subgradient_def
        using `?u \<in> A`  by auto
      then have "f ?u - f w \<ge> e' * norm v" using `inner (?u - w) v  = e' * norm v` by auto

      have "\<rho> * e' = \<rho> * norm (?u - w)" using `dist w ?u = e' `
        by (simp add: dist_norm)
      then have "\<rho> * e' \<ge> norm (f ?u - f w)" using 1 `?u \<in> A` `w \<in> A` dist_norm
        by metis
      then have "\<rho> * e' \<ge> f ?u - f w" by auto
      then  have " \<rho> * e' \<ge>  e' * norm v" using `f ?u - f w \<ge> e' * norm v`
        by linarith
      then show "\<rho> \<ge> norm v"
        using \<open>0 < e'\<close> by auto
    qed
  qed
qed

lemma 
  fixes A :: "'a::euclidean_space set"
  shows "\<forall> w \<in> A. \<exists> v. \<forall> u \<in> A. (\<lambda> z. hinge_loss z (x,y)) u \<ge> 
      (\<lambda> z. hinge_loss z (x,y)) w + (inner (u-w) v)"
proof
  fix w
  assume "w \<in> A"
  show " \<exists> v. \<forall> u \<in> A.  hinge_loss u (x,y)  \<ge> 
      hinge_loss w (x,y) + (inner (u-w) v)"
  proof(cases "1 - y * inner w x \<le> 0")
    case True
    have "\<forall> u. hinge_loss u (x,y)  \<ge> 
      hinge_loss w (x,y)" unfolding hinge_loss.simps using True
      by auto
    then have "\<forall> u. hinge_loss u (x,y)  \<ge> 
      hinge_loss w (x,y) + (inner (u-w) 0)" by auto
    then show ?thesis 
      by blast
  next
    case False
    have " hinge_loss w (x,y) = 1 - y * inner w x" using hinge_loss.simps False by auto

    have " \<forall> u \<in> A.  hinge_loss u (x,y)  \<ge> 
      hinge_loss w (x,y) + (inner (u-w) (- y *\<^sub>R x))"
    proof
      fix u
      assume "u\<in> A"
      have " hinge_loss u (x,y) \<ge> 1 - y * ( inner u x )" using hinge_loss.simps by auto
      also have "1 - y * ( inner u x ) =  1 - y * ( inner w x +  inner (u-w) x)"
        by (simp add: inner_diff_left )
      also have " \<dots> =  1 - y * inner w x - y * inner (u-w) x"
        by (simp add: distrib_left)
      also have " \<dots> =  hinge_loss w (x,y) + (inner (u-w) (- y *\<^sub>R x))" 
        using \<open>hinge_loss w (x, y) = 1 - y * (w \<bullet> x)\<close> by auto
      finally show "hinge_loss u (x,y)  \<ge> 
      hinge_loss w (x,y) + (inner (u-w) (- y *\<^sub>R x))" by auto
    qed
    then show ?thesis
      by blast
  qed
qed


lemma abv:
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
    proof (cases "1 - y * inner u x \<le> 0")
      case True
      then show ?thesis
      proof(cases "1 - y * inner v x \<le> 0")
        case True
        have "abs (?f u - ?f v) = 0" using True `1 - y * inner u x \<le> 0` by auto
        then show ?thesis by auto
      next
        case False
        have "?f v \<ge> 0" by auto
        have "abs(?f u - ?f v) = abs (?f v)" using  `1 - y * inner u x \<le> 0` by auto

        also have "abs (?f v) \<le> abs (?f v - 1 + y * inner u x)" using False `1 - y * inner u x \<le> 0`
          using `?f v \<ge> 0` by linarith
        also have "abs (?f v - 1 + y * inner u x) \<le> abs (- y * inner v x + y * inner u x)" 
          using False by auto
        also have " abs (- y * inner v x + y * inner u x) = abs ( y * (inner u x - inner v x))"
          by (metis add.commute minus_mult_commute ring_normalization_rules(2) vector_space_over_itself.scale_right_distrib)
        also have " abs ( y * (inner u x - inner v x)) =  abs ( y * (inner (u-v) x))" 
          by (simp add: inner_diff_left)
        also have "abs ( y * (inner (u-v) x)) = abs y * abs (inner (u-v) x)" 
          using abs_mult by blast
        also have "abs y * abs (inner (u-v) x) = abs (inner (u-v) x)" using assms by auto
        also have "abs (inner (u-v) x) \<le> norm (u-v) * norm x"
          using Cauchy_Schwarz_ineq2 by blast
        finally show ?thesis
          by (simp add: mult.commute)
      qed
    next
      case False
      then show ?thesis
      proof (cases "1 - y * inner v x \<le> 0")
        case True
        have "?f u \<ge> 0" by auto
        have "abs(?f u - ?f v) = abs (?f u)" using  `1 - y * inner v x \<le> 0` by auto
        also have "abs (?f u) \<le> abs (?f u - 1 + y * inner v x)" using False `1 - y * inner v x \<le> 0`
          using `?f u \<ge> 0` by linarith
        also have "abs (?f u - 1 + y * inner v x) \<le> abs (- y * inner v x + y * inner u x)" 
          using False by auto
        also have " abs (- y * inner v x + y * inner u x) = abs ( y * (inner u x - inner v x))"
          by (metis add.commute minus_mult_commute ring_normalization_rules(2) vector_space_over_itself.scale_right_distrib)
        also have " abs ( y * (inner u x - inner v x)) =  abs ( y * (inner (u-v) x))" 
          by (simp add: inner_diff_left)
        also have "abs ( y * (inner (u-v) x)) = abs y * abs (inner (u-v) x)" 
          using abs_mult by blast
        also have "abs y * abs (inner (u-v) x) = abs (inner (u-v) x)" using assms by auto
        also have "abs (inner (u-v) x) \<le> norm (u-v) * norm x"
          using Cauchy_Schwarz_ineq2 by blast
        finally show ?thesis
          by (simp add: mult.commute)
      next
        case False
        have "abs(?f u - ?f v)  \<le> abs (?f u - 1 + y * inner v x)"
          by simp
        also have "abs (?f u - 1 + y * inner v x) \<le> abs (- y * inner v x + y * inner u x)" 
          using False by auto
        also have " abs (- y * inner v x + y * inner u x) = abs ( y * (inner u x - inner v x))"
          by (metis add.commute minus_mult_commute ring_normalization_rules(2) vector_space_over_itself.scale_right_distrib)
        also have " abs ( y * (inner u x - inner v x)) =  abs ( y * (inner (u-v) x))" 
          by (simp add: inner_diff_left)
        also have "abs ( y * (inner (u-v) x)) = abs y * abs (inner (u-v) x)" 
          using abs_mult by blast
        also have "abs y * abs (inner (u-v) x) = abs (inner (u-v) x)" using assms by auto
        also have "abs (inner (u-v) x) \<le> norm (u-v) * norm x"
          using Cauchy_Schwarz_ineq2 by blast
        finally show ?thesis
          by (simp add: mult.commute)
      qed
    qed
  qed
  then show ?thesis unfolding lipschitz_on_def
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
  shows "\<forall>z \<in> D. convex_on H (\<lambda> h. hinge_loss h z)"
proof
  fix z
  assume "z \<in> D"
  show " convex_on H (\<lambda> h. hinge_loss h z)" unfolding hinge_loss.simps
  proof(rule)+
    fix t
    fix x
    fix y
    assume " 0 < (t::real)"
    assume " t < 1"
    assume " x \<in> H"
    assume " y \<in> H"
    have 1 : "(1 - t) *(1 - snd z * (x \<bullet> fst z)) = 
        (1 - t)*1 - (1 - t)* snd z * (x \<bullet> fst z)" 
      by (metis inner_diff_right inner_real_def mult.assoc real_inner_1_right)
    have 2: " t*(1 - snd z * (y \<bullet> fst z)) = 
       t*1 - t* snd z * (y \<bullet> fst z)"
      by (metis inner_diff_right inner_real_def mult.assoc real_inner_1_right)
    have "(1 - t) *
          max 0 (1 - snd z * (x \<bullet> fst z)) +
          t * max 0 (1 - snd z * (y \<bullet> fst z)) \<ge> 
         
          max 0  (1 - t) *(1 - snd z * (x \<bullet> fst z)) +
           max 0 t*(1 - snd z * (y \<bullet> fst z))" 
      by (smt \<open>0 < t\<close> \<open>t < 1\<close> inner_minus_right inner_real_def mult_pos_neg)
    also have " \<dots> \<ge> max 0 ((1 - t) *(1 - snd z * (x \<bullet> fst z)) + 
                            t*(1 - snd z * (y \<bullet> fst z)))" 
      using \<open>0 < t\<close> \<open>t < 1\<close> calculation by auto
    have "  max 0 ((1 - t) *(1 - snd z * (x \<bullet> fst z)) + 
                            t*(1 - snd z * (y \<bullet> fst z)))
             =  max 0 (1 - t - (1 - t)* snd z * (x \<bullet> fst z) + 
                            t - t* snd z * (y \<bullet> fst z))"
      using 1 2 by auto
    also  have " max 0 (1 - t - (1 - t)* snd z * (x \<bullet> fst z) + 
                            t - t* snd z * (y \<bullet> fst z)) =
         max 0 (1  - (1 - t)* snd z * (x \<bullet> fst z) + 
                             - t* snd z * (y \<bullet> fst z))" by auto
    also have " \<dots> =  max 0 (1  -  snd z * ((1 - t)*\<^sub>R x \<bullet> fst z) 
                             - snd z * (t *\<^sub>R y \<bullet>  fst z))" 
      by (simp add: mult.assoc mult.left_commute)
    also have " \<dots> = max 0 (1  -  snd z * (((1 - t)*\<^sub>R x \<bullet> fst z) 
                             +  (t *\<^sub>R y \<bullet>  fst z)))" 
      by (simp add: distrib_left)
    finally show " max 0
        (1 -
         snd z *
         (((1 - t) *\<^sub>R x + t *\<^sub>R y) \<bullet> fst z))
       \<le> (1 - t) *
          max 0 (1 - snd z * (x \<bullet> fst z)) +
          t * max 0 (1 - snd z * (y \<bullet> fst z))" 
      by (metis (mono_tags, hide_lams) \<open>max 0 ((1 - t) * (1 - snd z * (x \<bullet> fst z)) + t * (1 - snd z * (y \<bullet> fst z))) = max 0 (1 - t - (1 - t) * snd z * (x \<bullet> fst z) + t - t * snd z * (y \<bullet> fst z))\<close> \<open>max 0 ((1 - t) * (1 - snd z * (x \<bullet> fst z)) + t * (1 - snd z * (y \<bullet> fst z))) \<le> (1 - t) * max 0 (1 - snd z * (x \<bullet> fst z)) + t * max 0 (1 - snd z * (y \<bullet> fst z))\<close> \<open>max 0 (1 - (1 - t) * snd z * (x \<bullet> fst z) + - t * snd z * (y \<bullet> fst z)) = max 0 (1 - snd z * ((1 - t) *\<^sub>R x \<bullet> fst z) - snd z * (t *\<^sub>R y \<bullet> fst z))\<close> \<open>max 0 (1 - snd z * ((1 - t) *\<^sub>R x \<bullet> fst z) - snd z * (t *\<^sub>R y \<bullet> fst z)) = max 0 (1 - snd z * ((1 - t) *\<^sub>R x \<bullet> fst z + t *\<^sub>R y \<bullet> fst z))\<close> \<open>max 0 (1 - t - (1 - t) * snd z * (x \<bullet> fst z) + t - t * snd z * (y \<bullet> fst z)) = max 0 (1 - (1 - t) * snd z * (x \<bullet> fst z) + - t * snd z * (y \<bullet> fst z))\<close> add.commute  inner_commute inner_left_distrib inner_real_def inner_scaleR_left inner_scaleR_right)
  qed
qed

lemma hinge_loss_pos:
  fixes H :: "'a::euclidean_space set"
    and D :: "('a \<times> real) pmf"
  shows "\<forall>h\<in>H. \<forall>z\<in>D. hinge_loss h z \<ge> 0"
  by auto



end

