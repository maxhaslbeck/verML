theory Subgradients
  imports hinge_loss
begin


definition subgradient :: "  ('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set \<Rightarrow> 
          'a::euclidean_space \<Rightarrow> 'a::euclidean_space \<Rightarrow> bool " where
  "subgradient f H' w v = (w \<in> H' \<and> ( \<forall> u \<in> H'. f (u) \<ge> f(w) + (inner (u-w) v)))"

definition diff_set :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a::euclidean_space set \<Rightarrow> 
          'a::euclidean_space \<Rightarrow> 'a::euclidean_space set" where
  "diff_set f H' w = {h. subgradient f H' w h}"



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




end

