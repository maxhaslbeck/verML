\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory Expectation_over_samples
  imports "RLM_learn" "PMF_expectation"
begin


paragraph \<open>Summary\<close>
text \<open>In this theory we prove major theorem about the expectation 
of the difference of between prediction and error loss of the minimezer
of the regularization loss function. The informal proof can be found in UN
as Theorem 13.2. 
There are also general lemmas about expectations over a sample dataset.
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

context learning_basics_loss
begin

lemma fun_upd_similar : "\<forall>i. \<forall> j \<noteq> i. l v (S' j) = l v ((S'(i:= z)) j)"
  by simp

lemma sum_split :"\<forall>i \<in>{0..<n}. sum f {0..<n} = sum f {0..<i} + f i + sum f {i+1..<n}"
  for f :: "nat \<Rightarrow> real"
  using  sum.atLeastLessThan_concat sum.atLeast_Suc_lessThan
  by (smt One_nat_def Suc_leI add.right_neutral add_Suc_right atLeastLessThan_iff le_add1 order_trans)

lemma sum_of_fun_upd_eq_without_updated_value :
  assumes" i \<notin> A"
  shows "sum (\<lambda> j.  l v (S' j)) A = sum (\<lambda> j. l v ((S'(i:= z)) j)) A"
  using assms  fun_upd_similar
  by (metis (mono_tags, lifting) sum.cong)

lemma argmin_in_hypotheis_set: 
  assumes "S \<in> (Samples n D)"
  shows "(ridge_mine S k) \<in> H"
proof -
  have "(ridge_mine S k) \<in> (ridge_argmin S k)"
    using ridge_min_el_is_argmin  k_pos assms by blast 
  then show ?thesis
    by (simp add: is_arg_min_linorder ridge_argmin_def)
qed

lemma truncated_fun_has_same_min:
  shows "(ridge_mine (trunc_fun S n) k)  =  (ridge_mine S k)"
proof -
  let ?S' = "(S(n:=undefined))"
  have "train_err_loss S n l  =  train_err_loss ?S' n l "
    unfolding train_err_loss_def by auto
  then  have "ridge_fun S k = ridge_fun ?S' k" 
    by simp
  then show ?thesis 
    using ridge_argmin_def ridge_mine_def trunc_fun_def by auto
qed

text \<open>If we swap two values for our m drawn data points,
 then the probability over a dataset with m samples, will be the same.
This means it doesn't matter in what order we draw the samples.\<close>
lemma pmf_swapped_fun_values_same:
  assumes m_pos: "m > 0"
  shows "\<forall> i \<in> {0..<m}. pmf (Samples m D) f  = pmf (Samples m D) (swapped_fun f i (m-1)) "
  unfolding swapped_fun_def
proof 
  fix i
  assume "i \<in> {0..<m}"
  let ?f' = "(f(i:=(f (m-1)),(m-1):=(f i)))"
  let ?Dn1 = "Samples (m) D"
  let ?I = "{0..<m}"
  have "finite ?I" by auto
  have "finite {i,(m-1)}" by auto

  have pmf_of_f: "pmf ?Dn1 f = (if (\<forall>x. x \<notin> ?I \<longrightarrow> f x = undefined) then
           \<Prod>x\<in>?I. pmf ((\<lambda>_. D) x) (f x) else 0)"
    unfolding Samples_def
    using pmf_Pi[of ?I undefined "(\<lambda>_. D)" f] by blast

  have pmf_of_f': "pmf ?Dn1 ?f' = 
        (if (\<forall>x. x \<notin> ?I \<longrightarrow> ?f' x = undefined) then
           \<Prod>x\<in>?I. pmf ((\<lambda>_. D) x) (?f' x) else 0)"
    unfolding Samples_def
    using pmf_Pi[of ?I undefined "(\<lambda>_. D)" "?f'"] by blast

  show "pmf ?Dn1 f  = pmf ?Dn1 ?f'"
  proof (cases "(\<forall>x. x \<notin> ?I \<longrightarrow> f x = undefined)")
    case True
    have "(\<Prod>x\<in>?I. pmf D (f x)) = (\<Prod>x\<in>?I. pmf D (?f' x))"
    proof(cases "i=(m-1)")
      case True
      then show ?thesis by auto
    next
      case False
      have inter_empty: "(?I - {i,(m-1)}) \<inter> {i,(m-1)} = {}" by auto
      have union_I : "(?I - {i,(m-1)}) \<union> {i,(m-1)} = ?I"
        using Diff_cancel \<open>i \<in> ?I\<close> by auto

      have " (\<Prod>x\<in>(?I - {i,(m-1)}). pmf D (?f' x)) * (\<Prod>x\<in>{i,(m-1)}.(pmf D (?f' x))) = 
                (\<Prod>x\<in>(?I - {i,(m-1)}). pmf D (f x)) * (\<Prod>x\<in>{i,(m-1)}.(pmf D (f x)))"
        using prod.union_disjoint False 
        by auto
      then show ?thesis 
        using `finite {i,(m-1)}` `finite ?I`  inter_empty union_I prod.union_disjoint  finite_Diff 
        by metis
    qed
    then show ?thesis 
      using pmf_of_f pmf_of_f' True \<open>i \<in> {0..<m}\<close> fun_upd_other  by auto 
  next
    case False
    have "pmf ?Dn1 f = 0" 
      using False pmf_of_f by auto
    also have "pmf ?Dn1 ?f' = 0"
      using pmf_of_f' False fun_upd_other  \<open>i \<in> ?I\<close> by auto
    finally  show ?thesis  by linarith
  qed
qed

text \<open>swapping two values is injective function.\<close>
lemma inj_swapped: "inj (\<lambda> S. swapped_fun S i m)"
proof (rule)
  fix x
  fix y
  show " x \<in> UNIV \<Longrightarrow> y \<in> UNIV \<Longrightarrow> swapped_fun x i m = swapped_fun y i m \<Longrightarrow> x = y"
  proof
    fix xa
    assume "x \<in> UNIV"
    assume "y \<in> UNIV"
    assume "swapped_fun x i m = swapped_fun y i m"
    then show "x xa = y xa"
      unfolding swapped_fun_def
      by (smt  fun_upd_eqD fun_upd_triv fun_upd_twist)
  qed
qed

lemma pmf_pos:
  fixes m :: nat
  assumes m_pos: "m>0" 
  assumes pmf_pos: "pmf (Samples m D) f > 0"
  shows " \<forall> i. i \<notin> {0..<m} \<longrightarrow> f i = undefined"
proof -
  have "pmf (Pi_pmf {0..<m} undefined (\<lambda> _.D)) f > 0" 
    using pmf_pos
    unfolding Samples_def by auto
  then show ?thesis
    using pmf_Pi_outside[of "{0..<m}" f undefined "(\<lambda> _. D)"] by auto
qed

text \<open>if we change the drawing process by swapping the order, 
then for a fived set of samples, we will have the same probability. \<close>
lemma map_pmf_swap_same: 
  assumes m_pos: "m > 0"
  assumes "i  \<in> {0..<m}"
  shows " pmf (Samples m D) x =
         pmf (map_pmf (\<lambda> S. swapped_fun S i (m-1)) (Samples m D)) x" 
proof -
  let ?M = "(Samples m D)"
  let ?f = "(\<lambda> S. swapped_fun S i (m-1))"

  have "pmf ?M x = pmf ?M (?f x) " 
    using  pmf_swapped_fun_values_same[of m x] swapped_fun_def m_pos 
    by (metis \<open>i \<in> {0..<m}\<close>)
  also have "\<dots> = pmf (map_pmf ?f ?M) (?f (swapped_fun x i (m-1)))" 
    using  inj_swapped[of i "(m-1)"] pmf_map_inj' by metis
  also have " \<dots> =  pmf (map_pmf ?f ?M) x" 
    by (simp add: swapped_fun_def)
  then show "pmf ?M x = pmf (map_pmf ?f ?M) x"
    using calculation by linarith
qed

text \<open>Using the previous lemma we can conclude then that the 
expectation over such changed order of drawings is the same\<close>
lemma expect_sample_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
  assumes m_pos: "m > 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "measure_pmf.expectation (Samples m D) f  =
           measure_pmf.expectation (map_pmf (\<lambda> S. swapped_fun S i (m-1)) (Samples m D)) f"
proof -
  let ?M = "(Samples m D)"
  let ?M_swap = "(map_pmf (\<lambda> S. swapped_fun S i (m-1)) (Samples m D))"

  have "integral\<^sup>L ?M f  =  infsetsum (\<lambda>x. pmf ?M x * f x) UNIV"
    using pmf_expectation_eq_infsetsum by auto
  also have " \<dots> = infsetsum (\<lambda>x. pmf  ?M_swap x * f x) UNIV"
    using  map_pmf_swap_same i_le_n  by simp
  also have " \<dots> = integral\<^sup>L ?M_swap f "
    using pmf_expectation_eq_infsetsum[of "?M_swap" f] by auto   
  finally show ?thesis  by auto
qed

text \<open>the integrability of a function f is the same
as the one like f, but with swapped values\<close>
lemma integrable_func_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
  assumes m_pos: "m > 0"
  assumes f_nn: "\<forall>x\<in> (Samples m D). f x \<ge> 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "integrable (Samples m D) f  =
          integrable  (Samples m D) (\<lambda> x. f (swapped_fun x i (m-1)))"
proof -
  let ?M = "Samples m D"
  let ?g = "(\<lambda> x. f (swapped_fun x i (m-1)))"
  have "\<forall>x\<in>?M. (swapped_fun x i (m-1)) \<in> ?M" 
    by (metis i_le_n m_pos pmf_swapped_fun_values_same set_pmf_iff)

  then have 1:"\<forall>x \<in> ?M. ennreal (norm (?g x)) = ?g x"
    using f_nn by simp
  have "\<forall>x \<in> ?M. ennreal (norm (f x)) = f x"
    using f_nn by simp
  then have "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) = integral\<^sup>N ?M f"
    by (simp add: AE_measure_pmf_iff nn_integral_cong_AE)
  also have "\<dots> =  integral\<^sup>N (map_pmf (\<lambda>f. swapped_fun f i (m-1)) ?M) f"
    using expect_sample_swap_same[of m i f] i_le_n m_pos
    by (metis map_pmf_swap_same pmf_eqI)
  also have " \<dots> =  integral\<^sup>N ?M ?g" by auto
  also have " \<dots> =  integral\<^sup>N ?M (\<lambda> x. ennreal( norm (?g x)))"
    using 1  by (simp add: AE_measure_pmf_iff nn_integral_cong_AE)
  finally have "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) =
              integral\<^sup>N ?M (\<lambda> x. ennreal( norm(?g x)))" by auto

  then have 2: "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) < \<infinity> \<longleftrightarrow>
       integral\<^sup>N ?M (\<lambda> x. ennreal( norm(?g x))) < \<infinity>" by auto
  have 3: "f \<in> borel_measurable ?M" by auto
  have "?g \<in> borel_measurable ?M" by auto
  then show ?thesis using 2 3 integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed

text \<open>For a function f and f, but with swapped values, 
we have the same expectation over a set with m samples from D\<close>
lemma expect_f_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
  assumes m_pos: "m > 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "measure_pmf.expectation (Samples m D) f  =
           measure_pmf.expectation  (Samples m D) (\<lambda> x. f (swapped_fun x i (m-1)))"
proof -
  have "measure_pmf.expectation (Samples m D) f = 
    measure_pmf.expectation (map_pmf (\<lambda>f. swapped_fun f i (m-1)) (Samples m D)) f"
    using expect_sample_swap_same[of m i f] i_le_n m_pos  by blast
  then show ?thesis by auto
qed


lemma ridge_mine_swap: 
  assumes " i\<in>{0..<n+1}"
  shows "measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine Sz k) (Sz n)) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine (swapped_fun Sz i n) k) (Sz i))"
proof -
  let ?M = " (Samples (n+1) D)"
  let ?f = "(\<lambda> Sz. l (ridge_mine  Sz k) (Sz n))" 

  have " measure_pmf.expectation ?M ?f =
       measure_pmf.expectation ?M (\<lambda> x. ?f (swapped_fun x i n))" 
    using expect_f_swap_same[of "n+1" i ?f] `i\<in> {0..<n+1}`  by auto 

  then show " measure_pmf.expectation ?M ?f =
       measure_pmf.expectation ?M (\<lambda> Sz. l (ridge_mine (swapped_fun Sz i n) k) (Sz i))"
    unfolding swapped_fun_def 
    by (metis (no_types, lifting) Bochner_Integration.integral_cong fun_upd_same)
qed

text \<open>This is one of the more important lemmas.
Here we show E_Dn [ E_D [f]] = E_Dn+1 [f], i.e.
it doesn't matter if we draw n samples and then 1 more, 
or we draw n+1 samples -> We will have the same expectation.\<close>
lemma add_sample_expectation:
  fixes f ::"( _  \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes f_nn: "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows    "measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
      measure_pmf.expectation (Samples (m+1) D) (\<lambda> Sz. f (trunc_fun Sz m) (Sz m))" 
proof -
  let ?pair = "(pair_pmf (Samples m D) D)"
  let ?Dm = "Samples m D"
  have "finite {0..<m}" by auto
  have " m \<notin> {0..<m}" by auto
  have insert_m:"(insert m {0..<m}) = {0..<m+1}" 
    using atLeast0LessThan by auto

  have 1:" integral\<^sup>L ?Dm (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
  integral\<^sup>L ?pair  (\<lambda> (S,z). f S z)" 
    using expectation_pair_pmf'[of ?Dm D f]  f_nn integrable_D by linarith

  have 2: "\<forall>x\<in> ?pair. ((fst x)(m:=undefined)) = (fst x)"
  proof 
    fix x
    assume "x\<in>?pair"
    have "pmf (Samples m D) (fst x) > 0"
      using \<open>x \<in> ?pair\<close> pmf_positive by fastforce
    then have "\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined"
      unfolding Samples_def
      using pmf_Pi_outside
      by (metis finite_atLeastLessThan less_numeral_extra(3))
    then show "((fst x)(m:=undefined)) = (fst x)" by auto
  qed

  have "(map_pmf (\<lambda>(f,y). f(m:=y)) ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D (Samples m D)))) =
    (map_pmf (\<lambda>(y,f). f(m:=y)) ((pair_pmf D (Samples m D))))"
    using map_pmf_comp
    by (smt Pair_inject map_pmf_cong prod.collapse split_beta)

  also have "\<dots> = Samples (m+1) D"
    unfolding Samples_def
    using  `finite {0..<m}` `m \<notin> {0..<m}`  Pi_pmf_insert[of "{0..<m}" m undefined "(\<lambda>_. D)"]
      insert_m by auto

  finally have "integral\<^sup>L ?Dm (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
   integral\<^sup>L (Samples (m+1) D) (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m))"  
    using `finite {0..<m}` `m \<notin> {0..<m}` same_integral_restricted
    by (smt 1 2  fun_upd_same fun_upd_upd integral_map_pmf pair_commute_pmf prod.case_eq_if)

  then show ?thesis using trunc_fun_def by auto
qed


lemma integrable_uniform : "\<forall> S \<in> (Samples n D). integrable D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
  by blast

lemma uniform_nn: "\<forall>S\<in> (Samples n D). \<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
proof (rule)
  fix S
  assume "S\<in> Samples n D"
  have "finite {0..<n}" by auto
  have "{0..<n} \<noteq> {}"
    using n_pos by auto
  have "\<forall> i \<in> {0..<n}. l (ridge_mine S k) (S i) \<ge> 0" 
    using l_nn \<open>S \<in> (Samples n D)\<close> element_of_sample_in_dataset
      argmin_in_hypotheis_set by blast
  then have " sum (\<lambda>i. l (ridge_mine S k) (S i)) {0..<n} / card {0..<n} \<ge> 0"
    by (meson divide_nonneg_nonneg of_nat_0_le_iff sum_nonneg)
  then show "\<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
    using `finite {0..<n}` `{0..<n} \<noteq> {}` 
    by (metis card_atLeastLessThan finite_atLeastLessThan integral_pmf_of_set)
qed


lemma trunc_fun_in_smaller_samples:
  assumes  " S \<in> (Samples (m+1) D)"
  shows "trunc_fun S m \<in> Samples m D"
proof  -
  let ?M = "(Samples (m+1) D)"
  let ?I = "{0..<m}"
  have "finite {0..<m+1}" by auto 
  have "finite ?I" by auto
  then have 1: " pmf ?M S > 0"
    using pmf_positive_iff `S \<in> ?M` by fast 
  then have "\<forall> i. i \<notin> {0..<m+1} \<longrightarrow> S i = undefined" 
    using pmf_pos[of "(m+1)" S] n_pos  by auto
  then have "pmf ?M S = (\<Prod>x\<in>{0..<m+1}. pmf D (S x))"
    using pmf_Pi'[of "{0..<m+1}" S undefined "(\<lambda> _. D)"] `finite {0..<m+1}`  
    by (metis Samples_def)
  then have "\<forall>x \<in> {0..<m+1}.  pmf D (S x) > 0 " 
    by (meson \<open>S \<in> ?M\<close> pmf_positive element_of_sample_in_dataset)
  then have 2: "(\<Prod>x\<in>?I. pmf D (S x)) > 0" 
    by (simp add: prod_pos)
  have "\<And>x. x \<notin> ?I \<Longrightarrow> (trunc_fun S m) x = undefined" 
    by (simp add: \<open>\<forall>i. i \<notin> {0..<m + 1} \<longrightarrow> S i = undefined\<close> trunc_fun_def)
  then have "pmf (Samples m D) (trunc_fun S m) = (\<Prod>x\<in>?I. pmf D (S x))" 
    unfolding Samples_def
    using pmf_Pi'[of ?I "trunc_fun S m" undefined "(\<lambda> _. D)"]  `finite ?I` 
    using trunc_fun_def by auto
  then have "pmf (Samples m D) (trunc_fun S m) > 0" using 2 by auto

  then show "trunc_fun S m \<in> Samples m D"
    by (simp add: set_pmf_iff)
qed

lemma min_of_Dn1_in_H:
  assumes  "S \<in> (Samples (n+1) D)" 
  shows "(ridge_mine S k) \<in> H" 
proof -
  let ?M = "(Samples (n+1) D)"
  have "trunc_fun S n \<in> Samples n D" 
    using  trunc_fun_in_smaller_samples `S \<in> ?M`  by auto
  then have "(ridge_mine (trunc_fun S n) k) \<in> H"
    using argmin_in_hypotheis_set by blast
  then show "(ridge_mine S k) \<in> H" 
    by (simp add: truncated_fun_has_same_min)
qed

text \<open>Lemma 13.02 from UN.\<close>
lemma train_val_diff :
  assumes integrable_D:"\<forall> S \<in> (Samples n D). integrable D (\<lambda> z. l (ridge_mine S k) z)"
  assumes  pred_err_integrable: "integrable (Samples n D) (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  assumes  train_err_integrable: "integrable (Samples n D) (\<lambda> S. train_err_loss S n l (ridge_mine S k)) "
  assumes integrable_swapped_funi: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l (ridge_mine (swapped_fun S i n) k) (S i))))"
  assumes integrable_Si: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l  (ridge_mine S k) (S i))))"
  shows"  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
            =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) -  (l  (ridge_mine S k) (S i))))" 
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

  have pred_err_Dn1: "\<forall> i  \<in> ?I. integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) =
        integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
  proof 
    fix i
    assume "i\<in> ?I"
    have " integral\<^sup>L ?Dn (\<lambda> S. ?pred_err S) = 
        integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> z. (l (ridge_mine S k) z)))"
      unfolding pred_err_loss_def by auto
    also have " \<dots> = integral\<^sup>L ?Dn1 (\<lambda> S. ?l_trunc S (S n))"
      using l_nn argmin_in_hypotheis_set  integrable_D add_sample_expectation n_pos by auto
    also  have " \<dots> =  integral\<^sup>L ?Dn1 (\<lambda> S. ?l_Si S n)"
      by (simp add: truncated_fun_has_same_min)
    also have " \<dots> =  integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
      using ridge_mine_swap  `i \<in> ?I` by auto
    finally show " integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) = integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
      by auto
  qed

  then have 1: "integral\<^sup>L ?pmfI (\<lambda> i. integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S)) = 
                integral\<^sup>L ?pmfI (\<lambda> i. integral\<^sup>L ?Dn1 (\<lambda> S. ?l_swapped i S))"
    using pmf_restrict fin_I non_empty_I set_pmf_of_set
    by (smt same_integral_restricted)

  have " integral\<^sup>L ?pmfI  (\<lambda> i.  integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)) =
   integral\<^sup>L ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )"
  proof -
    have "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I.(ridge_mine (swapped_fun S i n) k) \<in> H" 
      using min_of_Dn1_in_H pmf_swapped_fun_values_same n_pos 
      by (smt add_diff_cancel_right' add_gr_0 atLeastLessThan_iff less_add_same_cancel1 less_trans
          set_pmf_iff swapped_fun_def zero_less_one) 
    then have l_swapped_nn: "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I. ?l_swapped i S \<ge> 0"
      using l_nn element_of_sample_in_dataset by auto

    have I_swap: 
      "\<forall> i\<in> ?I. \<forall> j \<in> ?I. integral\<^sup>L ?Dn1 (\<lambda> S. ?l_swapped i S) =
       integral\<^sup>L ?Dn1 (\<lambda> S. ?l_swapped j S)" 
      using ridge_mine_swap 
      by (metis (no_types, lifting) pred_err_Dn1)
    then show ?thesis using fin_I non_empty_I 
        l_swapped_nn swap_set_expectation[of ?Dn1 ?I ?l_swapped]
      by linarith
  qed

  then have 2: "integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) =
       integral\<^sup>L ?Dn1  (\<lambda> Sz. integral\<^sup>L ?pmfI (\<lambda> i. ?l_swapped i Sz) )"
    using 1 by simp

  have "\<forall>S. \<forall>i\<in>?I. (trunc_fun S n) i = S i"  using  trunc_fun_def by auto 

  then  have 4: "\<forall>S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (trunc_fun S n i)) =
               integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))" 
    by (metis (no_types, lifting) fin_I non_empty_I same_integral_restricted set_pmf_of_set)

  have "n>0" using n_pos by auto
  then have 5: "integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S))) =
      integral\<^sup>L ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (trunc_fun S n i)))"
    using 
      integrable_uniform uniform_nn add_sample_expectation[of n " (\<lambda> S. (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S)))"]   by blast

  have "card ?I = n" by auto
  then have "\<forall> S. integral\<^sup>L ?pmfI (\<lambda>i. l (ridge_mine S k) (S i) ) =
      (sum (?l_Si S) ?I) / card ?I"
    using integral_pmf_of_set `finite ?I` `?I \<noteq> {}` by blast
  then have "\<forall> S. train_err_loss S n l (ridge_mine S k) = 
      integral\<^sup>L ?pmfI (?l_Si S)" 
    using `card ?I = n` train_err_loss_def by force

  then have 6:" integral\<^sup>L ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k)) 
            =  integral\<^sup>L ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))"
    using 4 5  truncated_fun_has_same_min  by auto 

  have "integral\<^sup>L ?Dn 
          (\<lambda> S.   ?pred_err S - train_err_loss S n l (ridge_mine S k)) = 
       integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) -
       integral\<^sup>L ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k))   "  
    using train_err_integrable  pred_err_integrable by simp

  also have " \<dots>  =
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI 
   (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)))) - 
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))" using 2 6 by auto
  also have " \<dots> =   integral\<^sup>L ?Dn1 (\<lambda> S.  
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) ) -
  integral\<^sup>L ?pmfI (?l_Si S)  )" 
    using integrable_Si integrable_swapped_funi  by simp
  also have " \<dots> = 
     integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_fun S i n) k) (S i)) - (?l_Si S i) ) )"
  proof -
    have "\<forall> S. sum (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) ) ?I -  sum (?l_Si S) ?I  =
    sum (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) - (?l_Si S i) ) ?I"
      by (simp add: sum_subtractf)
    then  have "\<forall> S.
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_fun S i n) k) (S i)) )  -
 integral\<^sup>L ?pmfI (?l_Si S) =
    integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_fun S i n) k) (S i)) -  (?l_Si S i) )" using non_empty_I
      by (metis (no_types, lifting) diff_divide_distrib fin_I integral_pmf_of_set)
    then show ?thesis by auto
  qed
  finally show ?thesis by blast
qed

lemma ridge_index_swap_same: 
  shows "ridge_mine ( S(i:= (S n))) k =
                    ridge_mine (swapped_fun S i n) k"
  using truncated_fun_has_same_min using fun_upd_swap_same_if_truncated 
  by metis


lemma add_sample_integrable:
  fixes f ::"( _  \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes f_nn: "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows    "integrable (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
      integrable (Samples (m+1) D) (\<lambda> Sz. f (trunc_fun Sz m) (Sz m))" 
proof -
  let ?pair = "(pair_pmf (Samples m D) D)"
  let ?Dm = "Samples m D"
  let ?Dm1 = "Samples (m+1) D"
  let ?trunc_S = "(\<lambda> Sz. f (Sz(m:=undefined)) (Sz m))"
  have "finite {0..<m}" by auto
  have " m \<notin> {0..<m}" by auto
  have insert_m:"(insert m {0..<m}) = {0..<m+1}" 
    using atLeast0LessThan by auto
  have 1:"\<forall> S \<in> ?Dm. integral\<^sup>L D (f S) =  enn2real (integral\<^sup>N D (f S))"
    using integrable_D f_nn  
    by (metis (mono_tags, lifting) AE_measure_pmf_iff enn2real_ennreal 
        integral_nonneg_AE nn_integral_cong nn_integral_eq_integral)

  have 2:"\<forall> S \<in> ?Dm. ennreal (integral\<^sup>L D (f S)) =  (integral\<^sup>N D (f S))"
    using integrable_D f_nn 
    by (metis (mono_tags, lifting) AE_measure_pmf_iff  nn_integral_cong nn_integral_eq_integral)

  then have 3:"integral\<^sup>N ?Dm (\<lambda> S. integral\<^sup>N D (f S)) =  integral\<^sup>N ?Dm (\<lambda> S. integral\<^sup>L D (f S))"
    using same_nn_integral_restricted_ennreal[of ?Dm "(\<lambda> S. ( integral\<^sup>N D (f S)))" 
        "(\<lambda> S. integral\<^sup>L D (f S))"]  by auto

  have 4:" integral\<^sup>N ?Dm (\<lambda> S. integral\<^sup>N D (f S)) = integral\<^sup>N ?pair  (\<lambda> (S,z). f S z)"
    using nn_integral_pair_pmf'[of ?Dm D "(\<lambda> (S,z). f S z)"]
    by auto

  have 5: "\<forall>x\<in> ?pair. ((fst x)(m:=undefined)) = (fst x)"
  proof 
    fix x
    assume "x\<in>?pair"
    have "pmf ?Dm (fst x) > 0" using \<open>x \<in> ?pair\<close>
      using pmf_positive by fastforce
    then have "\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined"
      unfolding Samples_def using pmf_Pi_outside
      by (metis finite_atLeastLessThan less_numeral_extra(3))
    then show "((fst x)(m:=undefined)) = (fst x)" by auto
  qed

  have "integral\<^sup>N ?pair (\<lambda>x \<in> ?pair.  f (fst x) (snd x)) =
      integral\<^sup>N ?pair (\<lambda>x.  f (fst x) (snd x))"  
    using nn_integral_restrict_space_eq_restrict_fun by metis
  then have 6:" integral\<^sup>N ?pair (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x)) =
     integral\<^sup>N ?pair (\<lambda>x.  f (fst x) (snd x))" 
    by (simp add: 5 same_nn_integral_restricted_ennreal)

  have "(map_pmf (\<lambda>(f,y). f(m:=y)) ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D ?Dm))) =
    (map_pmf (\<lambda>(y,f). f(m:=y)) ((pair_pmf D ?Dm)))" using map_pmf_comp
    by (smt Pair_inject map_pmf_cong prod.collapse split_beta)

  also have "\<dots> = ?Dm1" 
    unfolding Samples_def
    using  `finite {0..<m}` `m \<notin> {0..<m}`  Pi_pmf_insert[of "{0..<m}" m undefined "(\<lambda>_. D)"]
      insert_m by auto

  finally have[simp]: " integral\<^sup>N ?pair  (\<lambda> (S,z). f S z) = integral\<^sup>N ?Dm1 ?trunc_S"
    using `finite {0..<m}` `m \<notin> {0..<m}` same_integral_restricted
      5 6 fun_upd_same fun_upd_upd nn_integral_map_pmf pair_commute_pmf prod.case_eq_if
    by (smt  nn_integral_cong)

  have "integral\<^sup>N ?Dm (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
      integral\<^sup>N (?Dm1) (\<lambda> Sz. f (trunc_fun Sz m) (Sz m))" using 3 4 
    by (simp add: trunc_fun_def)
  also have "\<dots> = integral\<^sup>N (?Dm1) (\<lambda> Sz. (norm (f (trunc_fun Sz m) (Sz m))))" 
    using  trunc_fun_in_smaller_samples f_nn element_of_sample_in_dataset
    by (simp add: same_nn_integral_restricted_ennreal)
  finally have nn_integral_eq: " integral\<^sup>N ?Dm (\<lambda> S. ennreal( norm ( integral\<^sup>L D (\<lambda> z. f S z)))) =
       integral\<^sup>N (?Dm1) (\<lambda> Sz. (norm (f (trunc_fun Sz m) (Sz m))))" 
    using  3 1 2 same_nn_integral_restricted_ennreal 
    by (smt enn2real_nonneg real_norm_def)

  have 8: "(\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) \<in> borel_measurable ?Dm" by auto
  have  "(\<lambda> Sz. f (trunc_fun Sz m) (Sz m)) \<in> borel_measurable (?Dm1)" by auto

  then show ?thesis using trunc_fun_def using nn_integral_eq 8 
      integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed


lemma expect_sample_same:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  assumes "i \<in> {0..<m}"
  shows "measure_pmf.expectation (Samples (m) D) (\<lambda> S.  l h (S (m-1))) = 
  measure_pmf.expectation (Samples (m) D) (\<lambda> S.  l h (S i))"
proof -
  let ?f = "(\<lambda> S. l h (S (m-1)))"
  have "measure_pmf.expectation (Samples m D) ?f  = 
           measure_pmf.expectation  (Samples m D) (\<lambda> x. ?f (swapped_fun x i (m-1)))"
    using expect_f_swap_same[of m i ?f] m_pos `i\<in>{0..<m}` by auto
  then show "measure_pmf.expectation (Samples m D) (\<lambda>S. l h (S (m - 1))) =
     measure_pmf.expectation (Samples m D) (\<lambda>S. l h (S i))" unfolding swapped_fun_def
    by simp
qed

lemma integrable_sample_same:
  fixes m :: "nat"
  assumes m_pos: "m>0" 
  assumes "h\<in>H"
  assumes "i \<in> {0..<m}"
  shows "integrable (Samples m D) (\<lambda> S.  l h (S (m-1))) = 
  integrable (Samples m D) (\<lambda> S.  l h (S i))"
proof -
  let ?f = "(\<lambda> S. l h (S (m-1)))"
  have "(m - 1) \<in> {0..<m}" using m_pos by auto
  have "integrable (Samples m D) ?f  = 
          integrable  (Samples m D) (\<lambda> x. ?f (swapped_fun x i (m-1)))"
    using integrable_func_swap_same[of m  ?f i] m_pos `i\<in>{0..<m}` l_nn 
    using \<open>m - 1 \<in> {0..<m}\<close> assms(2) element_of_sample_in_dataset by blast 
  then show "integrable (Samples m D) (\<lambda>S. l h (S (m - 1))) =
     integrable (Samples m D) (\<lambda>S. l h (S i))" unfolding swapped_fun_def
    by simp
qed


end
end