theory rlm_13_02_lemma
  imports "RLM_learn"
begin

context learning_basics1
begin



lemma S_index_similar : "\<forall>i. \<forall> j \<noteq> i. l v (S' j) = l v ((S_index S' i z) j)"
  by (simp add: S_index_def)

lemma sum_split :"\<forall>i \<in>{0..<n}. sum f {0..<n} = sum f {0..<i} + f i + sum f {i+1..<n}"
  for f :: "nat \<Rightarrow> real"
  by (smt Suc_eq_plus1 ab_semigroup_add_class.add_ac(1)
      atLeastLessThan_iff le_eq_less_or_eq sum.atLeastLessThan_concat sum.atLeast_Suc_lessThan)

lemma S_index_eq_without_i : " i \<notin> A \<Longrightarrow>
     sum (\<lambda> j.  l v (S' j)) A = sum (\<lambda> j. l v ((S_index S' i z) j)) A"
  by (metis (mono_tags, lifting) S_index_similar  sum.cong)

lemma restrict_integral: "integral\<^sup>L M f = integral\<^sup>L M   (restrict f (space M))" 
  by (metis Bochner_Integration.integral_cong restrict_apply)

lemma restrict_nn_integral: "integral\<^sup>N M f = integral\<^sup>N M   (restrict f (space M))" 
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

lemma min_in_H: "S \<in> (Samples n D) \<longrightarrow>  (ridge_mine S k) \<in> H"
proof 
  assume "S \<in> (Samples n D)"
  then have "(ridge_mine S k) \<in> (ridge_argmin S k)"
    using in_argmin  k_pos by blast 
  then show "(ridge_mine S k) \<in> H" 
    by (simp add: is_arg_min_linorder ridge_argmin_def)
qed

lemma truncated_same_min:
  shows "\<forall> S. (ridge_mine (truncated_S S n) k)  =  (ridge_mine S k)"
proof 
  fix S
  show "(ridge_mine (truncated_S S n) k)  =  (ridge_mine  S k)"
  proof -
    let ?S' = "(S(n:=undefined))"

    have "ridge_fun S k = ridge_fun ?S' k" 
    proof 
      fix xa 
      have "train_err_loss S n l xa =  train_err_loss ?S' n l xa"
        unfolding train_err_loss_def by auto
      then show "ridge_fun S k xa = ridge_fun ?S' k xa" 
        by simp
    qed
    then show ?thesis 
      using ridge_argmin_def ridge_mine_def truncated_S_def by auto
  qed
qed

lemma pmf_swapped_same:
    assumes m_pos: "m > 0"
    shows "\<forall> i \<in> {0..<m}. pmf (Samples m D) f  = pmf (Samples m D) (f(i:=(f (m-1)),(m-1):=(f i)))"
proof 
  fix i
  assume "i \<in> {0..<m}"
  let ?f' = "(f(i:=(f (m-1)),(m-1):=(f i)))"
  let ?Dn1 = "Samples (m) D"
  let ?I = "{0..<m}"
  have "finite ?I" by auto
  have "finite {i,(m-1)}" by auto

  have 1: "pmf ?Dn1 f = (if (\<forall>x. x \<notin> ?I \<longrightarrow> f x = undefined) then
           \<Prod>x\<in>?I. pmf ((\<lambda>_. D) x) (f x) else 0)"
    unfolding Samples_def
    using pmf_Pi[of ?I undefined "(\<lambda>_. D)" f] by blast

  have 2: "pmf ?Dn1 ?f' = 
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
        using prod.union_disjoint False by auto
      then show ?thesis  using `finite {i,(m-1)}` `finite ?I` 
          inter_empty union_I prod.union_disjoint  finite_Diff by metis   
    qed
    then show ?thesis using 1 2 True 
      using \<open>i \<in> {0..<m}\<close> fun_upd_other by auto 
  next
    case False
    have "pmf ?Dn1 f = 0"  using False "1" by auto
    also have "pmf ?Dn1 ?f' = 0"
      using 2 False fun_upd_other  \<open>i \<in> ?I\<close> by auto
    finally  show ?thesis  by linarith
  qed
qed

lemma inj_swapped: "inj (\<lambda> S. swapped_S S i m)"
proof (rule)
  fix x
  fix y
  show " x \<in> UNIV \<Longrightarrow> y \<in> UNIV \<Longrightarrow> swapped_S x i m = swapped_S y i m \<Longrightarrow> x = y"
  proof
    fix xa
    assume "x \<in> UNIV"
    assume "y \<in> UNIV"
    assume "swapped_S x i m = swapped_S y i m"
    then have "x (i:= x m, m:= x i) = y(i:= y m, m:= y i)" 
      using swapped_S_def by auto
    show "x xa = y xa" 
      by (smt \<open>x(i := x m, m := x i) = y(i := y m, m := y i)\<close> fun_upd_eqD fun_upd_triv fun_upd_twist)
  qed
qed

lemma map_pmf_swap_same: 
    assumes m_pos: "m > 0"
    shows "\<forall>i \<in> {0..<m}. pmf (Samples m D) x =
         pmf (map_pmf (\<lambda> S. swapped_S S i (m-1)) (Samples m D)) x" 
proof 
  fix i
  assume "i \<in> {0..<m}"
  let ?M = "(Samples m D)"
  let ?f = "(\<lambda> S. swapped_S S i (m-1))"

  have "pmf ?M x =pmf ?M (?f x) " 
    using  pmf_swapped_same[of m x] swapped_S_def m_pos  by (metis \<open>i \<in> {0..<m}\<close>)
  also have "\<dots> = pmf (map_pmf ?f ?M) (?f (swapped_S x i (m-1)))" 
    using  inj_swapped[of i "(m-1)"] pmf_map_inj' by metis
  also have " \<dots> =  pmf (map_pmf ?f ?M) x" 
    by (simp add: swapped_S_def)
  then show "pmf ?M x = pmf (map_pmf ?f ?M) x"
    using calculation by linarith
qed

lemma expect_sample_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
   assumes m_pos: "m > 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "measure_pmf.expectation (Samples m D) f  =
           measure_pmf.expectation (map_pmf (\<lambda> S. swapped_S S i (m-1)) (Samples m D)) f"
proof -
  let ?M = "(Samples m D)"
  let ?M_swap = "(map_pmf (\<lambda> S. swapped_S S i (m-1)) (Samples m D))"

  have "integral\<^sup>L ?M f  =  infsetsum (\<lambda>x. pmf ?M x * f x) UNIV"
    using pmf_expectation_eq_infsetsum by auto
  also have " infsetsum (\<lambda>x. pmf ?M x * f x) UNIV = infsetsum (\<lambda>x. pmf  ?M_swap x * f x) UNIV"
    using  map_pmf_swap_same i_le_n  by simp
  also have " infsetsum (\<lambda>x. pmf ?M_swap x * f x) UNIV = integral\<^sup>L ?M_swap f "
    using pmf_expectation_eq_infsetsum[of "?M_swap" f] by auto   
  finally show ?thesis  by auto
qed


lemma integrable_f_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
  assumes m_pos: "m > 0"
  assumes f_nn: "\<forall>x\<in> (Samples m D). f x \<ge> 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "integrable (Samples m D) f  =
          integrable  (Samples m D) (\<lambda> x. f (swapped_S x i (m-1)))"
proof -
  let ?M = "Samples m D"
  let ?g = "(\<lambda> x. f (swapped_S x i (m-1)))"
  have "\<forall>x\<in>?M. (swapped_S x i (m-1)) \<in> ?M" 
    by (metis i_le_n m_pos pmf_eq_0_set_pmf pmf_swapped_same swapped_S_def)
  then have 1:"\<forall>x \<in> ?M. ennreal (norm (?g x)) = ?g x" using f_nn
    by simp
  have "\<forall>x \<in> ?M. ennreal (norm (f x)) = f x" using f_nn by simp
  then have "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) = integral\<^sup>N ?M f"
    by (simp add: AE_measure_pmf_iff nn_integral_cong_AE)
  also have "integral\<^sup>N (Samples m D) f = 
    integral\<^sup>N (map_pmf (\<lambda>f. swapped_S f i (m-1)) (Samples m D)) f"
    using expect_sample_swap_same[of m i f] i_le_n m_pos 
    by (metis map_pmf_swap_same pmf_eqI)
  also have " integral\<^sup>N (map_pmf (\<lambda>f. swapped_S f i (m-1)) (Samples m D)) f =
         integral\<^sup>N (Samples m D) (\<lambda> x. f (swapped_S x i (m-1)))" by auto
  also have " \<dots> =  integral\<^sup>N (Samples m D) (\<lambda> x. ennreal( norm(f (swapped_S x i (m-1)))))"
    using 1  by (simp add: AE_measure_pmf_iff nn_integral_cong_AE)
  finally have "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) =
              integral\<^sup>N (Samples m D) (\<lambda> x. ennreal( norm(f (swapped_S x i (m-1)))))" by auto
  then have 2: "integral\<^sup>N ?M (\<lambda> x. ennreal (norm (f x))) < \<infinity> \<longleftrightarrow>
       integral\<^sup>N (Samples m D) (\<lambda> x. ennreal( norm(f (swapped_S x i (m-1))))) < \<infinity>" by auto
  have 3: "f \<in> borel_measurable ?M" by auto
  have "(\<lambda> x. f (swapped_S x i (m-1))) \<in> borel_measurable ?M" by auto
  then show ?thesis using 2 3 integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed

lemma expect_f_swap_same:
  fixes f :: "_ \<Rightarrow> real"
  fixes m :: "nat"
  assumes m_pos: "m > 0"
  assumes i_le_n: "i \<in> {0..<m}"
  shows "measure_pmf.expectation (Samples m D) f  =
           measure_pmf.expectation  (Samples m D) (\<lambda> x. f (swapped_S x i (m-1)))"
proof -
  have "measure_pmf.expectation (Samples m D) f = 
    measure_pmf.expectation (map_pmf (\<lambda>f. swapped_S f i (m-1)) (Samples m D)) f"
    using expect_sample_swap_same[of m i f] i_le_n m_pos  by blast
  then show ?thesis by auto
qed


lemma ridge_mine_swap: 
  "\<forall> i\<in>{0..<n+1}. measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  Sz k) (Sz n)) =
       measure_pmf.expectation (Samples (n+1) D) (\<lambda> Sz. l (ridge_mine  (swapped_S Sz i n) k) (Sz i))"
proof 
  fix i
  assume "i\<in>{0..<n+1}"
  let ?M = " (Samples (n+1) D)"
  let ?f = "(\<lambda> Sz. l (ridge_mine  Sz k) (Sz n))" 

  have " measure_pmf.expectation ?M ?f =
       measure_pmf.expectation ?M (\<lambda> x. ?f (swapped_S x i n))" 
    using expect_f_swap_same[of "n+1" i ?f] `i\<in> {0..<n+1}`  by auto 

  then show " measure_pmf.expectation ?M ?f =
       measure_pmf.expectation ?M (\<lambda> Sz. l (ridge_mine (swapped_S Sz i n) k) (Sz i))"
    unfolding swapped_S_def 
    by (metis (no_types, lifting) Bochner_Integration.integral_cong fun_upd_same)

qed

lemma same_integral_restricted[simp]:
  fixes f ::"(  _ \<Rightarrow> real)"
  fixes g ::"(  _ \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>L M f = integral\<^sup>L M g"
  by (metis (no_types, lifting) Bochner_Integration.integral_cong assms indicator_simps(2)
      integral_measure_pmf_real_indicator mult_not_zero)



lemma same_nn_integral_restricted:
  fixes f ::"(  _ \<Rightarrow> real)"
  fixes g ::"(  _ \<Rightarrow> real)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
  by (metis (mono_tags, lifting) assms ennreal_0 mult_not_zero nn_integral_cong 
      nn_integral_measure_pmf pmf_eq_0_set_pmf)

lemma same_nn_integral_restricted1:
  fixes f ::"(  _ \<Rightarrow> ennreal)"
  fixes g ::"(  _ \<Rightarrow> ennreal)"
  assumes "\<forall> x \<in> set_pmf M. f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
  by (metis (mono_tags, lifting) assms ennreal_0 mult_not_zero nn_integral_cong 
      nn_integral_measure_pmf pmf_eq_0_set_pmf)

lemma integrable_pair_pmf:
  fixes f ::"( _ \<times> _ \<Rightarrow> real)"
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
  fixes f ::"( _ \<Rightarrow> _ \<Rightarrow> real)"
  assumes f_nn: "AE S in (measure_pmf p) . AE z in (measure_pmf q). f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> p. integrable q (f S)"
  shows "integrable p  (\<lambda> S.  enn2real (\<integral>\<^sup>+ x. f S x \<partial>q)) \<longleftrightarrow>
      integrable (pair_pmf p q) (\<lambda> (S,z). f S z)"
  using integrable_pair_pmf[of  "(\<lambda> (S,z). f S z)"] assms by auto

lemma expectation_pair_pmf:
  fixes f ::"( _ \<times> _ \<Rightarrow> real)"
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


lemma add_sample_expectation:
  fixes f ::"( _  \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes f_nn: "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows    "measure_pmf.expectation (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
      measure_pmf.expectation (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m))" 
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
    have "pmf (Samples m D) (fst x) > 0" using \<open>x \<in> ?pair\<close>
      using pmf_positive by fastforce
    then have "\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined"
      unfolding Samples_def using pmf_Pi_outside
      by (metis finite_atLeastLessThan less_numeral_extra(3))
    then show "((fst x)(m:=undefined)) = (fst x)" by auto
  qed

  have "(map_pmf (\<lambda>(f,y). f(m:=y)) ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D (Samples m D)))) =
    (map_pmf (\<lambda>(y,f). f(m:=y)) ((pair_pmf D (Samples m D))))" using map_pmf_comp
    by (smt Pair_inject map_pmf_cong prod.collapse split_beta)

  also have "\<dots> = Samples (m+1) D" unfolding Samples_def
    using  `finite {0..<m}` `m \<notin> {0..<m}`  Pi_pmf_insert[of "{0..<m}" m undefined "(\<lambda>_. D)"]
      insert_m by auto

  finally have "integral\<^sup>L ?Dm (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
   integral\<^sup>L (Samples (m+1) D) (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m))"  
    using `finite {0..<m}` `m \<notin> {0..<m}` same_integral_restricted
    by (smt 1 2  fun_upd_same fun_upd_upd integral_map_pmf pair_commute_pmf prod.case_eq_if)

  then show ?thesis using truncated_S_def by auto
qed




lemma integrable_uniform : "\<forall> S \<in> (Samples n D). integrable D (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i)))"
  by blast

lemma integrable_train_err : "integrable (Samples n D) 
          (\<lambda> S. train_err_loss S n l (ridge_mine S k))"
  unfolding train_err_loss_def oops

lemma uniform_nn: "\<forall>S\<in> (Samples n D). \<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
proof (rule)
  fix S
  assume "S\<in> Samples n D"
  have "finite {0..<n}" by auto
  have "{0..<n} \<noteq> {}" using n_pos by auto
  have "\<forall> i \<in> {0..<n}. l (ridge_mine S k) (S i) \<ge> 0" 
    using l_pos min_in_H \<open>S \<in> (Samples n D)\<close> sample_in_D by blast
  then have " sum (\<lambda>i. l (ridge_mine S k) (S i)) {0..<n} / card {0..<n} \<ge> 0"
    by (meson divide_nonneg_nonneg of_nat_0_le_iff sum_nonneg)
  then show "\<forall>z\<in>D. (\<lambda> _.  
       measure_pmf.expectation (pmf_of_set {0..<n}) (\<lambda>i. l (ridge_mine S k) (S i))) z \<ge> 0"
    using `finite {0..<n}` `{0..<n} \<noteq> {}` 
    by (metis card_atLeastLessThan finite_atLeastLessThan integral_pmf_of_set)
qed

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

lemma pmf_pos:
  fixes m :: nat
  assumes m_pos: "m>0" 
  assumes pmf_pos: "pmf (Samples m D) f > 0"
  shows " \<forall> i. i \<notin> {0..<m} \<longrightarrow> f i = undefined"
proof -
  have "pmf (Pi_pmf {0..<m} undefined (\<lambda> _.D)) f > 0"  using pmf_pos  unfolding Samples_def by auto
  then show ?thesis using pmf_Pi_outside[of "{0..<m}" f undefined "(\<lambda> _. D)"] by auto
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

lemma truncated_S_in_Dn: "\<forall> S \<in> (Samples (m+1) D). truncated_S S m \<in> Samples m D"
proof  
  let ?M = "(Samples (m+1) D)"
  let ?I = "{0..<m}"
  fix S
  assume "S \<in> ?M" 
  have "finite {0..<m+1}" by auto 
  have "finite ?I" by auto
  then have 1: " pmf ?M S > 0" using pmf_positive_iff `S \<in> ?M` by fast 
  then have "\<forall> i. i \<notin> {0..<m+1} \<longrightarrow> S i = undefined" using pmf_pos[of "(m+1)" S] n_pos by auto
  then have "pmf ?M S = (\<Prod>x\<in>{0..<m+1}. pmf D (S x))"
    using pmf_Pi'[of "{0..<m+1}" S undefined "(\<lambda> _. D)"] `finite {0..<m+1}`  
    by (metis Samples_def)
  then have "\<forall>x \<in> {0..<m+1}.  pmf D (S x) > 0 " 
    by (meson \<open>S \<in> ?M\<close> pmf_positive sample_in_D)
  then have 2: "(\<Prod>x\<in>?I. pmf D (S x)) > 0" 
    by (simp add: prod_pos)
  have "\<And>x. x \<notin> ?I \<Longrightarrow> (truncated_S S m) x = undefined" 
    by (simp add: \<open>\<forall>i. i \<notin> {0..<m + 1} \<longrightarrow> S i = undefined\<close> truncated_S_def)
  then have "pmf (Samples m D) (truncated_S S m) = (\<Prod>x\<in>?I. pmf D (S x))" unfolding Samples_def
    using pmf_Pi'[of ?I "truncated_S S m" undefined "(\<lambda> _. D)"]  `finite ?I` 
    using truncated_S_def by auto
  then have "pmf (Samples m D) (truncated_S S m) > 0" using 2 by auto

  then show "truncated_S S m \<in> Samples m D"
    by (simp add: set_pmf_iff)
qed

lemma min_of_Dn1_in_H: "\<forall> S \<in> (Samples (n+1) D). (ridge_mine S k) \<in> H" 
proof 
  let ?M = "(Samples (n+1) D)"
  fix S
  assume "S \<in> ?M" 
  then have "truncated_S S n \<in> Samples n D" using truncated_S_in_Dn `S \<in> ?M`  by auto
  then have "(ridge_mine (truncated_S S n) k) \<in> H" using min_in_H by auto
  then show "(ridge_mine S k) \<in> H" 
    using truncated_same_min by auto
qed

lemma train_val_diff :
  assumes integrable_D:"\<forall> S \<in> (Samples n D). integrable D (\<lambda> z. l (ridge_mine S k) z)"
  assumes  pred_err_integrable: "integrable (Samples n D)  (\<lambda> S. pred_err_loss D l (ridge_mine S k))"
  assumes  train_err_integrable: " integrable (Samples n D)  (\<lambda> S. train_err_loss S n l (ridge_mine S k)) "
  assumes integrable_swapped_Si: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l (ridge_mine (swapped_S S i n) k) (S i))))"
  assumes integrable_Si: " integrable (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i.  (l  (ridge_mine S k) (S i))))"
  shows"  measure_pmf.expectation (Samples n D) 
          (\<lambda> S. pred_err_loss D l (ridge_mine S k) - train_err_loss S n l (ridge_mine S k)) 
            =  measure_pmf.expectation (Samples (n+1) D)
                        (\<lambda> S.  measure_pmf.expectation (pmf_of_set {0..<n})
                     (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) -  (l  (ridge_mine S k) (S i))))" 
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

  have pred_err_Dn1: "\<forall> i  \<in> ?I. integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) =
        integral\<^sup>L ?Dn1 (\<lambda> Sz. ?l_swapped i Sz)"
  proof 
    fix i
    assume "i\<in> ?I"
    have " integral\<^sup>L ?Dn (\<lambda> S. ?pred_err S) = 
        integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> z. (l (ridge_mine S k) z)))"
      unfolding pred_err_loss_def by auto
    also have " \<dots> = integral\<^sup>L ?Dn1 (\<lambda> S. ?l_trunc S (S n))"
      using l_pos min_in_H  integrable_D add_sample_expectation n_pos by auto
    also  have " \<dots> =  integral\<^sup>L ?Dn1 (\<lambda> S. ?l_Si S n)" 
      using truncated_same_min by auto
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
    have "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I.(ridge_mine (swapped_S S i n) k) \<in> H" 
      using min_of_Dn1_in_H pmf_swapped_same n_pos 
      by (smt add_diff_cancel_right' add_gr_0 atLeastLessThan_iff less_add_same_cancel1 less_trans set_pmf_iff swapped_S_def zero_less_one) 
    then have l_swapped_nn: "\<forall> S \<in> (set_pmf ?Dn1). \<forall> i \<in> ?I. ?l_swapped i S \<ge> 0"
      using l_pos  sample_in_D by auto

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

  have "\<forall>S. \<forall>i\<in>?I. (truncated_S S n) i = S i"  using  truncated_S_def by auto 

  then  have 4: "\<forall>S. integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)) =
               integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (S i))" 
    by (metis (no_types, lifting) fin_I non_empty_I same_integral_restricted set_pmf_of_set)

  have "n>0" using n_pos by auto
  then have 5: "integral\<^sup>L ?Dn (\<lambda> S. integral\<^sup>L D (\<lambda> _.  
       integral\<^sup>L ?pmfI (?l_Si S))) =
      integral\<^sup>L ?Dn1  (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda>i. ?l_trunc S (truncated_S S n i)))"
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
    using 4 5 truncated_same_min  by auto 

  have "integral\<^sup>L ?Dn 
          (\<lambda> S.   ?pred_err S - train_err_loss S n l (ridge_mine S k)) = 
       integral\<^sup>L ?Dn  (\<lambda> S. ?pred_err S) -
       integral\<^sup>L ?Dn  (\<lambda> S. train_err_loss S n l (ridge_mine S k))   "  
    using train_err_integrable  pred_err_integrable by simp

  also have " \<dots>  =
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI 
   (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)))) - 
   integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (?l_Si S))" using 2 6 by auto
  also have " \<dots> =   integral\<^sup>L ?Dn1 (\<lambda> S.  
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) ) -
  integral\<^sup>L ?pmfI (?l_Si S)  )" 
    using integrable_Si integrable_swapped_Si  by simp
  also have " \<dots> = 
     integral\<^sup>L ?Dn1 (\<lambda> S.  integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_S S i n) k) (S i)) - (?l_Si S i) ) )"
  proof -
    have "\<forall> S. sum (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) ) ?I -  sum (?l_Si S) ?I  =
    sum (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) - (?l_Si S i) ) ?I"
      by (simp add: sum_subtractf)
    then  have "\<forall> S.
   integral\<^sup>L ?pmfI (\<lambda> i. (l (ridge_mine (swapped_S S i n) k) (S i)) )  -
 integral\<^sup>L ?pmfI (?l_Si S) =
    integral\<^sup>L ?pmfI (\<lambda> i. 
   (l (ridge_mine (swapped_S S i n) k) (S i)) -  (?l_Si S i) )" using non_empty_I
      by (metis (no_types, lifting) diff_divide_distrib fin_I integral_pmf_of_set)
    then show ?thesis by auto
  qed
  finally show ?thesis by blast
qed

lemma ridge_index_swap_same: "\<forall> S. ridge_mine (S_index S i (S n)) k =
                    ridge_mine (swapped_S S i n) k"
  using truncated_same_min using S_index_swap_same 
  by metis


lemma add_sample_integrable:
  fixes f ::"( _  \<Rightarrow> _ \<Rightarrow> real)"
  fixes m :: "nat"
  assumes f_nn: "\<forall>S\<in> (Samples m D). \<forall>z\<in>D. f S z \<ge> 0"
  assumes integrable_D: "\<forall> S \<in> (Samples m D). integrable D (f S)"
  shows    "integrable (Samples m D) (\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) =
      integrable (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m))" 
proof -
  let ?pair = "(pair_pmf (Samples m D) D)"
  let ?Dm = "Samples m D"
  have "finite {0..<m}" by auto
  have " m \<notin> {0..<m}" by auto
  have insert_m:"(insert m {0..<m}) = {0..<m+1}" 
    using atLeast0LessThan by auto
  have 01:"\<forall> S \<in> ?Dm. integral\<^sup>L D (\<lambda> z. f S z) =  enn2real (integral\<^sup>N D (\<lambda> z. f S z))"
    using integrable_D f_nn 
    by (metis (mono_tags, lifting) AE_measure_pmf_iff enn2real_ennreal integral_nonneg_AE nn_integral_cong nn_integral_eq_integral)
  
 have 02: "\<forall> S \<in> ?Dm. ennreal (integral\<^sup>L D (\<lambda> z. f S z)) =  (integral\<^sup>N D (\<lambda> z. f S z))"
    using integrable_D f_nn 
    by (metis (mono_tags, lifting) AE_measure_pmf_iff  nn_integral_cong nn_integral_eq_integral)
  then have 03:"integral\<^sup>N (Samples m D) (\<lambda> S. integral\<^sup>N D (\<lambda> z. f S z)) =
      integral\<^sup>N (Samples m D) (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z))"
   using same_nn_integral_restricted1[of ?Dm "(\<lambda> S. ( integral\<^sup>N D (\<lambda> z. f S z)))" 
                    "(\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z))"]
   using "02" by auto
  
  have 1:" integral\<^sup>L ?Dm (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
  integral\<^sup>L ?pair  (\<lambda> (S,z). f S z)" 
    using expectation_pair_pmf'[of ?Dm D f]  f_nn integrable_D by linarith

   have 11:" integral\<^sup>N ?Dm (\<lambda> S. integral\<^sup>N D (\<lambda> z. f S z)) =
  integral\<^sup>N ?pair  (\<lambda> (S,z). f S z)"
     using nn_integral_pair_pmf'[of ?Dm D "(\<lambda> (S,z). f S z)"]
     by auto


have "integral\<^sup>N (map_pmf (\<lambda>(f,y). f(m:=y)) (pair_pmf (Samples m D) D))
       (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m)) =
     integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m))
         ( (\<lambda>(f,y). f(m:=y)) x))"
    using integral_map_pmf by simp

  have "integral\<^sup>N (pair_pmf (Samples m D) D)
         (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined)) (Sz m)) ( (\<lambda>(f,y). f(m:=y)) x)) = 
      integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m)) ( (\<lambda> f. (fst f)(m:=(snd f))) x))" 
    by (simp add: case_prod_beta)

  have " integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m)) ( (\<lambda> f. (fst f)(m:=(snd f))) x)) =
     integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m)) ((fst x)(m:=(snd x))))" by auto

  have " integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. (\<lambda> Sz. f (Sz(m:=undefined)) (Sz m)) ((fst x)(m:=(snd x)))) =
     integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x.  f (((fst x)(m:=(snd x)))(m:=undefined))  (((fst x)(m:=(snd x))) m))"
    by auto

  have " integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. f (((fst x)(m:=(snd x)))(m:=undefined))  (((fst x)(m:=(snd x))) m)) = 
     integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x. f ((fst x)(m:=undefined)) (((fst x)(m:=(snd x))) m))" by auto

  have " integral\<^sup>N (pair_pmf (Samples m D) D) 
    (\<lambda>x.  f ((fst x)(m:=undefined))  (((fst x)(m:=(snd x))) m)) =
      integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x.  f ((fst x)(m:=undefined)) (snd x))" by auto

  then have "integral\<^sup>L (map_pmf (\<lambda>(f,y). f(m:=y)) (pair_pmf (Samples m D) D))
       (\<lambda> Sz. f (Sz(m:=undefined)) (Sz m)) = 
   integral\<^sup>L (pair_pmf (Samples m D) D) (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x))"
    by simp



  have 2: "\<forall>x\<in> ?pair. ((fst x)(m:=undefined)) = (fst x)"
  proof 
    fix x
    assume "x\<in>?pair"
    have "pmf (Samples m D) (fst x) > 0" using \<open>x \<in> ?pair\<close>
      using pmf_positive by fastforce
    then have "\<forall>y. y \<notin> {0..<m} \<longrightarrow> (fst x) y = undefined"
      unfolding Samples_def using pmf_Pi_outside
      by (metis finite_atLeastLessThan less_numeral_extra(3))
    then show "((fst x)(m:=undefined)) = (fst x)" by auto
  qed

   then have "(\<lambda>x \<in> (pair_pmf (Samples m D) D).  f ((fst x)(m:=undefined))  (snd x)) =
    (\<lambda>x \<in> (pair_pmf (Samples m D) D).  f (fst x) (snd x))" by auto

  have " integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x)) =
     integral\<^sup>N (pair_pmf (Samples m D) D)
     (\<lambda>x \<in>(pair_pmf (Samples m D) D).  f ((fst x)(m:=undefined))  (snd x))"

    by (metis nn_integral_restrict_space_eq_restrict_fun) 

  have "integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x \<in> (pair_pmf (Samples m D) D).  f (fst x) (snd x)) =
      integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x.  f (fst x) (snd x))"  
  using nn_integral_restrict_space_eq_restrict_fun by metis
  then have " integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x.  f ((fst x)(m:=undefined))  (snd x)) =
     integral\<^sup>N (pair_pmf (Samples m D) D) (\<lambda>x.  f (fst x) (snd x))" 
    using \<open>(\<lambda>x\<in>set_pmf (pair_pmf (Samples m D) D). f ((fst x)(m := undefined)) (snd x)) = (\<lambda>x\<in>set_pmf (pair_pmf (Samples m D) D). f (fst x) (snd x))\<close> \<open>\<integral>\<^sup>+ x. ennreal (f ((fst x)(m := undefined)) (snd x)) \<partial>measure_pmf (pair_pmf (Samples m D) D) = \<integral>\<^sup>+ x. ennreal ((\<lambda>x\<in>set_pmf (pair_pmf (Samples m D) D). f ((fst x)(m := undefined)) (snd x)) x) \<partial>measure_pmf (pair_pmf (Samples m D) D)\<close> by auto
  
  have "   integral\<^sup>N ?pair  (\<lambda> (S,z). f S z) =
      integral\<^sup>N ( ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D (Samples m D))))
         (\<lambda> (S,z). f S z) " 
    by (metis pair_commute_pmf)


  have "(map_pmf (\<lambda>(f,y). f(m:=y)) ( map_pmf (\<lambda>(x, y). (y, x)) (pair_pmf D (Samples m D)))) =
    (map_pmf (\<lambda>(y,f). f(m:=y)) ((pair_pmf D (Samples m D))))" using map_pmf_comp
    by (smt Pair_inject map_pmf_cong prod.collapse split_beta)

  also have "\<dots> = Samples (m+1) D" unfolding Samples_def
    using  `finite {0..<m}` `m \<notin> {0..<m}`  Pi_pmf_insert[of "{0..<m}" m undefined "(\<lambda>_. D)"]
      insert_m by auto

   finally have " integral\<^sup>N ?pair  (\<lambda> (S,z). f S z) =
       integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. f (Sz(m:=undefined))  (Sz m))"
    using `finite {0..<m}` `m \<notin> {0..<m}` same_integral_restricted
     2 11 fun_upd_same fun_upd_upd nn_integral_map_pmf pair_commute_pmf prod.case_eq_if
    by (smt \<open>\<integral>\<^sup>+ x. ennreal (f ((fst x)(m := undefined)) (snd x)) \<partial>measure_pmf (pair_pmf (Samples m D) D) = \<integral>\<^sup>+ x. ennreal (f (fst x) (snd x)) \<partial>measure_pmf (pair_pmf (Samples m D) D)\<close> nn_integral_cong)

  then have "integral\<^sup>N (Samples m D) (\<lambda> S. integral\<^sup>N D (\<lambda> z. f S z)) =
      integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m))" unfolding truncated_S_def 
    using 11  by simp
  then have "integral\<^sup>N (Samples m D) (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
      integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m))" using 03
    by simp
  have "\<forall>S \<in> ?Dm. (integral\<^sup>N D (\<lambda> z. f S z)) = ennreal( norm ( integral\<^sup>L D (\<lambda> z. f S z)))"
    using "01" "02" by auto
  then have "integral\<^sup>N (Samples m D) (\<lambda> S. integral\<^sup>L D (\<lambda> z. f S z)) =
      integral\<^sup>N (Samples m D) (\<lambda> S. ennreal( norm ( integral\<^sup>L D (\<lambda> z. f S z))))"
    using "03" same_nn_integral_restricted1 by force

  have "\<forall>S \<in> (Samples (m+1) D). f (truncated_S S m) (S m) =
             (norm (f (truncated_S S m) (S m)))" using truncated_S_in_Dn[of m]
    by (simp add: f_nn sample_in_D)
  then have "integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. f (truncated_S Sz m) (Sz m)) =
      integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. (norm (f (truncated_S Sz m) (Sz m))))" 
using same_nn_integral_restricted1 
  by (metis (no_types, lifting))
  then have 10: " integral\<^sup>N (Samples m D) (\<lambda> S. ennreal( norm ( integral\<^sup>L D (\<lambda> z. f S z)))) =
       integral\<^sup>N (Samples (m+1) D) (\<lambda> Sz. (norm (f (truncated_S Sz m) (Sz m))))" 
    using \<open>\<integral>\<^sup>+ x. ennreal (measure_pmf.expectation D (f x)) \<partial>measure_pmf (Samples m D) = \<integral>\<^sup>+ S. ennreal (norm (measure_pmf.expectation D (f S))) \<partial>measure_pmf (Samples m D)\<close> \<open>\<integral>\<^sup>+ x. ennreal (measure_pmf.expectation D (f x)) \<partial>measure_pmf (Samples m D) = \<integral>\<^sup>+ x. ennreal (f (truncated_S x m) (x m)) \<partial>measure_pmf (Samples (m + 1) D)\<close> by auto

  have 11: "(\<lambda> S. measure_pmf.expectation D (\<lambda> z. f S z)) \<in> borel_measurable ?Dm" by auto
  have 12: "(\<lambda> Sz. f (truncated_S Sz m) (Sz m)) \<in> borel_measurable (Samples (m+1) D)" by auto









  then show ?thesis using truncated_S_def using 10 11 12
   integrable_iff_bounded
    by (metis (mono_tags, lifting) nn_integral_cong)
qed


end
end