\<^marker>\<open>creator Ralitsa Dardjonova\<close>

theory SVM
  imports "RLM_stable" "hinge_loss"
begin

paragraph \<open>Summary\<close>
text \<open>In this theory we define hinge loss and proove some lemmas 
that show it can be used as loss function for lipschitz convex learning\<close>

paragraph \<open>Main definitions\<close>
text \<open>
\<^item> \<open>soft_svm\<close> the function that is going to be optimized in the soft-SVM optimization problem
with respect to (w,\<xi>) - respectively the weights and the slack variables.
             k*|w|^2 + (1/n)\<Sum> \<xi>_i
\<^item> \<open>argmin_soft_svm\<close> definition of the soft-SVM opimization problem:
             min_(w,\<xi>) soft_svm, 
       s.t. \<forall>i. y_i * ( w \<bullet> x_i ) >= 1 - \<xi>_i 
       and      \<xi>_i >= 0
\<close>

paragraph \<open>Main Theorems\<close>
text \<open>
\<^item> \<open>ksi_are_margins\<close> We prove that the slack variables \<xi> correspond 
to the distance from a datapoint on the wrong side of the margin to the margin.
If a datapoint is on the correct side, we have \<xi>_i is 0.
\<^item> \<open>soft_svm_is_RLM\<close> We show that the soft-SVM optimization problem can be considered
as a regularized loss minimization problem, in this case ridge regression.
\<close>

text \<open>We define a locale for learning with hinge loss function.
It can be used to define soft-SVM optimization problem.\<close>
locale learning_with_hinge_loss =
  fixes H :: "'b::euclidean_space set"
    and D :: "('b \<times> real) pmf"
    and n :: "nat"
    and k :: "real"
  fixes \<rho> :: "real"
  assumes nnH: "H \<noteq> {}" 
    and  convH: "convex H"
    and n_pos: "n>0"
    and k_pos : "k>0"
    and rho_pos: "\<rho> > 0"
    and D_bounded : "\<forall>z \<in> D. norm (fst z) \<le> \<rho>"
    and y_abs : "\<forall>z\<in> D. abs (snd z) = 1"
begin
end

text \<open>We show that the locale \<open>learning_with_hinge_loss\<close> is a subset of \<open>lipschitz_ridge_and_convex_loss\<close>.
Thus we can use the theorems we have proved in this locale.\<close>
sublocale learning_with_hinge_loss \<subseteq> lipschitz_ridge_and_convex_loss H D n hinge_loss k \<rho>
proof unfold_locales 
  show "H \<noteq> {}" using nnH by auto
  show "convex H" using convH by auto
  show " \<forall>h\<in>H. \<forall>z\<in>set_pmf D. 0 \<le> hinge_loss h z" using hinge_loss_pos by auto
  show "\<forall>z\<in>set_pmf D. convex_on H (\<lambda>h. hinge_loss h z)" using hinge_loss_convex by auto
  show "0 < n" using n_pos by auto
  show "k>0" using k_pos by auto
  show " 0 < \<rho>" using rho_pos by auto
  show " \<forall>y\<in>set_pmf D. \<rho>-lipschitz_on H (\<lambda>h. hinge_loss h y)"
  proof
    fix y 
    assume " y\<in> D" 
    then have "abs (snd y) = 1" using y_abs by auto
    then have "(norm (fst y))-lipschitz_on H (\<lambda> z. hinge_loss z y)" 
      by (metis fst_conv hinge_loss.elims hinge_loss_is_lipschitz snd_conv)
    then show "\<rho>-lipschitz_on H (\<lambda> z. hinge_loss z y)" using D_bounded `y\<in>D`
      using lipschitz_on_le by blast
  qed

  show "\<forall> h \<in> H. integrable D (\<lambda> z. hinge_loss h z)"
  proof
    fix h
    assume "h\<in>H" 
    have "integrable D (\<lambda> z. 0)" by auto

    have "integrable D (\<lambda> z. (1 - (snd z) * inner h (fst z)))"
    proof 
      show "integrable D (\<lambda>x. 1)" by auto

      have  "integrable D (\<lambda> x. snd x *\<^sub>R fst x)"
      proof -
        have "AE x in D. norm (snd x *\<^sub>R fst x) \<le> \<rho> * ((\<lambda> x. 1) x)"
          using D_bounded y_abs
          by (simp add: AE_measure_pmf_iff)
        then have  "(\<integral>\<^sup>+x. norm (snd x *\<^sub>R fst x) \<partial>D) < \<infinity>"
          using  nn_integral_mult_bounded_inf[of "(\<lambda> x. 1)" D \<rho>] 
          using rho_pos by auto
        moreover have "(\<lambda> x. snd x *\<^sub>R fst x) \<in> borel_measurable D"
          by auto
        ultimately show "integrable D (\<lambda> x. snd x *\<^sub>R fst x)" 
          using integrableI_bounded by blast
      qed
      then  have "integrable D (\<lambda>x. (h \<bullet> snd x *\<^sub>R fst x))"
        using integrable_inner_right by blast
      then show "integrable D (\<lambda>x. snd x * (h \<bullet> fst x))"  by simp
    qed

    then have "integrable D (\<lambda> x. max 0 ( 1 - snd x * (h \<bullet> fst x)))" 
      using Bochner_Integration.integrable_max `integrable D (\<lambda> z. 0)` by blast

    then have "integrable D  (\<lambda> x. hinge_loss h (fst x, snd x))" 
      unfolding hinge_loss.simps  by auto
    then show "integrable D (hinge_loss h)" 
      by auto
  qed
qed

context learning_with_hinge_loss
begin

text \<open>
This is a definition of the soft-SVM function we want to minimize.
Here x is a tuple of the vector of weights w and the slack variables \<xi>\<close>
definition soft_svm :: " ('b \<times> (nat \<Rightarrow> real)  \<Rightarrow> real)" where
  "soft_svm = (\<lambda> x. k * norm (fst x)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. (snd x i)))"

text \<open>This is the definition of the soft-SVM optimization problem. 
We want to find a tuple (w,\<xi>), where w are the weights and \<xi> are the slack variables.\<close>
definition soft_svm_argmin :: "(nat \<Rightarrow> ('b \<times> real)) \<Rightarrow> ('b \<times> (nat \<Rightarrow> real) )set" where
  "soft_svm_argmin  S' = {h. is_arg_min (soft_svm)
   (\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. (snd (S' i)) * ((fst x) \<bullet> ((fst (S' i)))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) ) h}"

text \<open>A single argmin instance of the soft-SVM optimization problem.\<close>
definition soft_svm_mine :: "(nat \<Rightarrow> ('b \<times> real)) \<Rightarrow>'b \<times> (nat \<Rightarrow> real)" where
  "soft_svm_mine S' = (SOME h. h \<in> soft_svm_argmin S' )"

text \<open>The loss for a data point i is exactly (ksi i) --> the distance to 
the boundary. We follow the informal proof from @{cite UnderstandingML} in Section 15 Soft SVM.\<close>
lemma ksi_are_margins :
  assumes "s \<in> H"
  assumes "(s,ksi) \<in> soft_svm_argmin S"
  assumes "i \<in> {0..<n}"
  shows " ksi i = hinge_loss s (S i)"
proof -
  let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge>
 1 - (snd x i)) \<and> (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )"
  let ?hinge = "(\<lambda> i. hinge_loss s (S i))"
  let ?I = "{0..<n}"
  have pair_eq:"\<forall>x.  x = (fst x, snd x)" by auto

  moreover have "(\<forall>i\<in>?I. snd (S i) * (inner s (fst (S i))) \<ge> 1 - (ksi i))"
    using  assms unfolding soft_svm_argmin_def
    by (simp add: is_arg_min_linorder)
  moreover have " (\<forall> i\<in>?I. ksi i \<ge> 0)"
    using  assms unfolding soft_svm_argmin_def 
    by (simp add: is_arg_min_linorder)
  ultimately have ksi_ge_hinge:"\<forall> i \<in> ?I. ksi i \<ge> ?hinge i"
    by (smt  hinge_loss.simps)

  have "soft_svm (s,ksi) \<le> soft_svm (s, ?hinge)" 
  proof -
    have " ?P (s, ?hinge)"  
      using `s\<in>H` pair_eq by (smt hinge_loss.simps prod.sel(1) prod.sel(2))
    have  "(s,ksi) \<in> soft_svm_argmin S"
      using   assms unfolding soft_svm_argmin_def  by auto
    then show ?thesis using `?P (s, ?hinge)`
      by (simp add: is_arg_min_linorder soft_svm_argmin_def)
  qed
  then have "(1/n) * (\<Sum>i\<in>?I. (ksi i)) \<le> (1/n) * (\<Sum>i\<in>?I. (?hinge i))"
    by (simp add: local.soft_svm_def)
  then have "(\<Sum>i\<in>?I. (ksi i)) \<le> (\<Sum>i\<in>?I. (?hinge i))"
    using n_pos of_nat_0_less_iff real_mult_le_cancel_iff2 zero_less_divide_1_iff by blast
  then have sum_eq:"(\<Sum>i\<in>?I. (ksi i)) = (\<Sum>i\<in>?I. (?hinge i))"
    using sum_mono ksi_ge_hinge by smt 

  show " ksi i = hinge_loss s (S i)"
  proof (rule ccontr)
    assume "ksi i \<noteq> hinge_loss s (S i)" 
    then have "ksi i > ?hinge i" using ksi_ge_hinge `i\<in>?I`
      by fastforce
    then have "(\<Sum>i\<in>?I. (ksi i)) >  (\<Sum>i\<in>?I. (?hinge i))" 
      by (meson ksi_ge_hinge assms(3) finite_atLeastLessThan sum_strict_mono_ex1)
    then show False using sum_eq by auto
  qed
qed

lemma asas:
shows "\<forall> h. is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) h \<longleftrightarrow>
         is_arg_min (soft_svm) (\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge>
            1 - (snd x i)) \<and>  (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) ) (h, (\<lambda> x i. hinge_loss x (S i)) h)"
proof
 let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge>
            1 - (snd x i)) \<and>  (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )" 
  let ?hingei = "(\<lambda> x i. hinge_loss x (S i))" 

    fix h
    let ?ksi' = "(\<lambda> i. hinge_loss h (S i))"
    have 0: "\<forall>x. x = (fst x, snd x)" by auto
    show " is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) h \<longleftrightarrow> is_arg_min (soft_svm) ?P (h, ?ksi')"
    proof
      assume "is_arg_min (soft_svm) ?P (h, ?ksi')"
      then have "?P (h, ?ksi')"
        by (simp add: is_arg_min_linorder) 
      then have "h\<in>H" by auto
      have "\<forall> x. ?P x \<longrightarrow>  soft_svm x \<ge> soft_svm (h, ?ksi')"
        unfolding is_arg_min_def 
        using not_less `is_arg_min (soft_svm) ?P (h, ?ksi')` 
        by (simp add: is_arg_min_linorder)
      then have "\<forall>x. snd x = ?hingei (fst x) \<and> fst x \<in> H \<longrightarrow> soft_svm x \<ge> soft_svm (h, ?ksi')"
        using 0 by (smt hinge_loss.simps)
      then have "\<forall>x. x \<in> H \<longrightarrow>(\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n) x 
                   \<ge>  (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n ) h"
        using soft_svm_def  by auto
      then have " is_arg_min 
                (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n) (\<lambda> h. h \<in> H) h"
        by (metis (no_types, lifting) \<open>h \<in> H\<close> is_arg_min_linorder) 
      then have 8:" is_arg_min 
                  (\<lambda>h.  (\<Sum>i = 0..<n. (?hingei h i)) / n + k * (norm h)\<^sup>2) (\<lambda> h. h \<in> H) h"
        by (smt is_arg_min_linorder)
      have "ridge_fun S k = (\<lambda>h. (\<Sum>i = 0..<n. (?hingei h i)) / real n  + k * (norm h)\<^sup>2)" 
        unfolding ridge_fun.simps
        unfolding train_err_loss_def
        by auto
      then show " is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) ( h)" 
        using 8  by auto
    next
      assume "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h" 
      then have "h\<in>H" using  is_arg_min_def by fastforce
      have "?P (h, ?ksi')" 
        using `h\<in>H` 0  by (smt fst_conv hinge_loss.simps snd_conv)
      have 9:"\<forall> x. ?P x \<longrightarrow> soft_svm x \<ge> soft_svm (fst x, ?hingei (fst x))" 
      proof 
        fix x
        show "?P x \<longrightarrow> soft_svm x \<ge> soft_svm (fst x, ?hingei (fst x))"
        proof 
          assume "?P x" 
          have 2:"(\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - ((snd x) i))"
            using ` ?P x`  by simp
          have "fst x \<in>H" using `?P x` by auto
          have 3:" (\<forall> i\<in>{0..<n}. snd x i \<ge> 0)" using `?P x` by auto
          have 5:"\<forall> i \<in> {0..<n}. (snd x) i \<ge> ?hingei (fst x) i" 
            using 2 3 0  by (smt hinge_loss.simps)
          show "soft_svm x \<ge> soft_svm (fst x, ?hingei (fst x))"
            unfolding soft_svm_def 
            by (smt "5" divide_le_0_1_iff fst_conv of_nat_0_less_iff real_mult_le_cancel_iff2
                 snd_conv n_pos learning_with_hinge_loss_axioms sum_mono)
        qed
      qed
      have "(\<lambda>h. (\<Sum>i = 0..<n.  (?hingei h i)) / n) + (\<lambda>w. k * (norm w)\<^sup>2) = 
          (\<lambda>h. (\<Sum>i = 0..<n.  (?hingei h i)) / n  + k * (norm h)\<^sup>2)" by auto
      then have "ridge_fun S k = (\<lambda>h. (\<Sum>i = 0..<n. (?hingei h i)) / real n  + k * (norm h)\<^sup>2)" 
        unfolding ridge_fun.simps
        unfolding train_err_loss_def
        by simp
      then have " is_arg_min 
          (\<lambda>h.  (\<Sum>i = 0..<n. (?hingei h i)) / n + k * (norm h)\<^sup>2) (\<lambda> h. h \<in> H) h"
        using \<open>is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h\<close> by auto
      then have " is_arg_min 
          (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n)(\<lambda> h. h \<in> H) h" 
        by (smt is_arg_min_linorder)
      then have "\<forall>x. x \<in> H \<longrightarrow>
       (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n) x 
        \<ge>  (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / n) h" 
        by (metis (mono_tags, lifting) is_arg_min_linorder)
      then have "\<forall> x. fst x \<in> H \<longrightarrow>
       k * norm (fst x)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. (?hingei (fst x) i)) \<ge> soft_svm ( h, ?ksi')" 
        by (simp add: local.soft_svm_def)
      then have  "\<forall> x. ?P x \<longrightarrow> soft_svm x \<ge> soft_svm (h, ?ksi')" using 9 
        by (smt  fst_conv local.soft_svm_def snd_conv)
      then show "is_arg_min (soft_svm) ?P (h, ?ksi')"
        using `?P (h, ?ksi')` by (simp add: is_arg_min_linorder)
    qed
  qed

lemma argmin_svm_is_argmin_ridge:
  shows "(h, (\<lambda> i. hinge_loss h (S i))) \<in> soft_svm_argmin S  \<longleftrightarrow> h \<in> ridge_argmin S k"
proof -

  show ?thesis unfolding soft_svm_argmin_def unfolding ridge_argmin_def 
    using asas
    by auto
qed

text \<open>
Claim 15.5
Here we prove that the Support vector machine minimization problem
can be expressed as Ridge regression, i.e. it is a reguralized loss minimization
problem. We follow the informal proof from @{cite UnderstandingML}.
We show that a hypothesis h is an argmin of the ridge function iff 
h is argmin to the svm subject to the constraints. 
After that the proof is trivial.\<close>
lemma soft_svm_is_RLM:
assumes S_in_D: "S \<in> Samples n D"
  shows "ridge_fun S k (ridge_mine S k) =  soft_svm (soft_svm_mine S)"
proof -
  let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge>
            1 - (snd x i)) \<and>  (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )" 
  let ?hingei = "(\<lambda> x i. hinge_loss x (S i))" 

  have "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) (ridge_mine S k)" 
    using S_in_D k_pos learning_basics_loss_axioms ridge_argmin_def
    using ridge_min_el_is_argmin by auto
  then have 12: "is_arg_min soft_svm ?P ((ridge_mine S k), ?hingei (ridge_mine S k))"
    using asas by auto
  then have "ridge_fun S k (ridge_mine S k) = 
      (\<Sum>i = 0..<n. (?hingei (ridge_mine S k) i)) / real n  + k * (norm (ridge_mine S k))\<^sup>2"
    unfolding ridge_fun.simps 
    unfolding train_err_loss_def by auto
  also have " \<dots> =  soft_svm ((ridge_mine S k), ?hingei (ridge_mine S k))" 
    by (simp add: local.soft_svm_def)
  finally have "ridge_fun S k (ridge_mine S k) =
              soft_svm ((ridge_mine S k), ?hingei (ridge_mine S k))" by auto
  then have 13: "ridge_fun S k (ridge_mine S k) = soft_svm (SOME h. is_arg_min (soft_svm) ?P h)" 
    using  12   by (smt is_arg_min_linorder someI_ex)
  have "(SOME h. is_arg_min (soft_svm) ?P h) = soft_svm_mine S" 
    unfolding soft_svm_mine_def
    unfolding soft_svm_argmin_def
    by simp
  then show ?thesis using 13 by auto
qed

lemma soft_svm_is_RLM1:
assumes S_in_D: "S \<in> Samples n D"
  assumes "v \<in> soft_svm_argmin S"
  assumes "u \<in> ridge_argmin S k"
  shows "ridge_fun S k u =  soft_svm v"
proof -
  let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge>
            1 - (snd x i)) \<and>  (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )" 
  let ?hingei = "(\<lambda> x i. hinge_loss x (S i))" 

  have "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) u" 
    using S_in_D k_pos learning_basics_loss_axioms ridge_argmin_def
    using ridge_min_el_is_argmin assms by auto
  then have 12: "is_arg_min soft_svm ?P (u, ?hingei u)"
    using asas by auto
  then have "ridge_fun S k u = 
      (\<Sum>i = 0..<n. (?hingei u i)) / real n  + k * (norm u)\<^sup>2"
    unfolding ridge_fun.simps 
    unfolding train_err_loss_def by auto
  also have " \<dots> =  soft_svm (u, ?hingei u)" 
    by (simp add: local.soft_svm_def)
  finally have "ridge_fun S k u =
              soft_svm (u, ?hingei u)" by auto
  then have 13: "ridge_fun S k u = soft_svm (SOME h. is_arg_min (soft_svm) ?P h)" 
    using  12   by (smt is_arg_min_linorder someI_ex)
  have 14:" (SOME h. is_arg_min (soft_svm) ?P h) = soft_svm_mine S" 
    unfolding soft_svm_mine_def
    unfolding soft_svm_argmin_def by simp
  have "(soft_svm_mine S) \<in> soft_svm_argmin S" unfolding soft_svm_mine_def
    by (metis assms(2) verit_sko_ex')
  then have 21: "soft_svm (soft_svm_mine S) \<le> soft_svm v" unfolding soft_svm_argmin_def using assms
    by (metis (mono_tags, lifting) is_arg_min_linorder mem_Collect_eq soft_svm_argmin_def)
  have "soft_svm (soft_svm_mine S) \<ge> soft_svm v" unfolding soft_svm_argmin_def using assms
   
    by (metis (mono_tags, lifting) \<open>soft_svm_mine S \<in> soft_svm_argmin S\<close> is_arg_min_linorder mem_Collect_eq soft_svm_argmin_def)
  then have "soft_svm (soft_svm_mine S) = soft_svm v" using 21 by auto
  then show ?thesis using 13 14 by auto
qed

lemma ridge_fun_with_svm_min:
  assumes S_in_D: "S \<in> Samples n D"
  assumes "v \<in> soft_svm_argmin S"
  assumes "u \<in> ridge_argmin S k"
  shows "ridge_fun S k u = ridge_fun S k (fst v)"
proof -
  let ?P = " (\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. (snd (S i)) * ((fst x) \<bullet> ((fst (S i)))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )"
  have 1: "(fst v, snd v) \<in> soft_svm_argmin S" using assms by auto
  then have 2:"?P v" using assms unfolding soft_svm_argmin_def
    by (simp add: is_arg_min_linorder)
  have "(u, (\<lambda> i. hinge_loss u (S i))) \<in> soft_svm_argmin S  \<longleftrightarrow> u \<in> ridge_argmin S k"
    using argmin_svm_is_argmin_ridge by auto
  have "fst v \<in> H" using assms unfolding soft_svm_argmin_def 
    by (simp add: is_arg_min_linorder)
  then have "\<forall>i \<in> {0..<n}.  snd v i = hinge_loss (fst v) (S i)"
    using "1" ksi_are_margins by blast
  then have 4: "soft_svm (fst v, (\<lambda> i. hinge_loss (fst v) (S i))) = soft_svm v"
    unfolding soft_svm_def 
    by simp
  let ?t = "(fst v, (\<lambda> i. hinge_loss (fst v) (S i)))"
  have 3:"?P ?t" using 2 
    by (metis "1" fst_conv learning_with_hinge_loss.ksi_are_margins learning_with_hinge_loss_axioms snd_conv)
  have "(is_arg_min soft_svm ?P v)" using assms unfolding soft_svm_argmin_def  by auto
  then have "(is_arg_min soft_svm ?P ?t)" 
    unfolding soft_svm_argmin_def assms
    using 4 assms  3
    by (simp add: is_arg_min_def)
  then have "?t \<in> soft_svm_argmin S" unfolding soft_svm_argmin_def by auto
  then have "fst ?t \<in> ridge_argmin S k"  using argmin_svm_is_argmin_ridge by auto
  then have "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) (fst v)" unfolding soft_svm_argmin_def 
    by (simp add: ridge_argmin_def)
  then show ?thesis using assms 
  using \<open>fst (fst v, \<lambda>i. hinge_loss (fst v) (S i)) \<in> ridge_argmin S k\<close> 
      soft_svm_is_RLM1 assms by auto
qed
  

text \<open>The training error is integrable.\<close>
lemma train_err_svm_integrable:
  shows " integrable (Samples n D) (\<lambda> S. train_err_loss S n hinge_loss (fst (soft_svm_mine S)))"
proof -
  from nnH obtain h where "h\<in>H" by blast 
  let ?f = " (\<lambda> i S. hinge_loss (fst (soft_svm_mine S)) (S i))"
  let ?g = "(\<lambda> S  z. hinge_loss (fst (soft_svm_mine S)) z)"
  let ?M = "(Samples n D)"
  have nn: "\<And>S. S\<in>set_pmf ?M \<Longrightarrow> \<forall>i\<in>{0..<n}. 0 \<le> ?f i S "
    using l_nn element_of_sample_in_dataset argmin_in_hypotheis_set 
    using hinge_loss_pos by blast

  {
    fix S
    assume S: "S\<in>Samples n D"
    let ?w = "(fst (soft_svm_mine S))"
    have *: "train_err_loss S n hinge_loss (fst (soft_svm_mine S))
                 \<le> train_err_loss S n hinge_loss h +  k * norm ( h )^2" 
    proof -
      have " train_err_loss S n hinge_loss ?w \<le> train_err_loss S n hinge_loss h + k * norm ( h )^2"
      proof -
        have "is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) (ridge_mine S k)"
          unfolding ridge_mine_def unfolding ridge_argmin_def 
          by (metis S mem_Collect_eq ridge_argmin_def ridge_min_el_is_argmin verit_sko_ex_indirect)
        then have "(ridge_mine S k) \<in> ridge_argmin S k" unfolding ridge_argmin_def by auto
        have "ridge_fun S k ?w = ridge_fun S k (ridge_mine S k)" using ridge_fun_with_svm_min
        using \<open>ridge_mine S k \<in> ridge_argmin S k\<close> learning_with_hinge_loss.argmin_svm_is_argmin_ridge
            learning_with_hinge_loss_axioms soft_svm_mine_def 
            by (metis S someI_ex)
 
        then have "(ridge_fun S k)  ((fst (soft_svm_mine S))) \<le> (ridge_fun S k) h" 
          using `h\<in>H` 
          by (metis \<open>is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) (ridge_mine S k)\<close> is_arg_min_linorder)

        then have "train_err_loss S n hinge_loss ?w  + k* norm(?w)^2
                   \<le> train_err_loss S n hinge_loss h + k * norm ( h )^2"
          unfolding ridge_fun.simps by auto
        then show "train_err_loss S n hinge_loss ?w 
                  \<le> train_err_loss S n hinge_loss h + k * norm ( h )^2" using k_pos
          by (smt mult_nonneg_nonneg zero_le_power2)
      qed
      then show "train_err_loss S n hinge_loss ?w \<le>
                                train_err_loss S n hinge_loss h +  k * norm ( h )^2"
        by blast
    qed
    have " train_err_loss S n hinge_loss ?w \<ge> 0" 
      by (simp add: train_err_loss_nn nn S)
    then have  "(train_err_loss S n hinge_loss ?w) =
          (norm (train_err_loss S n hinge_loss ?w))" 
      by simp
    then have 12:" (norm (train_err_loss S n hinge_loss ?w))
      \<le> norm (train_err_loss S n hinge_loss h + k * (norm h)\<^sup>2)" 
      using * by auto
  } note bounded = this
  then have integrable_ridge_fun:"integrable ?M (\<lambda> S.  train_err_loss S n hinge_loss h + k * norm ( h )^2)" 
    apply(intro Bochner_Integration.integrable_add) 
    subgoal by(rule train_err_integrable_fixed_hypotheis[OF `h\<in>H`])
    subgoal by auto
    done
  show "integrable (Samples n D) (\<lambda> S. train_err_loss S n hinge_loss (fst (soft_svm_mine S)))" 
    apply(rule Bochner_Integration.integrable_bound)
      apply(rule integrable_ridge_fun)
    using bounded
    by (auto intro: AE_pmfI )   
qed


text \<open>Claim 15.7\<close>
lemma 
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D) (\<lambda> S.  pred_err_loss D hinge_loss (fst (soft_svm_mine S))) \<le>
    pred_err_loss D hinge_loss h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)" 
    oops

end