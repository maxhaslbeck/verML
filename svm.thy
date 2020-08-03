theory svm
  imports "RLM_stable" "Subgradients"
begin


locale soft_svm =
  fixes H :: "'b::euclidean_space set"
    and D :: "('b \<times> real) pmf"
    and n :: "nat"
    and k :: "real"
  fixes S :: "(nat \<Rightarrow> ('b \<times> real))"
    and \<rho> :: "real"
  assumes nnH: "H \<noteq> {}" 
    and  convH: "convex H"
    and n_pos: "n\<ge>1"
    and k_pos : "k>0"
    and rho_pos: "\<rho> > 0"
    and S_in_D: "S \<in> Samples n D" 
    and D_bounded : "\<forall>z \<in> D. norm (fst z) \<le> \<rho>"
    and y_abs : "\<forall>z\<in> D. abs (snd z) = 1"
begin
end


sublocale soft_svm \<subseteq> lipschitz_ridge_and_convex_loss H D n hinge_loss k \<rho>
proof unfold_locales 
  show "H \<noteq> {}" using nnH by auto
  show "convex H" using convH by auto
  show " \<forall>h\<in>H. \<forall>z\<in>set_pmf D. 0 \<le> hinge_loss h z" using hinge_loss_pos by auto
  show "\<forall>z\<in>set_pmf D. convex_on H (\<lambda>h. hinge_loss h z)" using hinge_loss_convex by auto
  show "1 \<le> n" using n_pos by auto
  show "k>0" using k_pos by auto
  show " 0 < \<rho>" using rho_pos by auto
  show " \<forall>y\<in>set_pmf D. \<rho>-lipschitz_on H (\<lambda>h. hinge_loss h y)"
  proof
    fix y 
    assume " y\<in> D" 
    then have "abs (snd y) = 1" using y_abs by auto
    then have "(norm (fst y))-lipschitz_on H (\<lambda> z. hinge_loss z y)" 
      using abv by auto
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

      have 6: "integrable D (\<lambda> x. snd x *\<^sub>R fst x)"
      proof -
        have 1:"(\<lambda> x. 1) \<in> borel_measurable D" by auto
        have 2:"\<rho> \<noteq> \<infinity>" by auto
        have "integrable D (\<lambda>x. 1)" by auto
        then have "integral\<^sup>N D (\<lambda> x. 1) < \<infinity>" by simp
        have "AE x in D. norm (snd x *\<^sub>R fst x) \<le> \<rho> * ((\<lambda> x. 1) x)"
          using D_bounded y_abs
          by (simp add: AE_measure_pmf_iff)
        then have 3: "(\<integral>\<^sup>+x. norm (snd x *\<^sub>R fst x) \<partial>D) < \<infinity>" using D_bounded 
            nn_integral_mult_bounded_inf[of "(\<lambda> x. 1)" D \<rho> "(\<lambda> x. norm (snd x *\<^sub>R fst x))"] 1 2
          using rho_pos by auto
        have 4:"(\<lambda> x. snd x *\<^sub>R fst x) \<in> borel_measurable D" by auto
        show "integrable D (\<lambda> x. snd x *\<^sub>R fst x)" using 3 4
          using integrableI_bounded by blast
      qed


      have 5: "integrable D (\<lambda>x. (h \<bullet> snd x *\<^sub>R fst x))"
      proof(cases "h=0")
        case True
        then show ?thesis
          by simp
      next
        case False

        then show "integrable D (\<lambda>x. h \<bullet> snd x *\<^sub>R fst x)" 
          using integrable_inner_right[of h D "(\<lambda> x. snd x *\<^sub>R fst x)"] 6 
            `h \<noteq> 0` by auto
      qed
      have "(\<lambda> x. h \<bullet> snd x *\<^sub>R fst x) = (\<lambda> x.  snd x * (h \<bullet> fst x))" 
        by simp
      then show "integrable D (\<lambda>x. snd x * (h \<bullet> fst x))" using 5 by simp
    qed
    then show "integrable D (hinge_loss h)" unfolding hinge_loss.simps
      by auto
  qed
qed

context soft_svm
begin

definition soft_svm :: "('b \<times> (nat \<Rightarrow> real)  \<Rightarrow> real)" where
  "soft_svm  = (\<lambda> x. k * norm (fst x)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. (snd x i)))"

definition soft_svm_argmin :: " ('b \<times> (nat \<Rightarrow> real) )set" where
  "soft_svm_argmin  = {h. is_arg_min (soft_svm) (\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) ) h}"

definition soft_svm_mine :: "'b \<times> (nat \<Rightarrow> real)" where
  "soft_svm_mine  = (SOME h. h \<in> soft_svm_argmin)"


lemma asd :
  assumes "fst h \<in> H"
  assumes "is_arg_min (soft_svm) (\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) ) h"
  shows "case h of (s,ksi) \<Rightarrow> \<forall>i\<in>{0..<n}. ksi i = hinge_loss s (S i)"
proof 

  fix s ksi
  assume "h = (s,ksi)"
  let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )"
  have "s\<in>H" using `fst h \<in> H` `h = (s,ksi)` by auto  
  have 2:"(\<forall>i\<in>{0..<n}. snd (S i) * (inner s (fst (S i))) \<ge> 1 - (ksi i))"
    using  `h = (s,ksi)` `is_arg_min (soft_svm) ?P h` 
    by (simp add: is_arg_min_linorder)
  have 3:" (\<forall> i\<in>{0..<n}. ksi i \<ge> 0)"
    using  `h = (s,ksi)` `is_arg_min (soft_svm) ?P h` 
    by (simp add: is_arg_min_linorder)


  let ?hinge = "(\<lambda> i. hinge_loss s (S i))"
  have "soft_svm (s,ksi) \<le> soft_svm (s, ?hinge)" 
  proof -
    have 1: "is_arg_min (soft_svm) ?P (s,ksi)"
      using `h = (s,ksi)`  `is_arg_min (soft_svm) ?P h`  by auto
    have " ?P (s, ?hinge)" unfolding hinge_loss.simps   using `s\<in>H`  by auto
    then show ?thesis using 1 
      by (simp add: is_arg_min_linorder)
  qed
  then have "(1/n)* (\<Sum>i\<in>{0..<n}. (ksi i)) \<le> 
            (1/n)* (\<Sum>i\<in>{0..<n}. (?hinge i))"  by (simp add: local.soft_svm_def)
  then have 4:"(\<Sum>i\<in>{0..<n}. (ksi i)) \<le>  (\<Sum>i\<in>{0..<n}. (?hinge i))" 
    by (smt divide_le_0_1_iff n_pos not_one_le_zero of_nat_le_0_iff real_mult_le_cancel_iff2)
  have 5:"\<forall> i \<in> {0..<n}. ksi i \<ge> ?hinge i" unfolding hinge_loss.simps using 2 3 by auto
  then have "(\<Sum>i\<in>{0..<n}. (ksi i)) \<ge>  (\<Sum>i\<in>{0..<n}. (?hinge i))"
    by (meson sum_mono)
  then have 6:"(\<Sum>i\<in>{0..<n}. (ksi i)) =  (\<Sum>i\<in>{0..<n}. (?hinge i))" using 4 by auto


  show "\<forall>i\<in>{0..<n}.  ksi i = hinge_loss s (S i)"
  proof 
    fix i
    assume "i\<in>{0..<n}" 
    show " ksi i = hinge_loss s (S i)" 
    proof (rule ccontr)
      assume "ksi i \<noteq> hinge_loss s (S i)" 
      then have "ksi i > ?hinge i" using 5 `i\<in>{0..<n}`
        by fastforce
      then have "(\<Sum>i\<in>{0..<n}. (ksi i)) >  (\<Sum>i\<in>{0..<n}. (?hinge i))" 
        by (meson "5" \<open>i \<in> {0..<n}\<close> finite_atLeastLessThan sum_strict_mono_ex1)
      then show False using 6 by auto
    qed
  qed
qed

lemma asd1 :
  assumes " h \<in> H"
  assumes "is_arg_min (soft_svm) (\<lambda> x . fst x\<in>H \<and> 
  (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) ) (h, ksi)"
  shows "\<forall>i\<in>{0..<n}. ksi i = hinge_loss h (S i)" using asd 
  using assms(1) assms(2) by auto

lemma 
  shows "ridge_fun S k (ridge_mine S k) =  soft_svm (soft_svm_mine)"
proof -
  let ?P = "(\<lambda> x . fst x\<in>H \<and> (\<forall>i\<in>{0..<n}. snd (S i) * (inner (fst x) (fst (S i))) \<ge> 1 - (snd x i)) \<and> 
    (\<forall> i\<in>{0..<n}. snd x i \<ge> 0) )" 
  let ?hingei = "(\<lambda> x i. hinge_loss x (S i))" 


  have 11: "\<forall> h. is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) h \<longleftrightarrow>
         is_arg_min (soft_svm) ?P (h, ?hingei h)"
  proof
    fix h
    let ?ksi' = "(\<lambda> i. hinge_loss h (S i))"
    show " is_arg_min (ridge_fun S k) (\<lambda>s. s\<in>H) h \<longleftrightarrow>
         is_arg_min (soft_svm) ?P (h, ?hingei h)"
    proof
      assume "is_arg_min (soft_svm) ?P (h, ?hingei h)"
      then have "?P (h, ?hingei h)"
        by (simp add: is_arg_min_linorder) 
      then have "h\<in>H" by auto
      have "\<forall> x. ?P x \<longrightarrow>
        soft_svm x \<ge> soft_svm (h, ?ksi')" unfolding is_arg_min_def 
        using not_less `is_arg_min (soft_svm) ?P (h, ?hingei h)` 
        by (simp add: is_arg_min_linorder)

      then have "\<forall>x. snd x = ?hingei (fst x) \<and>
             ?P x \<longrightarrow>  soft_svm x \<ge> soft_svm (h, ?ksi')" 
        by auto


      then have "\<forall>x. snd x = ?hingei (fst x) \<and> fst x \<in> H \<longrightarrow> 
     soft_svm x \<ge> soft_svm (h, ?ksi')"
        by auto
      then have "\<forall> x. fst x \<in> H \<longrightarrow>
  k * norm (fst x)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. ((?hingei (fst x)) i)) 
    \<ge> soft_svm (h, ?ksi')" 
        by (simp add: local.soft_svm_def)
      then have "\<forall> x.  x \<in> H \<longrightarrow>
  k * norm x^2 + (1/n)* (\<Sum>i\<in>{0..<n}. ((?hingei x) i)) 
    \<ge> soft_svm (h, ?ksi')" by auto
      then have  "\<forall> x.  x \<in> H \<longrightarrow>
  k * norm x^2 + (1/n)* (\<Sum>i\<in>{0..<n}. ((?hingei x) i)) 
    \<ge> k * norm (h)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. ((?hingei (h)) i))"
        by (simp add: local.soft_svm_def)
      then have "\<forall>x. x \<in> H \<longrightarrow>
       (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n) x 
        \<ge>  (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n  ) ( h)"
        by auto


      then have " is_arg_min 
          (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n  )
           (\<lambda> h. h \<in> H) ( h)"
        by (metis (no_types, lifting) \<open> h \<in> H\<close> is_arg_min_linorder) 

      then have 8:" is_arg_min 
          (\<lambda>h.  (\<Sum>i = 0..<n. (?hingei h i)) / real n + k * (norm h)\<^sup>2  )
           (\<lambda> h. h \<in> H) (h)"
        by (smt is_arg_min_linorder)


      have "(\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n) +
      (\<lambda>w. k * (norm w)\<^sup>2) = 
          (\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n  + k * (norm h)\<^sup>2)" by auto
      then have "ridge_fun S k =
    (\<lambda>h. (\<Sum>i = 0..<n. (?hingei h i)) / real n  + k * (norm h)\<^sup>2)" 
        unfolding ridge_fun.simps unfolding train_err_loss_def by simp


      then show " is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) ( h)"
        using 8  by auto
    next
      assume "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h" 
      have "h\<in>H" 
        using \<open>is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) h\<close> is_arg_min_def by fastforce
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
            unfolding hinge_loss.simps using 2 3 by auto

          show "soft_svm x \<ge> soft_svm (fst x, ?hingei (fst x))"
            unfolding soft_svm_def 
            by (smt "5" divide_le_0_1_iff fst_conv n_pos of_nat_1 of_nat_mono real_mult_le_cancel_iff2 snd_conv sum_mono)
        qed
      qed



      have "(\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n) +
      (\<lambda>w. k * (norm w)\<^sup>2) = 
          (\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n  + k * (norm h)\<^sup>2)" by auto
      then have "ridge_fun S k =
    (\<lambda>h. (\<Sum>i = 0..<n. (?hingei h i)) / real n  + k * (norm h)\<^sup>2)" 
        unfolding ridge_fun.simps unfolding train_err_loss_def by simp

      then have 1:" is_arg_min 
          (\<lambda>h.  (\<Sum>i = 0..<n. (?hingei h i)) / real n + k * (norm h)\<^sup>2  )
           (\<lambda> h. h \<in> H) (h)"
        using \<open>is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) ( h)\<close> by auto

      then have " is_arg_min 
          (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n  )
           (\<lambda> h. h \<in> H) (h)" 
        by (smt is_arg_min_linorder)
      then have "\<forall>x. x \<in> H \<longrightarrow>
       (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n) x 
        \<ge>  (\<lambda>h. k * (norm h)\<^sup>2 + (\<Sum>i = 0..<n. (?hingei h i)) / real n  ) (h)" 
        by (metis (mono_tags, lifting) is_arg_min_linorder)


      then have "\<forall> x. fst x \<in> H \<longrightarrow>
  k * norm (fst x)^2 + (1/n)* (\<Sum>i\<in>{0..<n}. ((?hingei (fst x)) i)) 
    \<ge> soft_svm ( h, ?ksi')" 
        by (simp add: local.soft_svm_def)

      then have "\<forall>x. snd x = ?hingei (fst x) \<and> fst x \<in> H \<longrightarrow> 
     soft_svm x \<ge> soft_svm (h, ?ksi')"
        by (simp add: local.soft_svm_def) 




      then have 10: "\<forall> x. ?P x \<longrightarrow>
        soft_svm x \<ge> soft_svm (h, ?ksi')" using 9 
        by (smt \<open>\<forall>x. fst x \<in> H \<longrightarrow> local.soft_svm (h, \<lambda>i. hinge_loss h (S i)) \<le> k * (norm (fst x))\<^sup>2 + 1 / real n * (\<Sum>i = 0..<n. hinge_loss (fst x) (S i))\<close> fst_conv local.soft_svm_def snd_conv)

      have "?P (h, ?ksi')" unfolding hinge_loss.simps using `h\<in>H` by auto 
      then show "is_arg_min (soft_svm) ?P (h, ?ksi')" using 10
        by (simp add: is_arg_min_linorder)

    qed
  qed
  have "is_arg_min (ridge_fun S k) (\<lambda>s. s \<in> H) (ridge_mine S k)" 
    using S_in_D k_pos learning_basics1.in_argmin learning_basics1_axioms ridge_argmin_def by fastforce
  then have 12: "is_arg_min soft_svm ?P ((ridge_mine S k), ?hingei (ridge_mine S k))"
    using 11 by auto

  have "(\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n) +
      (\<lambda>w. k * (norm w)\<^sup>2) = 
          (\<lambda>h. (\<Sum>i = 0..<n. hinge_loss h (S i)) /
            real n  + k * (norm h)\<^sup>2)" by auto
  then have "ridge_fun S k =
    (\<lambda>h. (\<Sum>i = 0..<n. (?hingei h i)) / real n  + k * (norm h)\<^sup>2)" 
    unfolding ridge_fun.simps unfolding train_err_loss_def by simp
  then have "ridge_fun S k (ridge_mine S k) = 
      (\<Sum>i = 0..<n. (?hingei (ridge_mine S k) i)) / real n  + k * (norm (ridge_mine S k))\<^sup>2"
    by auto
  also have " \<dots> = 
          soft_svm ((ridge_mine S k), ?hingei (ridge_mine S k))" 
    by (simp add: local.soft_svm_def)
  finally have "ridge_fun S k (ridge_mine S k) =
         soft_svm ((ridge_mine S k), ?hingei (ridge_mine S k))" by auto
  then have 13: "ridge_fun S k (ridge_mine S k) =  
    soft_svm (SOME h. is_arg_min (soft_svm) ?P h)" using  12  
    by (smt is_arg_min_linorder someI_ex)
  have "(SOME h. is_arg_min (soft_svm) ?P h) = soft_svm_mine" 
    unfolding soft_svm_mine_def unfolding soft_svm_argmin_def
    by simp
  then show ?thesis using 13 by auto

qed

lemma 
  assumes "h\<in>H"
  shows "measure_pmf.expectation (Samples n D)
                              (\<lambda> S.  pred_err_loss D hinge_loss (ridge_mine S k)) \<le>
    pred_err_loss D hinge_loss h  + k * norm ( h )^2  + (2*\<rho>^2)/(k*n)" 
  using assms oracle_inequality by blast

end