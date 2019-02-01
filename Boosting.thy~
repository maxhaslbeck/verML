theory Boosting
  imports Complex_Main LinearPredictor
begin


locale BOOST =
  fixes C :: "'a set"
    and y :: "'a \<Rightarrow> real"
    and oh :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  assumes 
       nonemptyx: "C \<noteq> {}"
    and finitex: "finite C"
    and ytwoclass: "\<forall>x. y x \<in> {-1,1}"
    and ohtwoclass: "\<forall>Ds x. oh Ds x \<in> {-1,1}"
begin




lemma cardxgtz:"card C > 0"
  by (simp add: card_gt_0_iff finitex nonemptyx) 



fun h :: "nat \<Rightarrow> 'a \<Rightarrow> real"
and \<epsilon> :: "nat \<Rightarrow> real"
and w :: "nat \<Rightarrow> real"
and D :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
    "h t i = oh (\<lambda>x. D t x) i"
  | "\<epsilon> t = sum (\<lambda>x. D t x) {x\<in>C. h t x \<noteq> y x}"
  | "w t = (ln (1/(\<epsilon> t)-1))/2"
  | "D (Suc t) i = (D t i * exp (-(w t)*(h t i)*(y i))) / (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) C)"
  | "D 0 i = 1/(card C)"

lemma ctov: "h t x = y x \<Longrightarrow> h t x * y x = 1" and ctov2: "h t x \<noteq> y x \<Longrightarrow> h t x * y x = -1"
  apply (smt empty_iff insert_iff mult_cancel_left2 mult_minus_right ytwoclass)
  by (metis empty_iff h.simps insert_iff mult.commute mult.left_neutral ohtwoclass ytwoclass)
    
  
fun f :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "f (Suc t) i = (w t) * (h t i) + f t i"
|"f 0 i = 0"

lemma aux34: "movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0))
        = (\<lambda>t. (if t < k then w t else 0))" using vec_lambda_inverse lt_valid[of k w]
    by auto

lemma aux35: "movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then h t i else 0))
        = (\<lambda>t. (if t < k then h t i else 0))" using vec_lambda_inverse lt_valid[of k "(\<lambda>t. h t i)"]
    by auto

definition "hyp k i = (f k i > 0)"

lemma convert_f: "(\<lambda>i. f k i > 0)  = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then w t else 0))) 
                                                 (vec_lambda (\<lambda>t. (if t<k then h t i else 0)))))"
proof -
  from aux34 have "\<forall>i. {q. movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) q \<noteq> 0 
        \<and> movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then h t i else 0))) q \<noteq> 0} \<subseteq> {..<k}"
    by auto
  then have "\<forall>i. minner (movec.vec_lambda (\<lambda>t. if t < k then w t else 0))
               (vec_lambda (\<lambda>t. (if t<k then h t i else 0)))
             = (\<Sum>ia\<in>{..<k}.
                 movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) ia \<bullet>
                 movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then h t i else 0))) ia)"
    using minner_alt by auto
  moreover have "\<forall>i. (\<Sum>ia\<in>{..<k}.
                 movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) ia \<bullet>
                 movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then h t i else 0))) ia) = f k i"
    unfolding aux34 aux35 
    apply(induction k)
    by auto
  ultimately show ?thesis unfolding linear_predictor_def by auto
qed

    
    
lemma "linear_predictor (vec_lambda (\<lambda>t. (if t<k then w t else 0))) \<in> all_linear(myroom k)"
  using all_linear_def aux34 myroom_def by auto



lemma "finite M1 \<Longrightarrow> finite M2 \<Longrightarrow> card ((\<lambda>(m1,m2). m1 \<circ>\<^sub>m m2) ` (M1 \<times> M2)) \<le> card M1 * card M2"
  using card_image_le finite_cartesian_product card_cartesian_product
  by (metis Sigma_cong)

lemma only_one: "a\<in>A \<Longrightarrow> \<forall>b\<in>A. b = a \<Longrightarrow> card A = 1"
  by (metis (no_types, hide_lams) One_nat_def card.empty card_Suc_eq empty_iff equalityI insert_iff subsetI) 

lemma "card ({vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. vec_nth (vm (x::'a)) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. vec_nth (vm x) t = 0) }) = card Hb ^ k"
proof(induct k)
  case 0
  obtain f::"('a\<Rightarrow>movec)" where o1: "\<forall>x. f x = 0" by fastforce
  then have s1: "f\<in>{vm. (\<forall>t<0. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>0. \<forall>x. movec.vec_nth (vm x) t = 0)}"
    by simp 
  have "\<forall>g\<in>{vm. (\<forall>t<0. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>0. \<forall>x. movec.vec_nth (vm x) t = 0)}.  \<forall>x. g x = 0"
    using movec_eq_iff by auto
  then have "\<forall>g\<in>{vm. (\<forall>t<0. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>0. \<forall>x. movec.vec_nth (vm x) t = 0)}.  g = f"
    using o1 by auto
  then have "card {vm. (\<forall>t<0. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>0. \<forall>x. movec.vec_nth (vm x) t = 0)} = 1"
    using s1 by (simp add: only_one)  
  then show ?case by auto 
next
  case (Suc k)
  have "{vm. (\<forall>t<Suc k. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>Suc k. \<forall>x. movec.vec_nth (vm x) t = 0)} \<subseteq>
     (\<lambda>(vm, g). (\<lambda>x. upd_movec (vm x) k (g x))) ` ({vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. movec.vec_nth (vm x) t = 0)} \<times> Hb)"
  proof (auto)
    fix vm
    assume a1: "\<forall>t<Suc k. \<exists>m\<in>Hb. \<forall>xa. movec.vec_nth (vm xa) t = m xa"
            "\<forall>t\<ge>Suc k. \<forall>xa. movec.vec_nth (vm xa) t = 0"
    let ?kM = "{vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. movec.vec_nth (vm x) t = 0)}"
    let ?wm = "(\<lambda>x. upd_movec (vm x) k 0)"
    have "?wm\<in>?kM" sorry
    obtain h where o1: "h\<in>Hb" "\<forall>x. vec_nth (vm x) k = h x" using a1 by auto

    have "\<exists>wm\<in>{vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. movec.vec_nth (vm x) t = 0)}. \<exists>h\<in>Hb.
   vm = (\<lambda>(vm, g) x. movec.vec_lambda (\<lambda>k'. if k' = k then g x else movec.vec_nth (vm x) k')) (wm, h)"
      sorry
    then show "vm \<in> (\<lambda>(vm, g) x. movec.vec_lambda (\<lambda>k'. if k' = k then g x else movec.vec_nth (vm x) k')) `
       ({vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. movec.vec_nth (vm x) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. movec.vec_nth (vm x) t = 0)} \<times> Hb)"
      by auto
  qed
  then show ?case sorry
qed


lemma aux857: "(x::real) \<ge> 1 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> x+z \<le> x*(1+z)"
proof -
  assume "x\<ge>1" "z\<ge>0"
  moreover from this have "x*z \<ge> z"
    by (metis mult_cancel_right2 ordered_comm_semiring_class.comm_mult_left_mono
        semiring_normalization_rules(7))
  ultimately show "x+z \<le> x*(1+z)"
    by (simp add: distrib_left)
qed


lemma two_le_e: "(2::real) < exp 1" using  exp_less_mono
  by (metis exp_ge_add_one_self less_eq_real_def ln_2_less_1 ln_exp numeral_Bit0 numeral_One) 


lemma ln_bound_linear: "x>0 \<Longrightarrow> ln (x::real) \<le> x*(exp (-1))"
proof -
  fix x::real
  assume "x>0"
  have f1: "\<forall>r. r + ln x = ln (x *\<^sub>R exp r)"
    by (simp add: \<open>0 < x\<close> ln_mult)
  have "\<forall>r ra. (ra::real) + (- ra + r) = r"
    by simp
  then have "exp (ln(x)) \<le> exp(x*(exp(-1)))"
    using f1 by (metis (no_types) \<open>0 < x\<close> exp_ge_add_one_self exp_gt_zero
                 exp_le_cancel_iff exp_ln mult_pos_pos real_scaleR_def)
  then show "ln x \<le> x * exp (- 1)"
    by blast
qed

lemma ln_bound_linear2: "x>0 \<Longrightarrow> (exp 1) * ln (x::real) \<le> x"
  by (metis (no_types, hide_lams) add.inverse_inverse divide_inverse exp_gt_zero exp_minus
      ln_bound_linear mult.commute pos_divide_le_eq)
  
lemma ln_bound_linear3: "x>0 \<Longrightarrow> a\<le>exp 1 \<Longrightarrow> a > 0 \<Longrightarrow> a * ln (x::real) \<le> x"
proof -
assume a1: "0 < x"
assume a2: "0 < a"
  assume a3: "a \<le> exp 1"
  have f4: "\<forall>r ra. (ra::real) \<le> r \<or> \<not> ra < r"
    by (simp add: linear not_less)
  then have f5: "\<forall>r. r \<le> x \<or> 0 < r"
    using a1 by (meson dual_order.trans not_less)
  have f6: "\<not> a < 0"
    using f4 a2 by (meson not_less)
  have f7: "\<forall>r ra rb. ((r::real) \<le> rb \<or> ra < r) \<or> rb < ra"
    by (meson dual_order.trans not_less)
  have f8: "\<forall>r. r < x \<or> \<not> r < exp 1 * ln x"
    using a1 by (meson dual_order.trans ln_bound_linear2 not_less)
  have f9: "\<forall>r. \<not> (r::real) < r"
by blast
have "\<not> exp 1 < a"
  using a3 not_less by blast
  then show ?thesis
    using f9 f8 f7 f6 f5 f4 by (metis (no_types) mult_less_cancel_right zero_less_mult_iff)
qed
    


lemma fixes a b::real
  assumes "b\<ge>0"
    and "a\<ge>sqrt(exp 1)"
  shows aux937: "(2*a*ln(a) + b) - a * ln (2*a*ln(a) + b) > 0"
proof -
  have "2*ln(sqrt(exp 1)) = 1"
    by (simp add: ln_sqrt)
  then have f1: "2*ln(a) \<ge> 1" using assms(2)
    by (smt ln_le_cancel_iff not_exp_le_zero real_sqrt_gt_zero) 
  have f2: "a > 1"
    using assms(2) less_le_trans less_numeral_extra(1) one_less_exp_iff real_sqrt_gt_1_iff by blast 
  have f3: "b/a \<ge> 0" using assms(1) f2 by auto


  have "2*ln(a) + b/a \<le> 2*ln(a)*(1+b/a)" using aux857 f1 f3 by auto
  then have "ln (2*ln(a) + b/a) \<le> ln (2*ln(a)*(1+b/a))"
    using f1 f3 by auto 
  then have f4: "- a * ln(2*ln(a)+b/a) \<ge> - a * ln (2*ln(a)*(1+b/a))"
    using f2 by auto
  have f5: "ln(2*ln(a)*(1+b/a)) = ln(2*ln(a)) + ln(1+b/a)"
    using f1 f3 ln_mult by auto

  have "2*a*ln(a) + b = a*(2*ln(a)+b/a)"
    using f2 by (simp add: distrib_left mult.commute)
  moreover have "(2*ln(a)+b/a) > 0"
    using f1 f3 by linarith 
  ultimately have "ln (2*a*ln(a) + b) = ln a + ln(2*ln(a)+b/a)"
    using ln_mult f2 by auto
  then have "(2*a*ln(a) + b) - a * ln (2*a*ln(a) + b)
              = 2*a*ln(a) + b - a * (ln a + ln(2*ln(a)+b/a))" by auto
  also have "... = a*ln(a) + b - a * ln(2*ln(a)+b/a)"
    by (simp add: distrib_left) 
  also have "... \<ge>
            a*ln(a) + b - a * ln(2*ln(a)*(1+b/a))" using f4 by auto

  also have "a*ln(a) + b - a * ln(2*ln(a)*(1+b/a))
           = a*ln(a) - a * ln(2*ln(a)) + b - a * ln(1+b/a)"
    using f5 by (simp add: distrib_left)
  finally have f6: "(2*a*ln(a) + b) - a * ln (2*a*ln(a) + b)
                \<ge> a*ln(a) - a * ln(2*ln(a)) + b - a * ln(1+b/a)" by auto

  have "b/a - a/a * ln(1+b/a) \<ge> 0" using f2 f3 ln_add_one_self_le_self by auto
  then have f7: "b - a * ln(1+b/a) \<ge> 0" using f2
    by (metis diff_ge_0_iff_ge dual_order.trans nonzero_mult_div_cancel_left not_le
        real_mult_le_cancel_iff2 times_divide_eq_left times_divide_eq_right zero_le_one) 


   have "a \<ge> exp 1 * ln a"
    using f2 ln_bound_linear2 by auto
   moreover have "exp 1 * ln a > 2 * ln a" using two_le_e f2
     using ln_gt_zero mult_less_cancel_right_disj by blast 
   ultimately have "ln a > ln (2 * ln a)" 
     using f1 by (metis exp_gt_zero less_le_trans less_numeral_extra(1)
         ln_less_cancel_iff not_numeral_less_zero zero_less_mult_iff)  
   then have "(ln(a)-ln(2*ln(a)))>0" by auto
   then have "a*ln(a) - a * ln(2*ln(a)) > 0"
     using f2 by auto
   from this f6 f7 show ?thesis by auto
qed


lemma fixes x a b::real
  assumes "x>0" 
      and "a>0"
      and "x \<ge> 2*a*ln(a)"
    shows aux683: "x \<ge> a* ln(x)" 
proof (cases "a<sqrt(exp 1)")
  case True
  moreover have "(1::real) < exp 1"
    by auto
  ultimately have "a \<le> exp (1::real)"
    by (metis eucl_less_le_not_le exp_gt_zero exp_half_le2 exp_ln linear ln_exp ln_sqrt not_less
        order.trans real_sqrt_gt_zero two_le_e)
  then show ?thesis using ln_bound_linear3 assms(1,2) by auto
next
  case c1: False
  obtain b where "x = (2*a*ln(a) + b)" "b\<ge>0" using assms(3)
    by (metis add.commute add.group_left_neutral add_mono_thms_linordered_field(1) diff_add_cancel
        le_less_trans less_irrefl not_le of_nat_numeral real_scaleR_def)
  moreover from this have "(2*a*ln(a) + b)  > a * ln (2*a*ln(a) + b)"
    using aux937 c1 by auto
  ultimately show ?thesis by auto
qed

lemma fixes x a::real
  shows "0 < x \<Longrightarrow> 0 < a \<Longrightarrow> x < a* ln(x) \<Longrightarrow> x < 2*a*ln(a)"
  using aux683 by (meson not_less)



lemma splitf: "exp (- f (Suc t) i * y i) = ((exp (- f t i * y i)) * exp (-(w (t))*(h (t) i)*(y i)))"
proof -
  have "f (Suc t) i * - y i = - f t i * y i + - w (t) * h (t) i * y i"    
    by (simp add: distrib_right)
  then have "- f (Suc t) i * y i = - f t i * y i + - w (t) * h (t) i * y i"
    by linarith 
  then show ?thesis using exp_add by metis
qed

lemma Dalt: "D t i = (exp (- ((f t i)) * (y i))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C)"
proof (induction t arbitrary: i)
  case 0
  show ?case by (simp add: sum_distrib_left cardxgtz)
next
  case c1: (Suc t)
  then have "D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>C. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ (sum (\<lambda>x. (exp (- f t x * y x) / (\<Sum>xx\<in>C. exp (- f t xx * y xx))) * exp (-(w t)*(h t x)*(y x))) C)"
    by auto
  then have s0:"D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>C. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) C)/ (\<Sum>x\<in>C. exp (- f t x * y x)))"
    by (simp add: sum_divide_distrib)
     have "(\<Sum>x\<in>C. exp (- f t x * y x)) > 0" by (simp add: nonemptyx finitex sum_pos)
     from s0 this have s1:"D (Suc t) i
= ((exp (- f t i * y i)) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) C))"
       by simp
     from s1 splitf show ?case by simp
qed


lemma dione: "sum (\<lambda>q. D t q) C = 1"
proof-
  have "sum (\<lambda>q. D t q) C = sum (\<lambda>q. (exp (- ((f t q)) * (y q))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C)) C"
    using Dalt by auto
  also have " sum (\<lambda>q. (exp (- ((f t q)) * (y q))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C)) C
           =  sum (\<lambda>q. (exp (- ((f t q)) * (y q)))) C / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C)"
    using sum_divide_distrib by (metis (mono_tags, lifting) sum.cong)
  also have "sum (\<lambda>q. (exp (- ((f t q)) * (y q)))) C / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C) = 1"
  using sum_pos finitex nonemptyx by (smt divide_self exp_gt_zero)
  finally show ?thesis by simp
qed

lemma dgtz: "D t x > 0"
proof (cases t)
  case 0
  then show ?thesis by (simp add: cardxgtz)
next
  case (Suc nat)
  then show ?thesis using sum_pos finitex nonemptyx Dalt exp_gt_zero
    by (smt divide_pos_neg minus_divide_right)
qed

lemma assumes "(a::real) \<le> b" and "0\<le>a" and "b \<le> 1/2"
      shows amono: "a*(1-a) \<le> b*(1-b)"
proof -
  let ?c = "b-a"
  have s1:"?c \<ge> 0" using assms by auto
  have "2*a+?c \<le> 1" using assms by auto
  then have "2*a*?c+?c*?c \<le> ?c" using assms
    by (metis distrib_left mult.commute mult_left_mono mult_numeral_1_right numeral_One s1)
  then have s2: "0 \<le> ?c - 2*a*?c-?c^2" by (simp add: power2_eq_square)
  have "a*(1-a) + ?c - ?c^2 -2*a*?c = b*(1-b)"
    by (simp add: Groups.mult_ac(2) left_diff_distrib power2_eq_square right_diff_distrib)
  from this s2 show ?thesis by auto
qed


definition dez:"Z t = 1/(card C) * (sum (\<lambda>x. exp (- (f t x) * (y x))) C)"


lemma
  assumes "\<forall>t. \<epsilon> t \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t \<noteq> 0" and "\<gamma> > 0"
  shows main101: "(Z (Suc t)) / (Z t) \<le> exp(-2*\<gamma>^2)"
proof -
  have s3: "\<forall>t. \<epsilon> t > 0" using sum_pos assms(2)
      by (metis (no_types, lifting) BOOST.\<epsilon>.elims BOOST_axioms dgtz sum.empty sum.infinite)
  have s1: "{x\<in>C. h t x = y x}\<inter>{x\<in>C. h t x \<noteq> y x} = {}"
    by auto
  have s2: "{x\<in>C. h t x = y x}\<union>{x\<in>C. h t x \<noteq> y x} = C"
    by auto
  have s10:"(Z (Suc t)) / (Z t) = (sum (\<lambda>x. exp (- (f (Suc t) x) * (y x))) C) / (sum (\<lambda>x. exp (- (f t x) * (y x))) C)"
    by (auto simp: dez cardxgtz)
  also have "(sum (\<lambda>x. exp (- (f (Suc t) x) * (y x))) C)
   = (sum (\<lambda>x. exp (- f t x * y x) * exp (-(w ( t))*(h ( t) x)*(y x))) C)"
    using splitf by auto
  also have "(sum (\<lambda>x. exp (- f t x * y x) * exp (-(w t)*(h t x)*(y x))) C) / (sum (\<lambda>x. exp (- (f t x) * (y x))) C)
  = (sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) C) * exp (-(w t)*(h t x)*(y x))) C)"
    using sum_divide_distrib by simp
  also have "(sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) C) * exp (-(w t)*(h t x)*(y x))) C)
      = (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) C)"
    using Dalt by simp
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) C
  = sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>C. h t x = y x}
  + sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>C. h t x \<noteq> y x}"
    using Groups_Big.comm_monoid_add_class.sum.union_disjoint finitex s1 s2 
    by (metis (no_types, lifting) finite_Un)
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>C. h t x = y x}
            = sum (\<lambda>x. D t x * exp (-(w t))) {x\<in>C. h t x = y x}"
    by (smt add.inverse_inverse empty_iff h.elims insert_iff mem_Collect_eq mult.left_neutral mult_cancel_left2 mult_minus1_right mult_minus_right sum.cong ytwoclass)
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>C. h t x \<noteq> y x}
            = sum (\<lambda>x. D t x * exp (w t)) {x\<in>C. h t x \<noteq> y x}"
    using ctov2 by (simp add: Groups.mult_ac(1))
  also have "(\<Sum>x | x \<in> C \<and> h t x = y x. D t x * exp (- w t)) +
  (\<Sum>x | x \<in> C \<and> h t x \<noteq> y x. D t x * exp (w t))
        = (\<Sum>x | x \<in> C \<and> h t x = y x. D t x) * exp (- w t) +
  (\<Sum>x | x \<in> C \<and> h t x \<noteq> y x. D t x) * exp (w t)"
    by (simp add: sum_distrib_right)
  also have "(\<Sum>x | x \<in> C \<and> h t x \<noteq> y x. D t x) = \<epsilon> t" by auto
  also have "(\<Sum>x | x \<in> C \<and> h t x = y x. D t x) = 1 - \<epsilon> t"
  proof -
    have "(\<Sum>x | x \<in> C \<and> h t x = y x. D t x) + (\<Sum>x | x \<in> C \<and> h t x \<noteq> y x. D t x)
        = sum (D t) C"
    using Groups_Big.comm_monoid_add_class.sum.union_disjoint finitex s1 s2 
      by (metis (no_types, lifting) finite_Un)
    then show ?thesis using dione
      by (smt Collect_cong \<epsilon>.simps)
  qed
  also have "exp (- w t) = 1/ exp(w t)"
    by (smt exp_minus_inverse exp_not_eq_zero nonzero_mult_div_cancel_right)
  also have "exp(w t) = sqrt (1/(\<epsilon> t)-1)"
  proof - 
    from s3 have  "(1/(\<epsilon> t)-1) > 0"
      by (smt assms(1) assms(3) less_divide_eq_1_pos)
    then have "exp (((ln (1/(\<epsilon> t)-1)) * 1/2)) = sqrt (1/(\<epsilon> t)-1)"
      by (smt exp_ln ln_sqrt real_sqrt_gt_zero)
    then show ?thesis by auto
  qed
  also have "sqrt(1/(\<epsilon> t)-1) = sqrt(1/(\<epsilon> t)-(\<epsilon> t)/(\<epsilon> t))"
    using assms(2) by (metis divide_self) 
  also have "sqrt(1/(\<epsilon> t)-(\<epsilon> t)/(\<epsilon> t)) = sqrt((1 - \<epsilon> t)/\<epsilon> t)"
    by (simp add: diff_divide_distrib)
  also have "1/(sqrt((1 - \<epsilon> t)/\<epsilon> t)) = sqrt(\<epsilon> t) / sqrt((1 - \<epsilon> t))"
    by (simp add: real_sqrt_divide)
  also have "\<epsilon> t * sqrt((1 - \<epsilon> t)/(\<epsilon> t)) =  sqrt(1 - \<epsilon> t) * sqrt(\<epsilon> t)"
    by (smt linordered_field_class.sign_simps(24) real_div_sqrt real_sqrt_divide s3 times_divide_eq_right)
  also have s19:"(1 - \<epsilon> t)* (sqrt (\<epsilon> t)/ sqrt(1 - \<epsilon> t)) = sqrt (\<epsilon> t)* sqrt(1 - \<epsilon> t)"
    using assms(1,3) by (smt less_divide_eq_1_pos mult.commute real_div_sqrt times_divide_eq_left)
  also have "sqrt (\<epsilon> t) * sqrt (1 - \<epsilon> t) + sqrt (1 - \<epsilon> t) * sqrt (\<epsilon> t)
            = 2 * sqrt((1 - \<epsilon> t) * \<epsilon> t)"
    using divide_cancel_right real_sqrt_mult by auto
  also have s20:"2* sqrt((1 - \<epsilon> t) * \<epsilon> t) \<le> 2* sqrt((1/2-\<gamma>)*(1-(1/2-\<gamma>)))"
    proof -
      have "((1 - \<epsilon> t) * \<epsilon> t) \<le> ((1/2-\<gamma>)*(1-(1/2-\<gamma>)))"
        using assms(1,3) amono s3 by (smt mult.commute)
      then show ?thesis by auto
    qed
  also have "2 * sqrt ((1 / 2 - \<gamma>) * (1 - (1 / 2 - \<gamma>))) = 2 * sqrt(1/4-\<gamma>^2)"
       by (simp add: algebra_simps power2_eq_square)
      
  also have "2 * sqrt(1/4-\<gamma>^2) = sqrt(4*(1/4-\<gamma>^2))"
    using real_sqrt_four real_sqrt_mult by presburger 
  also have "sqrt(4*(1/4-\<gamma>^2)) = sqrt(1-4*\<gamma>^2)" by auto
  also have "sqrt(1-4*\<gamma>^2) \<le> sqrt(exp(-4*\<gamma>^2))"
  proof -
    have "1-4*\<gamma>^2 \<le> exp(-4*\<gamma>^2)"
      by (metis (no_types) add_uminus_conv_diff exp_ge_add_one_self mult_minus_left)
    then show ?thesis by auto
  qed
  also have "sqrt(exp(-4*\<gamma>^2)) = exp(-4*\<gamma>^2/2)"
    by (metis exp_gt_zero exp_ln ln_exp ln_sqrt real_sqrt_gt_0_iff)
  finally show ?thesis by auto
qed

  
lemma help1:"(b::real) > 0 \<Longrightarrow> a / b \<le> c \<Longrightarrow> a \<le> b * c"
  by (smt mult.commute pos_less_divide_eq)

definition defloss: "loss t = 1/(card C) *(sum (\<lambda>x. (if (f t x * (y x)) > 0 then 0 else 1)) C)"


lemma
  assumes "\<forall>t. \<epsilon> t \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t \<noteq> 0" and "\<gamma> > 0"
  shows main102: "loss T \<le> exp (-2*\<gamma>^2*T)"
proof -
  have s1: "\<forall>k. Z k > 0"
    using dez finitex nonemptyx cardxgtz by (simp add: sum_pos)
  have s2: "Z T \<le> exp(-2*\<gamma>^2*T)"
  proof (induction T)
    case 0
    then show ?case 
      by (simp add: dez)
    next
      case c1:(Suc T)
    from main101 s1 have s3:"Z (Suc T) \<le> exp (-2*\<gamma>^2) * Z T"
      by (metis assms(1) assms(2) assms(3) help1 mult.commute)
    from c1 have "exp (-2*\<gamma>^2) * Z T  \<le> exp (-2*\<gamma>^2 *T) * exp (-2*\<gamma>^2)" by auto
    from this s3 show ?case
      by (smt exp_of_nat_mult power_Suc2 semiring_normalization_rules(7)) 
     (* by (smt Groups.mult_ac(2) exp_of_nat2_mult power.simps(2)) This proof worked on other version*)
  qed
  have help3: "\<forall>n. sum (\<lambda>x. if 0 < f T x * y x then 0 else 1) C \<le> sum (\<lambda>x. exp (- (f T x * y x))) C"
    by (simp add: sum_mono)
  then have s3: "loss T \<le> Z T" 
    by (simp add: defloss dez divide_right_mono)
  from s2 s3 show ?thesis by auto
qed
end

locale allboost =
  fixes X :: "'a set"
    and y :: "'a \<Rightarrow> real"
    and oh :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
    and T :: nat
    and B :: "('a \<Rightarrow> real) set"
assumes "infinite X"
    and ytwoclass: "\<forall>x. y x \<in> {-1,1}"
    and ohtwoclass: "\<forall>Ds. oh Ds \<in> B"
    and "\<forall>h x. h \<in> B \<longrightarrow> h x \<in> {- 1, 1}"
    and nonemptyB: "B \<noteq> {}"
begin
term BOOST.hyp

definition "H t = (\<lambda>S. BOOST.hyp S y oh t) `{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}"
definition "H' t = (\<lambda>(S, oh). BOOST.hyp S y oh t) `({S. S\<subseteq>X \<and> S\<noteq>{}}\<times>{oh. \<forall>DS. oh DS \<in> B})"

lemma aux1: "BOOST S y oh \<Longrightarrow> BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))"
proof -
  assume a1: "BOOST S y oh"
  then have "BOOST.hyp S y oh k = (\<lambda>i. 0 < BOOST.f S y oh k i)" using BOOST.hyp_def by fastforce
  also have "(\<lambda>i. 0 < BOOST.f S y oh k i) = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then BOOST.h S y oh t i else 0)))))" using BOOST.convert_f a1 by auto
  finally have s1: "BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then BOOST.h S y oh t i else 0)))))" by auto
  moreover have s1: "\<And>t i. BOOST.h S y oh t i = oh (BOOST.D S y oh t) i"
    by (simp add: BOOST.h.simps a1)
  then have "\<And> i. (\<lambda>t. (if t<k then BOOST.h S y oh t i else 0)) = (\<lambda>t. (if t<k then oh (BOOST.D S y oh t) i else 0))"
    by auto 
  then have "(\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then BOOST.h S y oh t i else 0)))))
       = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))" by auto
  then show "BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))" using s1
    by (simp add: calculation)
qed
   


lemma aux02: "\<forall>S\<in>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}. BOOST S y oh \<Longrightarrow> H k = (\<lambda>S i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))`{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}"
   using aux1[of _ k] H_def[of k]
   by (smt image_cong) 

lemma aux01: "(\<lambda>S i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))`{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}
\<subseteq> (\<lambda>(S,S') i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))))`({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})"
  by auto

lemma aux2: "(\<lambda> i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
       (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))))
=((\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))))"
  by auto

lemma aux3: "(\<lambda>(S, S')i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
       (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0))))) ` ({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}) 
=(\<lambda>(S,S').(\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0))))) ` ({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})"
  using aux2 by simp

definition "WH k = (\<lambda>S. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))) ` {S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}"

definition "Agg k = (\<lambda>S' i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))) ` {S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}"

lemma "Agg k \<subseteq> {vm. (\<forall>t<k. \<exists>m\<in>B. \<forall>x. vec_nth (vm (x::'a)) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. vec_nth (vm x) t = 0) }"
  unfolding Agg_def using ohtwoclass
  oops

lemma aux4: "(\<lambda>(S,S').(\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0))))) ` ({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})
= {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}" unfolding WH_def Agg_def by auto

lemma "\<forall>S\<in>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}. BOOST S y oh \<Longrightarrow> H k \<subseteq> {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}"
  using aux4 aux3 aux01 aux02 by auto

lemma "(\<lambda>h. restrict_map (mapify h) C) ` {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}  \<subseteq>
      {map. \<exists>a\<in>((\<lambda>h. restrict_map (mapify h) C) ` (Agg k)). \<exists>w\<in>((\<lambda>h. restrict_map (mapify h) (ran a)) ` (WH k)).
       map = w \<circ>\<^sub>m a}"
proof safe
  fix w a
  assume "w \<in> WH k" "a \<in> Agg k"
  have "mapify (w\<circ>a) = (mapify w) \<circ>\<^sub>m (mapify a)" unfolding mapify_alt map_comp_def by auto
  have "((mapify w) \<circ>\<^sub>m (mapify a)) |` C = (mapify w) \<circ>\<^sub>m ((mapify a) |` C)"
    unfolding restrict_map_def map_comp_def by auto
  have "(mapify w) \<circ>\<^sub>m ((mapify a) |` C) = ((mapify w)|` ran ((mapify a) |` C)) \<circ>\<^sub>m ((mapify a) |` C)"
    using restrict_map_def map_comp_def ran_def 

lemma "(\<lambda>(S,S') i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
       (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))))`({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})
\<subseteq>(\<lambda>(w, S'). (\<lambda>v. linear_predictor w v) \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y oh t) i) else 0)))))
   ` (((\<lambda>S. (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))) ` {S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})\<times>{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S})"


lemma "(\<lambda>S i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))`{S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}
\<subseteq> (\<lambda>(S,b) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (b i) else 0)))))`({S. S\<subseteq>X \<and> S\<noteq>{} \<and> finite S}\<times>B)"
proof
  fix x
  assume "x \<in> (\<lambda>S i. linear_predictor (movec.vec_lambda (\<lambda>t. if t < k then BOOST.w S y oh t else 0))
                     (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D S y oh t) i else 0))) `
             {S. S \<subseteq> X \<and> S \<noteq> {} \<and> finite S}"
  then obtain S where "S\<in>{S. S \<subseteq> X \<and> S \<noteq> {} \<and> finite S}" "x = (\<lambda>S i. linear_predictor (movec.vec_lambda (\<lambda>t. if t < k then BOOST.w S y oh t else 0))
                     (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D S y oh t) i else 0))) S" by auto
  obtain b where "b\<in>B" "\<forall>t. b = oh (BOOST.D S y oh t)" using ohtwoclass nonemptyB 


lemma "{vm. (\<forall>t<k. \<exists>m\<in>Hb. \<forall>x. vec_nth (vm (x::'a)) t = m x) \<and> (\<forall>t\<ge>k. \<forall>x. vec_nth (vm x) t = 0) }"

interpretation outer: vcd X "{True, False}" "H T"
proof
  show "card {True, False} = 2" by auto
  show "\<forall>h x. h \<in> H T \<longrightarrow> h x \<in> {True, False}" by auto
  have "{S. S \<subseteq> X \<and> S \<noteq> {}} \<noteq> {}"
    using allboost_axioms allboost_def order_refl by fastforce 
  then show "H T \<noteq> {}" unfolding H_def by blast
  show "infinite X"
    using allboost_axioms allboost_def by blast
qed

interpretation baseclass: vcd X "{-1::real,1}" B
proof
  show "card {- 1::real, 1} = 2" by auto
  show "\<forall>h x. h \<in> B \<longrightarrow> h x \<in> {- 1, 1}"
    by (meson allboost_axioms allboost_def)
  show  "B \<noteq> {}" "infinite X" using allboost_axioms allboost_def by auto
qed

find_theorems name:allboost

term outer.H_map

lemma "\<forall>C\<subseteq>X. restrictH outer.H_map C {True, False} \<subseteq> "