theory Boosting
  imports Complex_Main
begin


locale BOOST =
  fixes X :: "'a set"
    and y :: "'a \<Rightarrow> real"
    and oh :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  assumes 
       nonemptyx: "X \<noteq> {}"
    and finitex: "finite X"
    and ytwoclass: "\<forall>x. y x \<in> {-1,1}"
    and ohtwoclass: "\<forall>Ds x. oh Ds x \<in> {-1,1}"
begin

lemma cardxgtz:"card X > 0"
  by (simp add: card_gt_0_iff finitex nonemptyx) 



fun h :: "nat \<Rightarrow> 'a \<Rightarrow> real"
and \<epsilon> :: "nat \<Rightarrow> real"
and w :: "nat \<Rightarrow> real"
and D :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
    "h t i = oh (\<lambda>x. D t x) i"
  | "\<epsilon> t = sum (\<lambda>x. D t x) {x\<in>X. h t x \<noteq> y x}"
  | "w t = (ln (1/(\<epsilon> t)-1))/2"
  | "D (Suc t) i = (D t i * exp (-(w t)*(h t i)*(y i))) / (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) X)"
  | "D 0 i = 1/(card X)"

lemma ctov: "h t x = y x \<Longrightarrow> h t x * y x = 1" and ctov2: "h t x \<noteq> y x \<Longrightarrow> h t x * y x = -1"
  apply (smt empty_iff insert_iff mult_cancel_left2 mult_minus_right ytwoclass)
  by (metis empty_iff h.simps insert_iff mult.commute mult.left_neutral ohtwoclass ytwoclass)
    
  
fun f :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "f (Suc t) i = (w t) * (h t i) + f t i"
 |"f 0 i = 0"


lemma splitf: "exp (- f (Suc t) i * y i) = ((exp (- f t i * y i)) * exp (-(w (t))*(h (t) i)*(y i)))"
proof -
  have "f (Suc t) i * - y i = - f t i * y i + - w (t) * h (t) i * y i"    
    by (simp add: distrib_right)
  then have "- f (Suc t) i * y i = - f t i * y i + - w (t) * h (t) i * y i"
    by linarith 
  then show ?thesis using exp_add by metis
qed

lemma Dalt: "D t i = (exp (- ((f t i)) * (y i))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) X)"
proof (induction t arbitrary: i)
  case 0
  show ?case by (simp add: sum_distrib_left cardxgtz)
next
  case c1: (Suc t)
  then have "D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>X. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ (sum (\<lambda>x. (exp (- f t x * y x) / (\<Sum>xx\<in>X. exp (- f t xx * y xx))) * exp (-(w t)*(h t x)*(y x))) X)"
    by auto
  then have s0:"D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>X. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) X)/ (\<Sum>x\<in>X. exp (- f t x * y x)))"
    by (simp add: sum_divide_distrib)
     have "(\<Sum>x\<in>X. exp (- f t x * y x)) > 0" by (simp add: nonemptyx finitex sum_pos)
     from s0 this have s1:"D (Suc t) i
= ((exp (- f t i * y i)) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) X))"
       by simp
     from s1 splitf show ?case by simp
qed


lemma dione: "sum (\<lambda>q. D t q) X = 1"
proof-
  have "sum (\<lambda>q. D t q) X = sum (\<lambda>q. (exp (- ((f t q)) * (y q))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) X)) X"
    using Dalt by auto
  also have " sum (\<lambda>q. (exp (- ((f t q)) * (y q))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) X)) X
           =  sum (\<lambda>q. (exp (- ((f t q)) * (y q)))) X / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) X)"
    using sum_divide_distrib by (metis (mono_tags, lifting) sum.cong)
  also have "sum (\<lambda>q. (exp (- ((f t q)) * (y q)))) X / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) X) = 1"
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


definition dez:"Z t = 1/(card X) * (sum (\<lambda>x. exp (- (f t x) * (y x))) X)"


lemma
  assumes "\<forall>t. \<epsilon> t \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t \<noteq> 0" and "\<gamma> > 0"
  shows main101: "(Z (Suc t)) / (Z t) \<le> exp(-2*\<gamma>^2)"
proof -
  have s3: "\<forall>t. \<epsilon> t > 0" using sum_pos assms(2)
      by (metis (no_types, lifting) BOOST.\<epsilon>.elims BOOST_axioms dgtz sum.empty sum.infinite)
  have s1: "{x\<in>X. h t x = y x}\<inter>{x\<in>X. h t x \<noteq> y x} = {}"
    by auto
  have s2: "{x\<in>X. h t x = y x}\<union>{x\<in>X. h t x \<noteq> y x} = X"
    by auto
  have s10:"(Z (Suc t)) / (Z t) = (sum (\<lambda>x. exp (- (f (Suc t) x) * (y x))) X) / (sum (\<lambda>x. exp (- (f t x) * (y x))) X)"
    by (auto simp: dez cardxgtz)
  also have "(sum (\<lambda>x. exp (- (f (Suc t) x) * (y x))) X)
   = (sum (\<lambda>x. exp (- f t x * y x) * exp (-(w ( t))*(h ( t) x)*(y x))) X)"
    using splitf by auto
  also have "(sum (\<lambda>x. exp (- f t x * y x) * exp (-(w t)*(h t x)*(y x))) X) / (sum (\<lambda>x. exp (- (f t x) * (y x))) X)
  = (sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) X) * exp (-(w t)*(h t x)*(y x))) X)"
    using sum_divide_distrib by simp
  also have "(sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) X) * exp (-(w t)*(h t x)*(y x))) X)
      = (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) X)"
    using Dalt by simp
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) X
  = sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>X. h t x = y x}
  + sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>X. h t x \<noteq> y x}"
    using Groups_Big.comm_monoid_add_class.sum.union_disjoint finitex s1 s2 
    by (metis (no_types, lifting) finite_Un)
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>X. h t x = y x}
            = sum (\<lambda>x. D t x * exp (-(w t))) {x\<in>X. h t x = y x}"
    by (smt add.inverse_inverse empty_iff h.elims insert_iff mem_Collect_eq mult.left_neutral mult_cancel_left2 mult_minus1_right mult_minus_right sum.cong ytwoclass)
  also have "sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) {x\<in>X. h t x \<noteq> y x}
            = sum (\<lambda>x. D t x * exp (w t)) {x\<in>X. h t x \<noteq> y x}"
    using ctov2 by (simp add: Groups.mult_ac(1))
  also have "(\<Sum>x | x \<in> X \<and> h t x = y x. D t x * exp (- w t)) +
  (\<Sum>x | x \<in> X \<and> h t x \<noteq> y x. D t x * exp (w t))
        = (\<Sum>x | x \<in> X \<and> h t x = y x. D t x) * exp (- w t) +
  (\<Sum>x | x \<in> X \<and> h t x \<noteq> y x. D t x) * exp (w t)"
    by (simp add: sum_distrib_right)
  also have "(\<Sum>x | x \<in> X \<and> h t x \<noteq> y x. D t x) = \<epsilon> t" by auto
  also have "(\<Sum>x | x \<in> X \<and> h t x = y x. D t x) = 1 - \<epsilon> t"
  proof -
    have "(\<Sum>x | x \<in> X \<and> h t x = y x. D t x) + (\<Sum>x | x \<in> X \<and> h t x \<noteq> y x. D t x)
        = sum (D t) X"
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
  also have s19:"(1 - \<epsilon> t)* (sqrt (\<epsilon> t)/ sqrt(1 - \<epsilon> t)) = sqrt (\<epsilon> t)*sqrt(1 - \<epsilon> t)"
    using assms(1,3) by (smt less_divide_eq_1_pos mult.commute real_div_sqrt times_divide_eq_left)
  also have "sqrt (\<epsilon> t) * sqrt (1 - \<epsilon> t) + sqrt (1 - \<epsilon> t) * sqrt (\<epsilon> t)
            = 2 * sqrt((1 - \<epsilon> t) * \<epsilon> t)"
    by (simp add: real_sqrt_mult_distrib2) 
  also have s20:"2*sqrt((1 - \<epsilon> t) * \<epsilon> t) \<le> 2*sqrt((1/2-\<gamma>)*(1-(1/2-\<gamma>)))"
    proof -
      have "((1 - \<epsilon> t) * \<epsilon> t) \<le> ((1/2-\<gamma>)*(1-(1/2-\<gamma>)))"
        using assms(1,3) amono s3 by (smt mult.commute)
      then show ?thesis by auto
    qed
  also have "2 * sqrt ((1 / 2 - \<gamma>) * (1 - (1 / 2 - \<gamma>))) = 2 * sqrt(1/4-\<gamma>^2)"
       by (simp add: algebra_simps power2_eq_square)
      
  also have "2 * sqrt(1/4-\<gamma>^2) = sqrt(4*(1/4-\<gamma>^2))"
    using real_sqrt_four real_sqrt_mult_distrib2 by presburger 
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

definition defloss: "loss t = 1/(card X) *(sum (\<lambda>x. (if (f t x * (y x)) > 0 then 0 else 1)) X)"


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
  have help3: "\<forall>n. sum (\<lambda>x. if 0 < f T x * y x then 0 else 1) X \<le> sum (\<lambda>x. exp (- (f T x * y x))) X"
    by (simp add: sum_mono)
  then have s3: "loss T \<le> Z T" 
    by (simp add: defloss dez divide_right_mono)
  from s2 s3 show ?thesis by auto
qed

