theory Boosting
  imports Complex_Main
begin

fun ind :: "bool \<Rightarrow> real" where
 "ind True = 1"
|"ind False = -1"


fun recsum :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "recsum 0 f = f 0"
| "recsum (Suc n) f = (recsum n f) + f (Suc n)"


lemma recsum_distrib: "(recsum n f) / (recsum m g) = recsum n (\<lambda>x. (f x) / (recsum m g))"
  apply (induction n)
  by (auto simp: add_divide_distrib)

lemma recsum_gt: "\<forall>k. f k > 0 \<Longrightarrow> recsum n f > 0"
  apply (induction n)
  apply auto
  by (meson less_add_same_cancel1 less_imp_le less_le_trans)

lemma recsum_gt2: "\<forall>k. f k > 0 \<Longrightarrow> recsum n (\<lambda>x. (if a x then f x else 0)) \<ge> 0"
  apply (induction n)
  by (auto simp: less_eq_real_def pos_add_strict)

lemma rech1:"a \<ge> m \<Longrightarrow> recsum m (\<lambda>x. (if x\<le>a then f x else 1)) = recsum m f"
  apply (induction m)
  by auto

lemma recsum_hb: "recsum m (\<lambda>x. (if x\<le>m then f x else 1)) = recsum m f"
  by (simp add: rech1)

lemma recsplit: "recsum m f = recsum m (\<lambda>x. (if a x then f x else 0)) + recsum m (\<lambda>x. (if \<not>(a x) then f x else 0))"
  apply (induction m)
  by auto

lemma recdistmult: "recsum m (\<lambda>x. (if a x then f x * b else 0)) = recsum m (\<lambda>x. (if a x then f x else 0)) * b"
  apply (induction m)
  by (auto simp: distrib_left mult.commute)
 

function \<epsilon> :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real"
and w :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real"
and f :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
and D :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
    "\<epsilon> t h y m = recsum m (\<lambda>x. (if \<not>((ind(h t x)) * (ind(y x)) = 1) then (D x t h y m) else 0))"
  | "w (Suc t) h y m = (ln (1/(\<epsilon> (Suc t) h y m)-1))/2"
  | "w 0 h y m = 0"
  | "f t h y m x = recsum t (\<lambda>p. (if p \<le> t then (\<lambda>pp. (w pp h y m)* (ind(h pp x))) p else 1))"
  | "D i (Suc t) h y m = (exp (- ((f t h y m i)) * (ind (y i)))) / (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"
  | "D i 0 h y m = 1/(Suc m)"
  by pat_completeness auto
termination
   apply (relation "measure (\<lambda>x. case x of (Inl(Inl (t,h,y,m))) \<Rightarrow> 4*t+1
                                           | (Inl(Inr (t,h,y,m))) \<Rightarrow> 4*t+2
                                           | (Inr(Inl (t,h,y,m,x))) \<Rightarrow> 4*t+3
                                           | (Inr(Inr (i,(Suc t),h,y,m))) \<Rightarrow> 4*t+4
                                            | _ \<Rightarrow> 0   ) ")
  apply auto
  apply (simp split: nat.split)
  done




lemma fixes hx :: bool and y :: bool 
  shows inds: "ind (hx \<noteq> y) \<le> exp (- (ind hx) * (ind y))"
  apply (cases hx)
  apply (case_tac[!] y)
  apply auto
  apply (smt exp_ge_zero)
  apply (smt exp_ge_zero)
  done

lemma help1:"(b::real) > 0 \<Longrightarrow> a / b \<le> c \<Longrightarrow> a \<le> b * c"
  by (smt mult.commute pos_less_divide_eq)

lemma help2: "\<forall>n. Z n \<ge> 0 \<Longrightarrow> \<forall>n. Z (Suc n) \<le> exp x * Z n \<Longrightarrow> Z 0 = 1 \<Longrightarrow> Z T \<le> exp (real (x*T))"
proof (induction T)
  case 0
then show ?case by auto
next
  case c1:(Suc T)
  then have s1:"Z (Suc T) \<le> exp (real x) * Z T" by auto
  from c1 have "exp (real x) * Z T \<le> exp (x *(T + 1))"
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 exp_ge_zero mult_Suc_right mult_exp_exp mult_left_mono of_nat_add)  
  from this s1 show ?case by auto
qed



definition defloss: "loss t y h m = 1/(real (Suc m)) *(recsum m (\<lambda>x. (if (f t h y m x * (ind (y x))) > 0 then 0 else 1)))"



lemma dione: "recsum m (\<lambda>q. D q t h y m) = 1"
proof(cases t)
  case c1: 0
  have "\<forall>b. recsum m (\<lambda>q. 1 * b) = recsum m (\<lambda>q. 1) * b"
    apply (induction m)
    apply simp
    by (metis distrib_left mult.commute recsum.simps(2))
  then have s1: "\<forall>n. recsum m (\<lambda>q. 1 * 1 / n) = recsum m (\<lambda>q. 1) * 1 / n"
    by (metis times_divide_eq_right) 
  have s2: "\<forall>n. recsum m (\<lambda>q. 1) * 1 / n = (Suc m) * 1 / n"
    apply (induction m)
    by auto
  from s1 s2 have "recsum m (\<lambda>q. 1 / (Suc m)) = (Suc m) /(Suc m)"
    by (metis mult.right_neutral) 
  from this c1 show ?thesis by simp
next
  case c1: (Suc u)
  from c1 have "recsum m (\<lambda>q. D q t h y m) = recsum m (\<lambda>q. (exp (- ((f u h y m q)) * (ind (y q)))) / (recsum m (\<lambda>x. exp (- ((f u h y m x)) * (ind (y x))))))"
    by auto
  also have "recsum m (\<lambda>q. (exp (- ((f u h y m q)) * (ind (y q)))) / (recsum m (\<lambda>x. exp (- ((f u h y m x)) * (ind (y x))))))
           = recsum m (\<lambda>q. (exp (- ((f u h y m q)) * (ind (y q))))) / (recsum m (\<lambda>x. exp (- ((f u h y m x)) * (ind (y x)))))"
    using recsum_distrib by presburger
  also have "recsum m (\<lambda>q. (exp (- ((f u h y m q)) * (ind (y q))))) / (recsum m (\<lambda>x. exp (- ((f u h y m x)) * (ind (y x))))) = 1"
  proof -
    have "recsum m (\<lambda>n. exp (- f u h y m n * ind (y n))) \<noteq> 0"
      by (metis (no_types) exp_gt_zero order_less_irrefl recsum_gt)
    then show ?thesis
      by auto
  qed  
  finally show ?thesis by auto
qed

lemma dgtz: "D i t h y m > 0"
proof (cases t)
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then show ?thesis by (simp add: recsum_gt)
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


definition dez:"Z t y h m = 1/(real (Suc m)) * (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"


lemma ninds:"(if (f t h y m x * (ind (y x))) > 0 then 0 else 1) \<le> exp (- ((f t h y m x)) * (ind (y x)))" by auto



lemma
  assumes "\<forall>t. \<epsilon> t h y m \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t h y m \<noteq> 0" and "\<gamma> > 0"
  shows main101: "(Z (Suc t) y h m) / (Z t y h m) \<le> exp(-2*\<gamma>^2)"
proof -
  have s11: "recsum m (\<lambda>x. exp (- (f t h y n x * ind (y x)))) > 0"
    by (simp add: recsum_gt)
  have s10: "(Z (Suc t) y h m) / (Z t y h m) = (recsum m (\<lambda>x. exp (- ((f (Suc t) h y m x)) * (ind (y x))))) / (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"
    by (auto simp: dez assms)
  then have "(Z (Suc t) y h m) / (Z t y h m) = (recsum m (\<lambda>x. exp (- ((f t h y m x) + (w (Suc t) h y m) *(ind (h (Suc t) x))) * (ind (y x))))) / (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"
    by (simp add: rech1)
  then have "(Z (Suc t) y h m) / (Z t y h m) = (recsum m (\<lambda>x. exp (- ((f t h y m x)*(ind (y x)) + ((w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind (y x))))))) / (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"
    by (simp add: algebra_simps)
  then have "(Z (Suc t) y h m) / (Z t y h m) = (recsum m (\<lambda>x. exp (- ((f t h y m x) * (ind (y x)))) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind (y x))))) / (recsum m (\<lambda>x. exp (- ((f t h y m x)) * (ind (y x)))))"
    by (simp add: mult_exp_exp)
  then have "(Z (Suc t) y h m) / (Z t y h m) = recsum m (\<lambda>x. exp (- ((f t h y m x) * (ind (y x)))) / (recsum m (\<lambda>xx. exp (- ((f t h y m xx)) * (ind (y xx))))) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind (y x))))"
    using recsum_distrib by auto
  then have "(Z (Suc t) y h m) / (Z t y h m) = recsum m (\<lambda>x. (D x (Suc t) h y m) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind(y x))))"
    by auto
  then have s13: "(Z (Suc t) y h m) / (Z t y h m) = recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (\<lambda>x.(D x (Suc t) h y m) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind(y x))))x else 0))
                                             + recsum m (\<lambda>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (\<lambda>x.(D x (Suc t) h y m) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind(y x))))x else 0))"
    using recsplit by simp 
  have h1:"\<forall>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind(y x))) else 0) =
        (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp (- (w (Suc t) h y m)) else 0)"
    by auto
  have h2: "(\<not>((ind(h (Suc t) x)) * (ind(y x)) = 1)) = ((ind(h (Suc t) x)) * (ind(y x)) = -1)"
    by (metis (full_types) add.inverse_inverse ind.simps(1) ind.simps(2) mult.right_neutral mult_minus_right one_neq_neg_one)
  have h3:"\<forall>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp (- (w (Suc t) h y m) * (ind(h (Suc t) x)) * (ind(y x))) else 0) =
        (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp ((w (Suc t) h y m)) else 0)"
  proof -
  { fix nn :: nat and nna :: nat
    have "h (Suc t) nna \<longrightarrow> ind (h (Suc t) nna) = 1"
      by (metis ind.simps(1))
    moreover
    { assume "ind (h (Suc t) nna) = 1"
    then have "y nna \<longrightarrow> ind (y nna) * ind (h (Suc t) nna) = 1"
      by auto
      then have "\<not> y nna \<and> \<not> h (Suc t) nna \<or> D nna (Suc t) h y m * exp (ind (y nna) * - (w (Suc t) h y m * ind (h (Suc t) nna))) = exp (w (Suc t) h y m) * D nna (Suc t) h y m \<or> ind (y nna) * ind (h (Suc t) nna) = 1"
        by force }
      ultimately have "\<not> y nna \<and> \<not> h (Suc t) nna \<or> D nna (Suc t) h y m * exp (ind (y nna) * - (w (Suc t) h y m * ind (h (Suc t) nna))) = exp (w (Suc t) h y m) * D nna (Suc t) h y m \<or> ind (y nna) * ind (h (Suc t) nna) = 1"
        using mult.left_neutral by fastforce
      moreover
      { assume "\<not> y nna \<and> \<not> h (Suc t) nna"
        then have "ind (y nna) * ind (h (Suc t) nna) = 1"
          by simp }
      ultimately have "ind (h (Suc t) nn) * ind (y nn) = 1 \<or> ind (h (Suc t) nna) * ind (y nna) = 1 \<or> D nna (Suc t) h y m * exp (- w (Suc t) h y m * ind (h (Suc t) nna) * ind (y nna)) = D nna (Suc t) h y m * exp (w (Suc t) h y m) \<and> ind (h (Suc t) nn) * ind (y nn) \<noteq> 1 \<and> ind (h (Suc t) nna) * ind (y nna) \<noteq> 1"
        by (metis (no_types) mult.commute mult_minus_left) }
      then show ?thesis
        by (metis (no_types))
    qed 

  from s13 h3 h1 have "(Z (Suc t) y h m) / (Z t y h m) = recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp (- (w (Suc t) h y m)) else 0))
                                             + recsum m (\<lambda>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) * exp ((w (Suc t) h y m)) else 0))"
    by auto
  then have "(Z (Suc t) y h m) / (Z t y h m) = recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)) * exp (- (w (Suc t) h y m))
                                             + recsum m (\<lambda>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)) * exp ((w (Suc t) h y m))"
    using recdistmult by auto
  then have s14: "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * exp ((w (Suc t) h y m))
                                             + recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)) * exp (-(w (Suc t) h y m))"
    by auto
  have "1 - \<epsilon> (Suc t) h y m = recsum m (\<lambda>q. D q (Suc t) h y m) - (recsum m (\<lambda>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)))"
    using dione \<epsilon>.simps by presburger
  also have "recsum m (\<lambda>q. D q (Suc t) h y m) = (recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)))
                                              + (recsum m (\<lambda>x. (if \<not>((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)))"
    using recsplit by simp 
  finally have s15: "1 - \<epsilon> (Suc t) h y m = (recsum m (\<lambda>x. (if ((ind(h (Suc t) x)) * (ind(y x)) = 1) then (D x (Suc t) h y m) else 0)))" by auto
  from this s14 have "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * exp ( (w (Suc t) h y m))
                                                + (1 - \<epsilon> (Suc t) h y m) * exp (-(w (Suc t) h y m))"
    by auto
  then have "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * exp (((ln (1/(\<epsilon> (Suc t) h y m)-1))/2))
                                                + (1 - \<epsilon> (Suc t) h y m) * exp (-((ln (1/(\<epsilon> (Suc t) h y m)-1))/2))"
    by auto
  also have "exp (-((ln (1/(\<epsilon> (Suc t) h y m)-1))/2)) = 1/(exp (((ln (1/(\<epsilon> (Suc t) h y m)-1))/2)))"
    by (smt exp_diff exp_zero)
  finally have s17: "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * exp (((ln (1/(\<epsilon> (Suc t) h y m)-1))/2))
                                                + (1 - \<epsilon> (Suc t) h y m) * 1/(exp (((ln (1/(\<epsilon> (Suc t) h y m)-1))/2)))"
      by auto
  from assms have s16: "\<epsilon> (Suc t) h y m < 1"
    by (smt le_divide_eq_1_pos)
  have s18: "\<epsilon> (Suc t) h y m \<ge> 0"
    using recsum_gt2 dgtz \<epsilon>.simps by presburger
  from s16 this assms(2) have "(1/(\<epsilon> (Suc t) h y m))-1 > 0"
    by (simp add: less_eq_real_def)
  then have "exp (((ln (1/(\<epsilon> (Suc t) h y m)-1)) * 1/2)) = sqrt (1/(\<epsilon> (Suc t) h y m)-1)"
    by (metis exp_ln ln_sqrt mult.right_neutral real_sqrt_gt_0_iff)
   
  from this s17 have "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * sqrt(1/(\<epsilon> (Suc t) h y m)-1)
                                                + (1 - \<epsilon> (Suc t) h y m) * 1/(sqrt(1/(\<epsilon> (Suc t) h y m)-1))"
    by auto
  also have "sqrt(1/(\<epsilon> (Suc t) h y m)-1) = sqrt(1/(\<epsilon> (Suc t) h y m)-(\<epsilon> (Suc t) h y m)/(\<epsilon> (Suc t) h y m))"
    using assms(2) by auto 
  also have "sqrt(1/(\<epsilon> (Suc t) h y m)-(\<epsilon> (Suc t) h y m)/(\<epsilon> (Suc t) h y m)) = sqrt((1 - \<epsilon> (Suc t) h y m)/\<epsilon> (Suc t) h y m)"
    by (simp add: diff_divide_distrib)
  finally have "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * sqrt((1 - \<epsilon> (Suc t) h y m)/\<epsilon> (Suc t) h y m)
                                                + (1 - \<epsilon> (Suc t) h y m) * 1/(sqrt((1 - \<epsilon> (Suc t) h y m)/\<epsilon> (Suc t) h y m))" by auto
  then have "(Z (Suc t) y h m) / (Z t y h m) = \<epsilon> (Suc t) h y m * sqrt(1 - \<epsilon> (Suc t) h y m)/sqrt(\<epsilon> (Suc t) h y m)
                                                + (1 - \<epsilon> (Suc t) h y m) * sqrt(\<epsilon> (Suc t) h y m) / sqrt((1 - \<epsilon> (Suc t) h y m))"
    by (simp add: real_sqrt_divide)
  also have "\<epsilon> (Suc t) h y m * sqrt(1 - \<epsilon> (Suc t) h y m)/sqrt(\<epsilon> (Suc t) h y m) =  sqrt(1 - \<epsilon> (Suc t) h y m) * sqrt(\<epsilon> (Suc t) h y m)"
    by (metis mult.commute real_div_sqrt s18 times_divide_eq_left)
  finally have s19:"(Z (Suc t) y h m) / (Z t y h m) =  sqrt(1 - \<epsilon> (Suc t) h y m) * sqrt(\<epsilon> (Suc t) h y m)
                                                +  sqrt(\<epsilon> (Suc t) h y m) * sqrt((1 - \<epsilon> (Suc t) h y m))"
    by (metis add.commute diff_add_cancel less_add_same_cancel1 less_eq_real_def mult.commute real_div_sqrt s16 times_divide_eq_right)
  have s20:"((1 - \<epsilon> (Suc t) h y m) * \<epsilon> (Suc t) h y m) \<le> ((1/2-\<gamma>)*(1-(1/2-\<gamma>)))"
    using assms amono s18  by (metis diff_add_cancel less_add_same_cancel1 less_eq_real_def mult.commute) 
  from s19 have "(Z (Suc t) y h m) / (Z t y h m) =  2 * sqrt((1 - \<epsilon> (Suc t) h y m) * \<epsilon> (Suc t) h y m)"
    by (simp add: real_sqrt_mult_distrib2)
  also have "2 * sqrt((1 - \<epsilon> (Suc t) h y m) * \<epsilon> (Suc t) h y m) \<le> 2 * sqrt((1/2-\<gamma>)*(1/2+\<gamma>))" using s20 by auto
  also have "2 * sqrt((1/2-\<gamma>)*(1/2+\<gamma>)) = 2 * sqrt(1/4-\<gamma>^2)"
      proof -
          have "2 * sqrt (1 / 2 * (1 / 2) - \<gamma> * \<gamma>) = 2 * sqrt (1 / 4 - \<gamma> * \<gamma>)"
      by force
        then show ?thesis
          by (metis linordered_field_class.sign_simps(24) semiring_normalization_rules(29) square_diff_square_factored)
      qed
  also have "2 * sqrt(1/4-\<gamma>^2) = sqrt(4*(1/4-\<gamma>^2))"
    using real_sqrt_four real_sqrt_mult_distrib2 by presburger 
  also have "sqrt(4*(1/4-\<gamma>^2)) = sqrt(1-4*\<gamma>^2)" by auto
  finally have "(Z (Suc t) y h m) / (Z t y h m) \<le> sqrt(1-4*\<gamma>^2)" by auto
  also have "1-4*\<gamma>^2 \<le> exp(-4*\<gamma>^2)"
    by (metis (no_types) add_uminus_conv_diff exp_ge_add_one_self mult_minus_left)
  finally have "(Z (Suc t) y h m) / (Z t y h m) \<le> sqrt(exp(-4*\<gamma>^2))" by auto
  then have "(Z (Suc t) y h m) / (Z t y h m) \<le> exp(-4*\<gamma>^2/2)"
    by (metis exp_gt_zero exp_ln ln_exp ln_sqrt real_sqrt_gt_0_iff)
  then show ?thesis by auto
qed


lemma
  assumes "\<forall>t. \<epsilon> t h y m \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t h y m \<noteq> 0" and "\<gamma> > 0"
  shows main102: "loss T y h m \<le> exp (-2*\<gamma>^2*T)"
proof -
    have s1: "\<forall>k. Z k y h m > 0"
    apply (induction m)
    by (auto simp: dez add_pos_pos recsum_gt)
  have s2: "Z T y h m \<le> exp(-2*\<gamma>^2*T)"
  proof (induction T)
    case 0
    have "recsum m (\<lambda>x. 1) \<le> 1 + real m"
      apply (induction m)
      by auto
    then show ?case by (simp add: dez)
    next
      case c1:(Suc T)
    from main101 s1 have s1:"Z (Suc T) y h m \<le> exp (-2*\<gamma>^2) * Z T y h m"
      by (metis assms(1) assms(2) assms(3) help1 mult.commute) 
    from c1 have "exp (-2*\<gamma>^2) * Z T y h m \<le> exp (-2*\<gamma>^2 *T) * exp (-2*\<gamma>^2)" by auto
    from this s1 show ?case
      by (smt Groups.mult_ac(2) exp_of_nat2_mult power.simps(2)) 
  qed
  have help3: "\<forall>n. recsum m (\<lambda>x. if 0 < f T h y n x * ind (y x) then 0 else 1) \<le> recsum m (\<lambda>x. exp (- (f T h y n x * ind (y x))))"
  apply (induction m)
    by (auto simp:add_mono_thms_linordered_semiring(1))
  then have s3: "loss T y h m \<le> Z T y h m"
    by (simp add: defloss dez divide_right_mono)
  from s2 s3 show ?thesis by auto
qed

