theory Boosting
  imports Complex_Main LinearPredictor VCDim
begin


text {* Abstract
These theories are a result of my work for the Specification and Verification Practical course
in WS19. They mostly formalize theorems from the book "Understanding Machine Learning" by 
Shai Shalev-Shwartz and Shai Ben-David, published 2014. The main method analyzed is Boosting
(concretely AdaBoost) and upper bounds for both Training and Validation Errors are proven based
on assumptions about the quality of the underlying weak learner (e.g. decision stumps). Claims about
the Validation Error or Prediction Error require a quantification of the model complexity in the
form of the VC-Dimension. As a result most of the work revolves around binding the VC-Dimension of
Boosting and deducing strong statements from that measure. The auxiliary concepts explored in this
work are the VC-Dimension, Uniform Convergence, PAC-Learnability, Linear Predictors and Decision Stumps.
In the context of Linear Predictors in Isabelle, a specific implementation of standard vectors is
given as well.*}



text {*File Overview: Chapters | Definitions, Lemmas, Theorems
LearningTheory:       2,3,4      Equations 3.1, 2.2 (Errors), Definitions 3.1, 4.1, 4.3, Lemma 4.2
FiniteHypClasses:     2          Corollary 2.3/3.2 (equivalent)
VCDim:                4          Definitions 6.2 6.3 6.5 6.9, Lemma 6.10 (Sauer's), Theorem 6.7
                                 (The Fundamental Theorem of Statistical Learning), 6.11 (sorry'd)
LinearPredictor:      9          Theorem 9.2
Boosting:             10         Theorem 10.2, Lemma 10.3
*}

text {*Test:
@{thm mapify_alt} @{term learning_basics.uniform_convergence}}
 *}

text {* Other files:
RpowD: In this file a vector type is defined, that is used for the linear predictor. The main goal
       of defining this type was making the vector size independent of the type, but this is not
       absolutely necessary and the type could be replaced by something more standard. Note, that
       it contains a pseudo scalar/inner product (minner) that is defined without instantiating
       metric or normed space.
DecisionStump: This document contains an attempt at providing an upper bound for the error of
               decision stumps. Since there is no non-trivial (better than 0.5) upper bound without
               assumptions, I tried to specify the conditions necessary for such a bound. I proof
               that the condition I came up with is sufficient for the bound provided but it turns
               out, it is not a necessary condition for a bound <0.5 and as such not optimal.
               However, such a bound would not be very powerful so this side-project was stopped.
Theorem611: This document contains a collection of (mostly failed) attempts at gathering subproofs
            and important lemmata for theorem 6.11. It may help proving the theorem in the future
            and serves no other purpose.
Pi_pmf: This was imported by Max Haslbeck to define iid samples and otherwise left untouched by me.
*}

text{* General comments
Big parts of LearningTheory and FiniteHypClasses are by Max Haslbeck and only slightly adapted.
In chapter 2 of the book, the ground truth gets introduced in terms of a labeling function. This
assumption gets loosened in chapter 3 by including the label of a data point in the data generating
distribution. I decided to use that notation throughout to make the statements more general. The
definition of PAC-Learning however is not agnostic but based on the realizability assumption, which
creates some minor differences to the book.
Locales are used mostly to fix hypothesis classes and defining input and output sets. Note, that
in VCDim I assumed the input set X to be infinite. This was done to allow the definition of the
growth function to be as in the book. (with a free parameter describing input set size) Maybe it's
possible to lift this constraint by changing the definitions accordingly, however if X was finite,
H would also be finite and PAC-learnable by Corollary 2.3.
There is one critical part of the theory left unproven, namely theorem 6.11. It is very important,
as it provides the bridge between combinatorics and probability theory. Because of limited time,
the proof for this theorem was ommited and could be added at a later time.
Error terms:
In machine learning, typically two different errors are measured when training a model. The training
error is the error achieved by the model on the data used for training while the validation error
is measured on a seperate data set that is retrieved from the same source. This is done to approximate
the error that can be expected when using the model to predict on new data from the same source
distribution. In the book and in this work this error will therefore be referred to as prediction
error. We can derive bounds for this error that do not require an actual validation set using
learning theory.
 *}

text {* Main results and interpretation
The main result of this work is the last lemma in Boosting as it effectively presents a bound on
the prediction error of Boosting that does not rely on the realizability assumption. It combines
Theorem 10.2, Lemma 10.3 and bounds from VCDim. There is one strong assumption though and that
is the assumed error of the weak learner/base class (0.5-\<gamma>). The quality of the bound given by
Theorem 10.2 is highly dependent on the quality of the weak learner in terms of a high \<gamma>. Therefore
the other part, which bounds the difference between Training and Prediction error, could be
considered stronger, as it does not require such strong assumptions.
 *}



section "Boosting"

lemma only_one: "a\<in>A \<Longrightarrow> \<forall>b\<in>A. b = a \<Longrightarrow> card A = 1"
  by (metis (no_types, hide_lams) One_nat_def card.empty card_Suc_eq empty_iff equalityI insert_iff subsetI) 

fun btor :: "bool \<Rightarrow> real" where
"btor x = (if x then 1 else -1)"

locale BOOST =
  fixes S :: "nat \<Rightarrow> 'a \<times> bool"
    and m :: nat
    and X :: "'a set"
    and oh :: "(nat \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  assumes 
    ohtwoclass: "\<forall>Ds x. oh Ds x \<in> {-1,1}"
    and mgtz: "0<m"
    and samdef:"\<forall>i<m. S i \<in> (X\<times>{True, False})"
begin



abbreviation "y \<equiv> btor \<circ> snd \<circ> S"

abbreviation "C \<equiv> {0..<m}"

lemma nonemptyx: "C \<noteq> {}" using mgtz by auto

lemma finitex: "finite C" by auto

lemma ytwoclass: "\<forall>i. y i \<in> {-1::real, 1}" by auto


fun ih :: "nat \<Rightarrow> 'a \<Rightarrow> real"
and h :: "nat \<Rightarrow> nat \<Rightarrow> real"
and \<epsilon> :: "nat \<Rightarrow> real"
and w :: "nat \<Rightarrow> real"
and D :: "nat \<Rightarrow> nat \<Rightarrow> real" where
    "ih t x = oh (\<lambda>i. D t i) x"
  | "h t i = oh (\<lambda>x. D t x) (fst (S i))"
  | "\<epsilon> t = sum (\<lambda>x. D t x) {i\<in>{0..<m}. h t i \<noteq> btor (snd (S i))}"
  | "w t = (ln (1/(\<epsilon> t)-1))/2"
  | "D (Suc t) i = (D t i * exp (-(w t)*(h t i)*(btor (snd (S i))))) / (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)* y x)) {0..<m})"
  | "D 0 i = 1/m"


lemma ctov: "h t x = y x \<Longrightarrow> h t x * y x = 1" and ctov2: "h t x \<noteq> y x \<Longrightarrow> h t x * y x = -1"
  apply (smt empty_iff insert_iff mult_cancel_left2 mult_minus_right ytwoclass)
  by (metis empty_iff h.simps insert_iff mult.commute mult.left_neutral ohtwoclass ytwoclass)



fun f :: "nat \<Rightarrow> nat \<Rightarrow> real" where
"f T i = sum (\<lambda>t. (w t) * (h t i)) {0..<T}"

fun f' :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
"f' T x = sum (\<lambda>t. (w t) * (ih t x)) {0..<T}"

lemma "f T i = f' T (fst (S i))" by auto

lemma aux34: "movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0))
        = (\<lambda>t. (if t < k then w t else 0))" using vec_lambda_inverse lt_valid[of k w]
    by auto

lemma aux35: "movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then ih t i else 0))
        = (\<lambda>t. (if t < k then ih t i else 0))" using vec_lambda_inverse lt_valid[of k "(\<lambda>t. ih t i)"]
    by auto

definition "hyp k x = (f' k x > 0)"

lemma hyp_alt: "hyp k (fst (S i)) = (f k i > 0)"
  by (metis (mono_tags, lifting) BOOST.h.simps BOOST.hyp_def BOOST.ih.simps BOOST_axioms f'.simps f.simps sum.cong) 

lemma convert_f: "(\<lambda>i. f' k i > 0)  = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then w t else 0))) 
                                                 (vec_lambda (\<lambda>t. (if t<k then ih t i else 0)))))"
proof -
  from aux34 have "\<forall>i. {q. movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) q \<noteq> 0 
        \<and> movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then ih t i else 0))) q \<noteq> 0} \<subseteq> {..<k}"
    by auto
  then have "\<forall>i. minner (movec.vec_lambda (\<lambda>t. if t < k then w t else 0))
               (vec_lambda (\<lambda>t. (if t<k then ih t i else 0)))
             = (\<Sum>ia\<in>{..<k}.
                 movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) ia \<bullet>
                 movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then ih t i else 0))) ia)"
    using minner_alt by auto
  moreover have "\<forall>i. (\<Sum>ia\<in>{..<k}.
                 movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then w t else 0)) ia \<bullet>
                 movec.vec_nth (vec_lambda (\<lambda>t. (if t<k then ih t i else 0))) ia) = f' k i"
    unfolding aux34 aux35 
    apply(induction k)
    by auto
  ultimately show ?thesis unfolding linear_predictor_def by auto
qed


lemma splitf: "exp (- f (Suc t) i * y i) = ((exp (- f t i * y i)) * exp (-(w (t))*(h (t) i)*(y i)))"
proof -
  have "f (Suc t) i * - y i = - f t i * y i + - w (t) * h (t) i * y i"    
    by (simp add: distrib_right)
  then have "- f (Suc t) i * y i = - f t i * y i + - w (t) * h (t) i * y i"
    by linarith 
  then show ?thesis using exp_add by metis
qed

lemma Dalt: "D t i = (exp (- ((f t i)) * (y i))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) {0..<m})"
proof (induction t arbitrary: i)
  case 0
  show ?case by (simp add: sum_distrib_left)
next
  case c1: (Suc t)
  then have "D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>{0..<m}. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ (sum (\<lambda>x. (exp (- f t x * y x) / (\<Sum>xx\<in>{0..<m}. exp (- f t xx * y xx))) * exp (-(w t)*(h t x)*(y x))) {0..<m})"
    by auto
  then have s0:"D (Suc t) i
= ((exp (- f t i * y i) / (\<Sum>x\<in>C. exp (- f t x * y x))) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) C)/ (\<Sum>x\<in>C. exp (- f t x * y x)))"
    by (simp add: sum_divide_distrib)
     have "(\<Sum>x\<in>C. exp (- f t x * y x)) > 0"
       by (meson exp_gt_zero finite_atLeastLessThan nonemptyx sum_pos)
     from s0 this have s1:"D (Suc t) i
= ((exp (- f t i * y i)) * exp (-(w t)*(h t i)*(y i))) 
/ ((sum (\<lambda>x. (exp (- f t x * y x)) * exp (-(w t)*(h t x)*(y x))) C))"
       by simp
     from s1 splitf show ?case by simp
qed


lemma dione: "sum (\<lambda>q. D t q) C = 1"
proof-
  have "sum (\<lambda>q. D t q) C = sum (\<lambda>q. (exp (- ((f t q)) * (y q))) / (sum (\<lambda>x. exp (- ((f t x)) *  (y x))) C)) C"
    using Dalt by presburger
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
  then show ?thesis by (simp add: mgtz)
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
    by (auto simp: dez mgtz)
  also have "(sum (\<lambda>x. exp (- (f (Suc t) x) * (y x))) C)
   = (sum (\<lambda>x. exp (- f t x * y x) * exp (-(w ( t))*(h ( t) x)*(y x))) C)"
    using splitf by auto
  also have "(sum (\<lambda>x. exp (- f t x * y x) * exp (-(w t)*(h t x)*(y x))) C) / (sum (\<lambda>x. exp (- (f t x) * (y x))) C)
  = (sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) C) * exp (-(w t)*(h t x)*(y x))) C)"
    using sum_divide_distrib by simp
  also have "(sum (\<lambda>x. exp (- f t x * y x)/ (sum (\<lambda>x. exp (- (f t x) * (y x))) C) * exp (-(w t)*(h t x)*(y x))) C)
      = (sum (\<lambda>x. D t x * exp (-(w t)*(h t x)*(y x))) C)"
    using Dalt by presburger
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
    then show ?thesis using dione by auto
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

lemma losstotrain: "TrainErr S {0..<m} (hyp t) \<le> loss t" unfolding TrainErr_def defloss
proof -
   have "\<forall>i. (case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) \<le> (if 0 < f t i * y i then 0 else 1)"
  proof
    fix i
    show "(case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) \<le> (if 0 < f t i * y i then 0 else 1)"
    proof(cases "(case S i of (a, b) \<Rightarrow>  hyp t a \<noteq> b)")
      case c1: True
      then have "0 \<ge> f t i * y i"
        by (smt btor.simps case_prod_unfold comp_apply hyp_alt mult_le_0_iff)
      then have "(if 0 < f t i * y i then 0::real else 1) = 1" by auto
      moreover from c1 have "(case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) = 1" by auto
      ultimately show ?thesis by linarith 
    next
      case False
      then have "(case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) = 0"
        by (simp add: case_prod_unfold) 
      then show ?thesis
        by (smt less_eq_real_def)
    qed
  qed
  then have "(\<Sum>i\<in>C. case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) \<le> (\<Sum>x\<in>C. if 0 < f t x * y x then 0 else 1)"
     by (simp add: sum_mono)
  then show "(\<Sum>i\<in>C. case S i of (a, b) \<Rightarrow> if hyp t a \<noteq> b then 1::real else 0) / real (card C) \<le> 1 / real (card C) * (\<Sum>x\<in>C. if 0 < f t x * y x then 0 else 1)"
    by (simp add: divide_right_mono)
qed
    
lemma \<comment> \<open>Theorem 10.2\<close>
  assumes "\<forall>t. \<epsilon> t \<le> 1/2 - \<gamma>" and "\<forall>t. \<epsilon> t \<noteq> 0" and "\<gamma> > 0"
  shows main102: "TrainErr S {0..<m} (hyp T) \<le> exp (-2*\<gamma>^2*T)"
proof -
  have s1: "\<forall>k. Z k > 0"
    using dez finitex nonemptyx mgtz by (simp add: sum_pos)
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
  from s2 s3 have "loss T \<le> exp (-2*\<gamma>^2*T)" by auto
  then show ?thesis using losstotrain[of T] by auto
qed
end

section "VC-Dimension Boosting (Lemma 10.3)"

subsection "Definitions and Interpretations"

locale allboost =
  fixes X :: "'a set"
    and oh :: "(nat \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
    and T :: nat
    and B :: "('a \<Rightarrow> real) set"
assumes infx: "infinite X"
    and ohtwoclass: "\<forall>Ds. oh Ds \<in> B"
    and defonB: "\<forall>h x. h \<in> B \<longrightarrow> h x \<in> {- 1, 1}"
    and nonemptyB: "B \<noteq> {}"
    and Tgtz: "1 < T"
begin

term BOOST.hyp

abbreviation "St \<equiv> {(S,m). (\<forall>i::nat<m. S i \<in> (X\<times>{True, False})) \<and> 0<(m::nat)}"

definition "H t = (\<lambda>(S,m). BOOST.hyp S m oh t) `St"


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
  show  "B \<noteq> {}" "infinite X" using allboost_axioms allboost_def[of X] by auto
qed

interpretation vectors: linpred T
proof
  show "1<T" using Tgtz by auto
qed


definition "WH k = (\<lambda>P. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0)))) ` St"

definition "Agg k = (\<lambda>Q i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))) ` St"



subsection "Splitting H"

lemma aux1: "BOOST S y X oh \<Longrightarrow> BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))"
proof -
  assume a1: "BOOST S y X oh"
  then have "BOOST.hyp S y oh k = (\<lambda>i. 0 < BOOST.f' S y oh k i)" using BOOST.hyp_def by fastforce
  also have "(\<lambda>i. 0 < BOOST.f' S y oh k i) = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))
             (vec_lambda (\<lambda>t. (if t<k then BOOST.ih S y oh t i else 0)))))" using BOOST.convert_f a1 by blast
  finally have s1: "BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then BOOST.ih S y oh t i else 0)))))" by auto
  moreover have s1: "\<And>t i. BOOST.ih S y oh t i = oh (BOOST.D S y oh t) i"
    by (meson BOOST.ih.simps a1)
  then have "\<And> i. (\<lambda>t. (if t<k then BOOST.ih S y oh t i else 0)) = (\<lambda>t. (if t<k then oh (BOOST.D S y oh t) i else 0))"
    by auto 
  then have "(\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then BOOST.ih S y oh t i else 0)))))
       = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))" by auto
  then show "BOOST.hyp S y oh k = (\<lambda>i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S y oh t) i) else 0)))))" using s1
    by (simp add: calculation)
qed
   


lemma aux02: assumes "\<forall>(S,m)\<in>{(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}. BOOST S m X oh"
             shows " H k = (\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0)))))`{(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}"
  apply rule
  apply rule
  defer
proof
  let ?H' = "(\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0)))))`{(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}"
  fix h
  assume "h \<in> H k"
  then obtain S m where o1: "(S,m)\<in> {(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}"
                        "h = (\<lambda>(S,m). BOOST.hyp S m oh k) (S,m)" using H_def by auto
  then have "BOOST S m X oh" using assms by auto
  then have "h = (\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0))))) (S,m)"
    using aux1 o1 by auto
  then show "h \<in> ?H'" using o1 by auto
next
let ?H' = "(\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0)))))`{(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}"
  fix h
  assume "h\<in> ?H'"
  then obtain S m where o1: "(S,m)\<in> {(S,m). (\<forall>i<m. S i \<in> (X\<times>{True, False})) \<and> 0<m}"
          "h = (\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0))))) (S,m)" by auto
  then have "BOOST S m X oh" using assms by auto
  then have "h = (\<lambda>(S,m). BOOST.hyp S m oh k) (S,m)" using aux1 o1 by auto
  then show "h \<in> H k" using o1 H_def by auto
qed


lemma aux01: "(\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0)))))`St
\<subseteq> (\<lambda>(P,Q) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))))`(St\<times>St)"
proof
  fix h
  assume "h \<in> (\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0)))))`St"
  then obtain S m where o1: "(S,m)\<in> St"
          "h = (\<lambda>(S,m) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S m oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S m oh t) i) else 0))))) (S,m)" by auto
  moreover obtain P where o2: "fst P = S" "snd P = m" by auto
  ultimately have "h = (\<lambda>P i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst P) (snd P) oh t) i) else 0))))) P" by auto
  then have "h = (\<lambda>(P,Q) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0))))) (P,P)"
    by auto
  moreover have "(P,P) \<in> (St\<times>St)" using o1(1) o2 by fastforce 
  ultimately show "h \<in> (\<lambda>(P,Q) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))))`(St\<times>St)"
    by (meson image_iff)
qed

lemma aux2: "(\<lambda> i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0))) 
       (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y' oh t) i) else 0)))))
=((\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w S y oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D S' y' oh t) i) else 0)))))"
  by auto

lemma aux3: "(\<lambda>(P,Q) i. (linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0))) 
             (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))))`(St\<times>St)
=(\<lambda>(P,Q).(\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0))))) ` (St\<times>St)"
  using aux2 by simp


lemma aux4: "(\<lambda>(P,Q).(\<lambda>v. linear_predictor (vec_lambda (\<lambda>t. (if t<k then BOOST.w (fst P) (snd P) oh t else 0)))  v)
 \<circ> (\<lambda>i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0))))) ` (St\<times>St)
= {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}" unfolding WH_def Agg_def by auto

lemma aux5: "\<forall>(S,m)\<in>St. BOOST S m X oh" unfolding BOOST_def
  using allboost_axioms ohtwoclass defonB by auto

lemma final4: "H k \<subseteq> {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}"
  using aux4 aux3 aux01 aux02 aux5 by auto

subsection "Restricting H"

definition "Agg_res k C = ((\<lambda>h. restrict_map (mapify h) C) ` (Agg k))"
definition "WH_res k agg = ((\<lambda>h. restrict_map (mapify h) (ran agg)) ` (WH k))"


lemma final3: "(\<lambda>h. restrict_map (mapify h) C) ` {boost. \<exists>w\<in>(WH k). \<exists>a\<in>(Agg k). boost = w \<circ> a}  \<subseteq>
      {map. \<exists>a\<in>Agg_res k C. \<exists>w\<in>WH_res k a. map = w \<circ>\<^sub>m a}"
proof safe
  fix w a
  assume "w \<in> WH k" "a \<in> Agg k"
  moreover have "mapify (w\<circ>a) = (mapify w) \<circ>\<^sub>m (mapify a)" unfolding mapify_alt map_comp_def by auto
  moreover have "((mapify w) \<circ>\<^sub>m (mapify a)) |` C = (mapify w) \<circ>\<^sub>m ((mapify a) |` C)"
    unfolding restrict_map_def map_comp_def by auto
  moreover have "(mapify w) \<circ>\<^sub>m ((mapify a) |` C) = ((mapify w)|` ran ((mapify a) |` C)) \<circ>\<^sub>m ((mapify a) |` C)"
    unfolding restrict_map_def map_comp_def ran_def
  proof -
    { fix aa :: 'a
      have ff1: "\<forall>aa. (\<exists>ab. (ab \<in> C \<longrightarrow> mapify a ab = Some (a aa)) \<and> (ab \<notin> C \<longrightarrow> None = Some (a aa))) \<or> aa \<notin> C"
        by (metis mapify_def)
      have "a aa \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} \<longrightarrow> (if a aa \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w (a aa) else None) = Some (w (a aa))"
        by (simp add: mapify_def)
      moreover
      { assume "(if a aa \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w (a aa) else None) = Some (w (a aa))"
        then have "aa \<in> C \<longrightarrow> (case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> w) x) = (case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w m else None)"
          by simp }
      ultimately have "aa \<in> C \<longrightarrow> (case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> w) x) = (case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w m else None)"
        using ff1 by blast
      then have "(case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> w) x) = (case if aa \<in> C then Some (a aa) else None of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w m else None)"
        by force
      then have "(case if aa \<in> C then mapify a aa else None of None \<Rightarrow> None | Some x \<Rightarrow> mapify w x) = (case if aa \<in> C then mapify a aa else None of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> {m. \<exists>aa. (aa \<in> C \<longrightarrow> mapify a aa = Some m) \<and> (aa \<notin> C \<longrightarrow> None = Some m)} then mapify w m else None)"
        by (metis (no_types) mapify_alt mapify_def) }
    then show "(\<lambda>aa. case if aa \<in> C then mapify a aa else None of None \<Rightarrow> None | Some x \<Rightarrow> mapify w x) = (\<lambda>aa. case if aa \<in> C then mapify a aa else None of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> {m. \<exists>aa. (if aa \<in> C then mapify a aa else None) = Some m} then mapify w m else None)"
      by presburger
  qed
  ultimately show "\<exists>aa\<in>Agg_res k C. \<exists>wa\<in>WH_res k aa. mapify (w \<circ> a) |` C = wa \<circ>\<^sub>m aa"
    unfolding Agg_res_def WH_res_def by auto
qed

lemma final5: "restrictH outer.H_map C {True, False} \<subseteq> {map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a}"
proof -
  have "restrictH outer.H_map C {True, False} = (\<lambda>h. restrict_map (mapify h) C) ` H T"
    using outer.restrictH_map_conv by auto
  also have "... \<subseteq> (\<lambda>h. mapify h |` C) ` {boost. \<exists>w\<in>WH T. \<exists>a\<in>Agg T. boost = w \<circ> a}" using image_mono final4[of T] by auto
  finally show ?thesis using final3[of C T] unfolding Agg_res_def WH_res_def by auto
qed

subsection "Bounding WH_res"

    
lemma WH_subset: "WH k \<subseteq> all_linear(myroom k)"
proof -
  have "\<forall>S m. (movec.vec_lambda (\<lambda>t. if t < k then BOOST.w S m oh t else 0)) \<in> {x. \<forall>q\<ge>k. movec.vec_nth x q = 0}"
  proof auto
    fix S q m
    show "k \<le> q \<Longrightarrow> movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then BOOST.w S m oh t else 0)) q = 0"
      using vec_lambda_inverse lt_valid[of k "BOOST.w S m oh"] by auto
  qed
  then show ?thesis unfolding WH_def all_linear_def myroom_def
    by auto
qed


lemma vecmain: "finite C \<Longrightarrow> T \<le> m \<Longrightarrow> card C \<le> m \<Longrightarrow> C \<subseteq> (myroom T) \<Longrightarrow> card ((\<lambda>h. restrict_map (mapify h) C) ` (all_linear (myroom T))) \<le> m^T"
  using vectors.vmain by auto

lemma aux259: "A\<subseteq>D \<Longrightarrow> ((\<lambda>h. mapify h |` C) ` A) \<subseteq> ((\<lambda>h. mapify h |` C) ` D)" by auto

lemma vec1: "finite C \<Longrightarrow> T \<le> m \<Longrightarrow> card C \<le> m \<Longrightarrow> C \<subseteq> (myroom T) \<Longrightarrow> card ((\<lambda>h. restrict_map (mapify h) C) ` (WH T)) \<le> m^T"
  using vecmain WH_subset[of T] vectors.vfinite card_mono aux259[of "WH T" "all_linear (myroom T)"]
  by (metis (mono_tags, lifting) le_trans)


lemma aux843: "finite (dom f) \<Longrightarrow> card (ran f) \<le> card (dom f)"
proof -
  assume "finite (dom f)"
  moreover have "Some ` (ran f) = f ` (dom f)"
    by (smt Collect_cong Collect_mono aux41 domI image_def mem_Collect_eq ran_def)
  moreover have "card (ran f) = card (Some ` (ran f))"
    by (simp add: card_image) 
  ultimately show "card (ran f) \<le> card (dom f)"
    by (simp add: card_image_le)
qed


lemma aux630: "movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D S y oh t) i else 0) \<in> myroom k" 
    using lt_valid[of k "(\<lambda>t. oh (BOOST.D S y oh t) i)"] myroom_def[of k] vec_lambda_inverse by auto



lemma assumes "finite C" "a\<in>Agg_res k C"
  shows vec2: "card (ran a) \<le> card C" "ran a \<subseteq> myroom k"
proof -
  have "dom a \<subseteq> C" using assms(2) Agg_res_def
    by (simp add: dom_mapify_restrict)
  then show "card (ran a) \<le> card C" using card_mono assms(1) aux843
    by (metis infinite_super le_trans)
   obtain Q where o1: "Q\<in>St"
      "a = (\<lambda>h. mapify h |` C) (\<lambda>i. movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) i else 0))"
     using Agg_res_def Agg_def assms(2) by auto
  show "ran a \<subseteq> myroom k" 
  proof
    fix r
    assume a1: "r\<in> ran a"
    then obtain x where o2: "a x = Some r"
    proof -
      assume a1: "\<And>x. a x = Some r \<Longrightarrow> thesis"
      have "r \<in> {m. \<exists>aa. a aa = Some m}"
        by (metis \<open>r \<in> ran a\<close> ran_def)
      then show ?thesis
        using a1 by blast
    qed
    moreover have "a x = Some (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0))"
    proof -
      have "x \<in> C"
        using o2 \<open>dom a \<subseteq> C\<close> by blast
      then show ?thesis
        by (simp add: mapify_def o1(2))
    qed
    ultimately have "r = movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)" by auto
    then show "r\<in> myroom k" using myroom_def aux630[of k] by auto
  qed
qed



lemma
  assumes "finite C" "a\<in>Agg_res T C" "T \<le> card C"
  shows final2: "card (WH_res T a) \<le> (card C)^T" "finite (WH_res T a)"
  using vec1[of "ran a"] vec2[of C a T] WH_res_def[of T a] assms
proof -
  have "dom a = C" using assms(2) Agg_res_def mapify_def 
  proof -
    obtain mm :: "('a \<Rightarrow> movec) set \<Rightarrow> (('a \<Rightarrow> movec) \<Rightarrow> 'a \<Rightarrow> movec option) \<Rightarrow> ('a \<Rightarrow> movec option) \<Rightarrow> 'a \<Rightarrow> movec" where
      f1: "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (mm x0 x1 x2) \<and> mm x0 x1 x2 \<in> x0)"
      by moura
    have "a \<in> (\<lambda>f. mapify f |` C) ` Agg T"
      using Agg_res_def assms(2) by blast
    then have f2: "a = mapify (mm (Agg T) (\<lambda>f. mapify f |` C) a) |` C"
      using f1 by (meson imageE)
    have "C = dom (mapify (mm (Agg T) (\<lambda>f. mapify f |` C) a)) \<inter> C"
      by (simp add: mapify_def)
    then show ?thesis
      using f2 by (metis dom_restrict)
  qed
  then have s10: "finite (ran a)" using assms(1)
    by (simp add: finite_ran)
  then have "card (WH_res T a) \<le> (card C)^T"
    using vec1[of "ran a"] vec2[of C a T] WH_res_def[of T a] assms by auto
  moreover have "card (ran a) \<le> card C"
    using vec2[of C a T] assms by auto
  ultimately show "card (WH_res T a) \<le> (card C)^T" using power_mono[of "card (ran a)" "card C" T] Tgtz
    by (meson le0 le_trans nat_mult_le_cancel_disj)
  show "finite (WH_res T a)" using vectors.vfinite s10 WH_res_def WH_subset[of T]
    by (metis aux259 infinite_super)
qed

subsection "Bounding Agg_res"

lemma aux296: "(a::nat) \<le> b * c \<Longrightarrow> b \<le> c ^ (d::nat) \<Longrightarrow> c \<ge> 0  \<Longrightarrow> a \<le> c ^ (Suc d)"
  by (metis dual_order.trans mult.commute mult_right_mono power_Suc)

lemma mapify_restrict_alt: "mapify h |` C = (\<lambda>x. if x\<in>C then Some (h x) else None)"
  by (metis mapify_def restrict_in restrict_out)

lemma baux: "(\<lambda>h. h |` C) ` baseclass.H_map = (\<lambda>h. restrict_map (mapify h) C) ` B" by auto

lemma base1: "baseclass.VCDim = Some d \<Longrightarrow> 1 < d \<Longrightarrow> d \<le> card C \<Longrightarrow> C \<subseteq> X \<Longrightarrow> card ((\<lambda>h. restrict_map (mapify h) C) ` B) \<le> (card C)^d"
  using baseclass.resforboost[of C d "card C"] baux card_gt_0_iff by force 


lemma assumes "finite C"
  shows base2: "card (Agg_res k C) \<le> card ((\<lambda>h. restrict_map (mapify h) C) ` B) ^ k \<and> finite (Agg_res k C)"
proof(induct k)
  case 0
  let ?f = "(\<lambda>x. if x\<in>C then Some 0 else None)"
  let ?A = "((\<lambda>h. mapify h |` C) `
      (\<lambda>Q i. (vec_lambda (\<lambda>t. (if t<0 then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))) ` St)"
  have s0: "St \<noteq> {}"
  proof -
    obtain x where "x\<in>X" using infx by fastforce
    then have "(x,True) \<in> (X\<times>{True, False})" by auto
    moreover obtain m::nat where "0 < m" by auto
    moreover obtain S::"(nat \<Rightarrow> 'a \<times> bool)" where "(\<forall>i<m. S i = (x,True))" by fastforce
    moreover have "(\<forall>i<m. S i \<in> (X\<times>{True, False}))" using calculation by auto
    ultimately have "(S,m)\<in>St" by auto
    then show ?thesis by auto 
  qed
  then have "(\<lambda>Q i. (vec_lambda (\<lambda>t. (if t<0 then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0))))
     ` St = {(\<lambda>i. 0)}" using zero_movec_def by auto
  moreover from this have "card ?A = 1" using card_image_le by auto
  ultimately show ?case unfolding Agg_res_def Agg_def by auto
next
  case c1: (Suc k)
  let ?SucA = "Agg_res (Suc k) C"
  let ?A = "Agg_res k C"
  let ?resB = "(\<lambda>h. mapify h |` C) ` B"
  let ?conv = "(\<lambda>(vm, g). (\<lambda>x. (case (vm x) of Some z \<Rightarrow> Some (vec_lambda 
  (\<lambda>t. if t=k then (case g x of Some x' \<Rightarrow> x') else vec_nth z t)) | None \<Rightarrow> None)))"
  have s1: "?SucA \<subseteq>
     ?conv ` (?A \<times> ?resB)"
  proof
    fix vm
    assume a1: "vm\<in>?SucA"
    then obtain Q where o1: "Q\<in>St"
      "vm = (\<lambda>h. mapify h |` C) ((\<lambda>Q i. (vec_lambda (\<lambda>t. (if t<Suc k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))) Q)"
      unfolding Agg_res_def Agg_def by auto
    have s2: "dom vm = C" using a1 Agg_res_def
      by (simp add: dom_mapify_restrict)
    let ?vm = "(\<lambda>x. (case (vm x) of Some z \<Rightarrow> Some (vec_lambda 
  (\<lambda>t. if t=k then 0 else vec_nth z t)) | None \<Rightarrow> None))"
    let ?vm' = "(\<lambda>h. mapify h |` C) ((\<lambda>Q i. (vec_lambda (\<lambda>t. (if t<k then (oh (BOOST.D (fst Q) (snd Q) oh t) i) else 0)))) Q)"
    have "\<forall>x. ?vm x = ?vm' x"
    proof
      fix x
      show "(case vm x of None \<Rightarrow> None
          | Some z \<Rightarrow> Some (movec.vec_lambda (\<lambda>t. if t = k then 0 else movec.vec_nth z t))) =
         (mapify (\<lambda>i. movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) i else 0)) |` C) x"
      proof(cases "vm x")
        case None
        moreover from this have "x\<notin>C" using s2 by auto
        ultimately show ?thesis by auto
      next
        case c1: (Some a)
        then have s3: "x\<in>C" using s2 by auto
        then have s4: "(mapify (\<lambda>i. movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) i else 0)) |` C) x
        =  Some ( movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0))"
          by (meson mapify_restrict_alt)
        have "a = movec.vec_lambda (\<lambda>t. if t < Suc k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)"
          using o1(2) c1 s3 
            mapify_restrict_alt[of "(\<lambda>i. movec.vec_lambda (\<lambda>t. if t < Suc k then oh (BOOST.D (fst Q) (snd Q) oh t) i else 0))" C]
          by auto
        then have "\<forall>t. (\<lambda>t. if t = k then 0 else movec.vec_nth a t) t = (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0) t"
          using vec_lambda_inverse lt_valid[of "Suc k" "(\<lambda>t. oh (BOOST.D (fst Q) (snd Q) oh t) x)"] by auto
        then have "(\<lambda>t. if t = k then 0 else movec.vec_nth a t) = (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)"
          by auto
        then show ?thesis
          by (simp add: c1 s4) 
      qed
    qed
    then have s100: "?vm \<in> ?A" unfolding Agg_res_def Agg_def using o1(1) by auto
    have "oh (BOOST.D (fst Q) (snd Q) oh k) \<in> B" using ohtwoclass by auto
    then have "mapify (oh (BOOST.D (fst Q) (snd Q) oh k)) |` C \<in> ?resB" by auto
    then have s101: "(\<lambda>x. if x\<in>C then Some (oh (BOOST.D (fst Q) (snd Q) oh k) x) else None) \<in> ?resB" 
      using mapify_restrict_alt[of "oh (BOOST.D (fst Q) (snd Q) oh k)" C] by auto
    have s102: "vm = ?conv (?vm,(\<lambda>x. if x\<in>C then Some (oh (BOOST.D (fst Q) (snd Q) oh k) x) else None))"
    proof
      fix x
      show "vm x =
         (case (\<lambda>x. case vm x of None \<Rightarrow> None
                     | Some z \<Rightarrow> Some (movec.vec_lambda (\<lambda>t. if t = k then 0 else movec.vec_nth z t)),
                \<lambda>x. if x \<in> C then Some (oh (BOOST.D (fst Q) (snd Q) oh k) x) else None) of
          (vm, g) \<Rightarrow>
            \<lambda>x. case vm x of None \<Rightarrow> None
                 | Some z \<Rightarrow>
                     Some
                      (movec.vec_lambda
                        (\<lambda>t. if t = k then case g x of Some x' \<Rightarrow> x' else movec.vec_nth z t)))
          x"
      proof(cases "vm x")
        case None
        then show ?thesis by auto
      next
        case c1: (Some a)
        moreover from this have s3: "x\<in>C" using s2 by auto
        ultimately show ?thesis apply auto
        proof -
          have s4: "a = movec.vec_lambda (\<lambda>t. if t < Suc k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)"
            using o1(2) c1 s3 
              mapify_restrict_alt[of "(\<lambda>i. movec.vec_lambda (\<lambda>t. if t < Suc k then oh (BOOST.D (fst Q) (snd Q) oh t) i else 0))" C]
            by auto
          then have "\<forall>t. (\<lambda>t. if t = k then 0 else movec.vec_nth a t) t = (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0) t"
            using vec_lambda_inverse lt_valid[of "Suc k" "(\<lambda>t. oh (BOOST.D (fst Q) (snd Q) oh t) x)"] by auto
          then have "(\<lambda>t. if t = k then 0 else movec.vec_nth a t) = (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)"
            by auto
          then have s5: "movec.vec_lambda (\<lambda>t. if t = k then (oh (BOOST.D (fst Q) (snd Q) oh k) x)  else
     movec.vec_nth (movec.vec_lambda (\<lambda>t. if t = k then 0 else movec.vec_nth a t)) t)
      = movec.vec_lambda (\<lambda>t. if t = k then (oh (BOOST.D (fst Q) (snd Q) oh k) x)  else
     movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)) t)" 
            by metis
          have "movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0))
              = (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)" 
            using vec_lambda_inverse lt_valid[of k "(\<lambda>t. oh (BOOST.D (fst Q) (snd Q) oh t) x)"] by auto

          then have "movec.vec_lambda (\<lambda>t. if t = k then (oh (BOOST.D (fst Q) (snd Q) oh k) x)  else
     (movec.vec_nth (movec.vec_lambda (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0))) t)
       = movec.vec_lambda (\<lambda>t. if t = k then (oh (BOOST.D (fst Q) (snd Q) oh k) x)  else
     (\<lambda>t. if t < k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0) t)" by presburger
          moreover have "...
        = movec.vec_lambda (\<lambda>t. if t < Suc k then oh (BOOST.D (fst Q) (snd Q) oh t) x else 0)"
            by (metis (full_types) less_Suc_eq) 
          ultimately have "a = movec.vec_lambda (\<lambda>t. if t = k then (oh (BOOST.D (fst Q) (snd Q) oh k) x)  else
     movec.vec_nth (movec.vec_lambda (\<lambda>t. if t = k then 0 else movec.vec_nth a t)) t)"
            using s4 s5 by auto
          then show "a =
    movec.vec_lambda
     (\<lambda>t. if t = k then case Some (oh (BOOST.D (fst Q) (snd Q) oh k) x) of Some x' \<Rightarrow> x'
           else movec.vec_nth (movec.vec_lambda (\<lambda>t. if t = k then 0 else movec.vec_nth a t)) t)"
            by (metis option.simps(5)) 
        qed
      qed
    qed
    from s100 s101 have "(?vm,(\<lambda>x. if x\<in>C then Some (oh (BOOST.D (fst Q) (snd Q) oh k) x) else None)) \<in> (?A \<times> ?resB)"
      by auto
    from this s102 show "vm \<in> ?conv ` (?A \<times> ?resB)" by blast
  qed
  then have "finite ?A \<Longrightarrow> finite ?resB \<Longrightarrow> card ?SucA \<le> card ?A * card ?resB"
  proof -
    assume a1: "finite ?A" "finite ?resB"
    then have "finite (?conv ` (?A \<times> ?resB))" by auto
    then have "card ?SucA \<le> card (?A \<times> ?resB)" 
      using s1 card_image_le[of "(?A \<times> ?resB)" ?conv] a1 card_mono[of "(?conv ` (?A \<times> ?resB))" ?SucA] by auto
    then show "card ?SucA \<le> card ?A * card ?resB"
      using card_cartesian_product[of ?A ?resB] by auto
  qed
  moreover have s20:"finite ?resB" using assms baseclass.finite_restrict[of C] by (simp add: baux) 
  moreover have "finite ?A" using c1 by auto
  ultimately have "card ?SucA \<le> card ?A * card ?resB" by auto
  moreover have "finite(?A \<times> ?resB)" using s20 c1 by auto
  moreover from this have "finite (?SucA)" using s1 using finite_surj by auto 
  ultimately show ?case using aux296 c1 by auto
qed


lemma assumes "baseclass.VCDim = Some d" "1 < d" "d \<le> card C" "C \<subseteq> X" "finite C"
  shows final1:"card (Agg_res k C) \<le> ((card C)^d) ^ k"
proof -
have "\<exists>n. card ((\<lambda>f. mapify f |` C) ` Agg k) \<le> n ^ k \<and> n \<le> card C ^ d"
  by (metis Agg_res_def One_nat_def assms(1) assms(2) assms(3) assms(4) assms(5) base1 base2)
  then show ?thesis
    by (metis Agg_res_def le0 le_trans power_mono)
qed 

subsection "Putting the upper bound together"

lemma assumes "finite C" "C \<subseteq> X" "T\<le> card C" "d \<le> card C" "baseclass.VCDim = Some d" "1 < d"
  shows final10: "card (restrictH outer.H_map C {True, False}) \<le>  (card C)^((d+1)*T)"
proof -
  let ?f = "(\<lambda>a. ((\<lambda>w. (w, a)) ` (WH_res T a)))"
  let ?S = "Agg_res T C"
  have a1:"finite (Agg_res T C)" using base2 assms by auto
  have a2:"\<forall>a\<in> Agg_res T C. finite (WH_res T a)" using final2(2) assms by auto
  have sfin: "\<forall>s\<in>?f ` ?S. finite s" using a2 by auto
  moreover have "\<forall>s\<in>?S. \<forall>t\<in>?S. s \<noteq> t \<longrightarrow> ?f s \<inter> ?f t = {}" by auto
  ultimately have s1: "card (UNION ?S ?f) = (\<Sum>x\<in>?S. card (?f x))"
    using card_Union_image a1 by auto
  have "(\<And>i. i \<in> Agg_res T C \<Longrightarrow> card (WH_res T i) \<le> (card C) ^ T)"
    using final2[of C] assms(1,3) by auto
  moreover have "(\<And>i. i \<in> Agg_res T C \<Longrightarrow> (card \<circ> (\<lambda>a. (\<lambda>w. (w, a)) ` WH_res T a)) i \<le> card (WH_res T i))"
    using a2 card_image_le by auto
  ultimately have "(\<And>i. i \<in> Agg_res T C \<Longrightarrow> (card \<circ> (\<lambda>a. (\<lambda>w. (w, a)) ` WH_res T a)) i \<le>  (card C) ^ T)"
    by fastforce
  then have "(\<Sum>x\<in>?S. card (?f x)) \<le> card ?S * ((card C)^T)"
    using sum_bounded_above[of ?S "card \<circ> ?f" "((card C)^T)"] by auto
  moreover have "card ?S \<le> ((card C)^d) ^ T" using final1 assms(1,2,4,5,6) by auto
  ultimately have "(\<Sum>x\<in>?S. card (?f x)) \<le> ((card C)^T)*(((card C)^d) ^ T)"
    by (smt add_mult_distrib2 le_Suc_ex mult.commute trans_le_add1)
  then have "card (UNION ?S ?f) \<le> ((card C)^T)*(((card C)^d) ^ T)" using s1 by auto
  moreover have s5: "{map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a}
   = (\<lambda>(w,a). w \<circ>\<^sub>m a) ` (UNION ?S ?f)" by auto
  moreover have s6: "finite (UNION ?S ?f)" using sfin a1 by auto
  ultimately have s2: "card ({map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a}) \<le> ((card C)^T)*(((card C)^d) ^ T)" 
    using card_image_le[of "(UNION ?S ?f)" "(\<lambda>(w,a). w \<circ>\<^sub>m a)"] by auto
  have "((card C)^d) ^ T = (card C)^(d*T)"
    by (metis power_mult)
  moreover have "(card C)^T * (card C)^(d*T) = (card C)^(T*(d+1))"
    by (simp add: mult.commute power_add) 
  ultimately have "((card C)^T)*(((card C)^d) ^ T) =  (card C)^((d+1)*T)"
    by (metis semiring_normalization_rules(26) semiring_normalization_rules(3))
  then have "card ({map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a}) \<le>  (card C)^((d+1)*T)" using s2 by auto
  moreover have "finite ({map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a})" using s5 s6 by auto
  moreover have "card (restrictH outer.H_map C {True, False}) \<le> card ({map. \<exists>a\<in>Agg_res T C. \<exists>w\<in>WH_res T a. map = w \<circ>\<^sub>m a})"
    using calculation(2) card_mono final5[of C] by auto
  ultimately show ?thesis by auto
qed

subsection "Aux lemma A.1"

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
  
lemma ln_bound_linear3: "x>0 \<Longrightarrow> a<exp 1 \<Longrightarrow> a > 0 \<Longrightarrow> a * ln (x::real) < x"
  by (metis less_eq_real_def less_le_trans ln_bound_linear2 mult_less_cancel_right mult_zero_left not_less) 
    


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
    shows aux683: "x > a* ln(x)" 
proof (cases "a<sqrt(exp 1)")
  case True
  moreover have "(1::real) < exp 1"
    by auto
  ultimately have "a < exp (1::real)"
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
  shows lemA1: "0 < x \<Longrightarrow> 0 < a \<Longrightarrow> x \<le> a* ln(x) \<Longrightarrow> x < 2*a*ln(a)"
  using aux683 by (meson not_less)

subsection "Upper bound of VC-Dimension"



lemma assumes "shatters outer.H_map C {True, False}"
"finite C" "C \<subseteq> X" "T\<le> card C" "d \<le> card C" "baseclass.VCDim = Some d" "1 < d"
  shows final11:"card C < 2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))"
proof -
  have "card (restrictH outer.H_map C {True, False}) = 2 ^ (card C)" using mappow assms(1,2) shatters_def
    by (metis finite.emptyI finite_insert outer.cardY)
  then have "2 ^ (card C) \<le> (card C)^((d+1)*T)" using final10 assms
    by fastforce
  moreover have s1: "0 < (card C)^((d+1)*T)"
    using assms(5) assms(7) by auto
  moreover have "0 < (2::nat) ^ (card C)" by auto
  ultimately have "ln (2 ^ (card C)) \<le> ln((card C)^((d+1)*T))"
    using ln_le_cancel_iff by (metis numeral_power_le_of_nat_cancel_iff
              of_nat_0_less_iff of_nat_numeral of_nat_zero_less_power_iff)
  then have "real (card C) * ln(2) \<le> real ((d+1)*T) * ln((card C))"
    using ln_realpow s1 by auto
  then have "real (card C) \<le> real ((d+1)*T)/ln(2) * ln((card C))"
    using frac_le[of "real (card C) * ln(2)" "real ((d+1)*T) * ln((card C))" "ln(2)" "ln(2)"] by auto
  moreover have "0<real(card C)"
    using assms(4) vectors.dgz by linarith
  moreover have "0<real ((d+1)*T)/ln(2)"
  proof -
    have f1: "\<not> ln ((1::real) + 1) < 0" by force
    have "(0::real) < ln (1 + 1)" by simp
    then show ?thesis using f1 by (metis add_is_0 add_mult_distrib divide_eq_0_iff divide_less_cancel
         less_nat_zero_code linorder_neqE_nat nat_mult_1 of_nat_0_less_iff one_add_one vectors.dgone)
  qed
  ultimately have "real (card C) < 2 * real ((d+1)*T)/ln(2) * ln(real ((d+1)*T)/ln(2))"
    using lemA1[of "real (card C)" "real ((d+1)*T)/ln(2)"] by auto
  then show ?thesis by auto
qed

lemma assumes "shatters outer.H_map C {True, False}" "baseclass.VCDim = Some d" "1 < d" "C \<subseteq> X"
shows final12: "(card C) < 2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))"
proof -
  have "3\<le>(d+1)*T" using vectors.dgone assms(3)
    by (metis add_mono_thms_linordered_field(4) discrete less_1_mult less_imp_le_nat
        numeral_Bit1 numeral_One semiring_normalization_rules(3))
  then have "ln(2)*3\<le>(d+1)*T" using ln_2_less_1 by linarith 
  then have "3\<le>(((d+1)*T)/ln(2))" using le_divide_eq_numeral(1) by fastforce
  then have "1\<le>ln(((d+1)*T)/ln(2))" using ln3_gt_1
    by (metis (no_types, hide_lams) add.right_neutral add_0_left add_mono_thms_linordered_field(4)
        less_trans linorder_not_less ln_less_cancel_iff rel_simps(51))
  then have "ln(2)\<le>2*ln(((d+1)*T)/ln(2))" using ln_2_less_1 by linarith
  then have s1: "1 \<le> 2/ln(2)*ln(((d+1)*T)/ln(2))" using le_divide_eq_numeral(1) by fastforce
  moreover have "d\<le>(d+1)*T" using vectors.dgone by (metis (full_types) le0 le_add_same_cancel1
        less_or_eq_imp_le mult.commute mult.left_neutral mult_le_mono)
  moreover have s2: "0 \<le> real ((d + 1) * T)" by auto
  ultimately have s3: "d \<le> ((d+1)*T)* 2/ln(2) * ln(((d+1)*T)/ln(2))" 
    using mult_mono[of d "(d+1)*T" 1 "2/ln(2)*ln(((d+1)*T)/ln(2))"]
  proof -
    have "real d \<le> real ((d + 1) * T)"
      by (metis \<open>d \<le> (d + 1) * T\<close> of_nat_mono)
    then show ?thesis
      by (metis (no_types) \<open>0 \<le> real ((d + 1) * T)\<close> \<open>1 \<le> 2 / ln 2 * ln (real ((d + 1) * T) / ln 2)\<close> 
          \<open>\<lbrakk>real d \<le> real ((d + 1) * T); 1 \<le> 2 / ln 2 * ln (real ((d + 1) * T) / ln 2); 0 \<le> real ((d + 1) * T); 0 \<le> 1\<rbrakk>
           \<Longrightarrow> real d * 1 \<le> real ((d + 1) * T) * (2 / ln 2 * ln (real ((d + 1) * T) / ln 2))\<close>
          divide_divide_eq_right le_numeral_extra(1) mult.right_neutral of_nat_mult of_nat_numeral
          times_divide_eq_left times_divide_eq_right)
     qed 
     have "T\<le>(d+1)*T" by simp
     from this s1 s2 have s4: "T \<le> 2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))"
       using mult_mono[of T "(d+1)*T" 1 "2/ln(2)*ln(((d+1)*T)/ln(2))"]
     proof -
       have f1: "\<not> real T \<le> real ((d + 1) * T) \<or> real T \<le> real ((d + 1) * T) * (2 / ln 2 * ln (real ((d + 1) * T) / ln 2))"
         by (metis (no_types) \<open>\<lbrakk>real T \<le> real ((d + 1) * T); 1 \<le> 2 / ln 2 * ln (real ((d + 1) * T)
           / ln 2); 0 \<le> real ((d + 1) * T); 0 \<le> 1\<rbrakk> \<Longrightarrow> real T * 1 \<le> real ((d + 1) * T) *
         (2 / ln 2 * ln (real ((d + 1) * T) / ln 2))\<close> le_numeral_extra(1) mult.right_neutral s1 s2)
       have "real T \<le> real (T * (d + 1))"
         by (metis \<open>T \<le> (d + 1) * T\<close> mult.commute of_nat_mono)
       then show ?thesis
         using f1 by (metis (no_types) divide_divide_eq_right mult.commute of_nat_mult of_nat_numeral times_divide_eq_left)
     qed
  have s5: "0<2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))" using s4 vectors.dgz by linarith
  then show ?thesis 
  proof (cases "finite C \<and> T\<le> card C \<and> d \<le> card C")
    case True
    then show ?thesis using final11 assms by auto
  next
    case False
    then show ?thesis using s3 s4 s5 apply auto
      by (smt linorder_not_less nat_less_real_le) 
  qed
qed

lemma \<comment> \<open>Lemma 10.3\<close>
assumes  "baseclass.VCDim = Some d" "1 < d"
shows VCBoosting: "\<exists>od. outer.VCDim = Some od \<and> od \<le> nat(floor(2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))))"
  using outer.vcd_upper final12[of _ d] assms le_nat_floor by (simp add: less_eq_real_def) 

lemma assumes  "baseclass.VCDim = Some d" "1 < d"
shows "outer.uniform_convergence" using outer.uni_conv VCBoosting assms by auto

subsection "Putting the bounds together"

lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and "\<delta>\<in>{x.0<x\<and>x<1}" 
    shows prbound: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>(H T). abs(PredErr D h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(outer.growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
  using outer.theorem611 assms by auto

  

lemma assumes "set_pmf D \<subseteq> (X\<times>{True, False})" "0<m"
  shows doboost: "\<forall>S\<in>(set_pmf (Samples m D)). BOOST S m X oh"
  unfolding BOOST_def Samples_def 
proof
  fix S
  assume "S \<in> set_pmf (Pi_pmf {0..<m} undefined (\<lambda>_. D))"
  then have "(\<forall>i\<in>{0..<m}. S i \<in> X \<times> {True, False})"
    using assms(1) set_Pi_pmf[of "{0..<m}" S undefined D] by auto
  moreover have "(\<forall>Ds x. oh Ds x \<in> {- 1, 1}) \<and> 0 < m" using assms(2) defonB ohtwoclass by auto
  ultimately show "(\<forall>Ds x. oh Ds x \<in> {- 1, 1}) \<and> 0 < m \<and> (\<forall>i<m. S i \<in> X \<times> {True, False})" by auto
qed



lemma fixes m :: nat
      and \<delta> :: real
  assumes "set_pmf D \<subseteq> (X\<times>{True, False})"
      and "\<delta>\<in>{x.0<x\<and>x<1}" "0<m" "baseclass.VCDim = Some d" "1 < d"
      "\<forall>S\<in>(set_pmf (Samples m D)).\<forall> t. BOOST.\<epsilon> S m oh t \<le> 1/2 - \<gamma>" 
      "\<forall>S\<in>(set_pmf (Samples m D)).\<forall> t. BOOST.\<epsilon> S m oh t \<noteq> 0" and "\<gamma> > 0"
    shows "measure_pmf.prob (Samples m D) {S. PredErr D (BOOST.hyp S m oh T)
   \<le> (4+sqrt(ln(real(outer.growth (2*m)))))/(\<delta> * sqrt(2*m)) + exp (-2*\<gamma>^2*T)} \<ge> 1 - \<delta>"
    and "outer.growth m \<le> sum (\<lambda>x. m choose x) {0..(nat(floor(2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2)))))}"
proof -
  let ?prb = "(4+sqrt(ln(real(outer.growth (2*m)))))/(\<delta> * sqrt(2*m))"
  let ?A = "{S.  S\<in>(set_pmf (Samples m D)) \<and> 
    (\<forall>h\<in>(H T). abs(PredErr D h - TrainErr S {0..<m} h) \<le> ?prb)}"
  have "?A
  = {S. \<forall>h\<in>(H T). abs(PredErr D h - TrainErr S {0..<m} h) \<le> ?prb} \<inter> set_pmf (Samples m D)" by auto
  then have s10: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>(H T). abs(PredErr D h - TrainErr S {0..<m} h) \<le> ?prb}
    = measure_pmf.prob (Samples m D) ?A"
    by (simp add: measure_Int_set_pmf) 
  have s1: "?A\<subseteq>{S. S\<in>(set_pmf (Samples m D)) \<and> (\<forall>h\<in>(H T). PredErr D h - TrainErr S {0..<m} h \<le> ?prb)}"
    by auto
  have "\<forall>S\<in>(set_pmf (Samples m D)).(BOOST.hyp S m oh T)\<in> H T" unfolding Samples_def
  proof
    fix S
    assume "S \<in> set_pmf (Pi_pmf {0..<m} undefined (\<lambda>_. D))"
    then have "(\<forall>i\<in>{0..<m}. S i \<in> X \<times> {True, False})"
      using assms(1) set_Pi_pmf[of "{0..<m}" S undefined D] by auto
    then have "(S,m)\<in>St" using assms(3) by auto
    then show "BOOST.hyp S m oh T \<in> H T"
      using H_def by auto
  qed
  then have "?A
          \<subseteq> {S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T)
                   - TrainErr S {0..<m} (BOOST.hyp S m oh T) \<le> ?prb)}"
    using s1 by auto
  moreover have "\<forall>S. (PredErr D (BOOST.hyp S m oh T) - TrainErr S {0..<m} (BOOST.hyp S m oh T) \<le> ?prb) \<longrightarrow>
  (PredErr D (BOOST.hyp S m oh T) \<le> ?prb + TrainErr S {0..<m} (BOOST.hyp S m oh T))"
    by auto
  ultimately have "?A \<subseteq> {S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T)
                    \<le> ?prb + TrainErr S {0..<m} (BOOST.hyp S m oh T))}"
     by auto
  moreover have "\<forall>S\<in>(set_pmf (Samples m D)). TrainErr S {0..<m} (BOOST.hyp S m oh T) \<le> exp (-2*\<gamma>^2*T)"
    using BOOST.main102[of _ m X oh \<gamma> T] doboost assms(1,3,6,7,8) by auto
  moreover from this have "{S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T)
                    \<le> ?prb + TrainErr S {0..<m} (BOOST.hyp S m oh T))}
              \<subseteq> {S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T)
                    \<le> ?prb + exp (-2*\<gamma>^2*T))}" by auto
  ultimately have "?A \<subseteq> {S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T)
                    \<le> ?prb + exp (-2*\<gamma>^2*T))}" by auto
  moreover have "measure_pmf.prob (Samples m D) ?A \<ge> 1 - \<delta>"
    using s10 assms(1,2) prbound[of D "{True, False}" \<delta> m] by auto
  ultimately have "measure_pmf.prob (Samples m D)
{S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T) \<le> ?prb + exp (-2*\<gamma>^2*T))} \<ge> 1 - \<delta>"
    using subsetlesspmf[of ?A "{S. S\<in>(set_pmf (Samples m D)) \<and>
     (PredErr D (BOOST.hyp S m oh T) \<le> ?prb + exp (-2*\<gamma>^2*T))}" "Samples m D"] by auto
  moreover have "{S. S\<in>(set_pmf (Samples m D)) \<and> (PredErr D (BOOST.hyp S m oh T) \<le> ?prb + exp (-2*\<gamma>^2*T))}
  = {S. PredErr D (BOOST.hyp S m oh T) \<le> ?prb + exp (-2*\<gamma>^2*T)} \<inter> set_pmf (Samples m D)" by auto
  ultimately show "measure_pmf.prob (Samples m D)
               {S. PredErr D (BOOST.hyp S m oh T) \<le> ?prb + exp (-2*\<gamma>^2*T)} \<ge> 1 - \<delta>"
    by (simp add: measure_Int_set_pmf)
next
   let ?a = "nat(floor(2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2))))"
  obtain vcd where o1: "outer.VCDim = Some vcd" "vcd \<le> ?a"
    using VCBoosting assms(3,4,5) by auto
  then have "outer.growth m \<le> sum (\<lambda>x. m choose x) {0..vcd}" using outer.lem610 assms(3) by auto
  then show "outer.growth m \<le> sum (\<lambda>x. m choose x) 
            {0..(nat(floor(2*((d+1)*T)/ln(2) * ln(((d+1)*T)/ln(2)))))}"
    using o1(2) sum_mono2[of "{0..?a}" "{0..vcd}" "((choose) m)"] by auto
qed

end