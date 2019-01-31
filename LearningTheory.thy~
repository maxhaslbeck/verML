theory LearningTheory
  imports Complex_Main Pi_pmf
begin

lemma set_Pi_pmf: "finite A \<Longrightarrow>  f \<in> set_pmf (Pi_pmf A dflt (%_. D)) \<Longrightarrow> i\<in>A \<Longrightarrow> f i \<in> set_pmf D"
  apply (auto simp: set_pmf_eq pmf_Pi)
  by (meson prod_zero) 


locale learning_basics =
  fixes X :: "'a set"
    and Y :: "'b set"
    and H :: "('a \<Rightarrow> 'b) set"
assumes cardY: "card Y = 2"
    and Hdef: "\<forall>h x. h\<in>H \<longrightarrow> h x \<in> Y"
    and nnH: "H \<noteq> {}"
begin


text \<open>Definition of the Prediction Error (2.1). 
    This is the Isabelle way to write: 
      @{text "L\<^sub>D\<^sub>,\<^sub>f(h) =  D({S. f S \<noteq> h S})"} \<close>
definition PredErr :: "'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "PredErr D f h = measure_pmf.prob D {S. f S \<noteq> h S}" 

lemma PredErr_alt: "PredErr D f h = measure_pmf.prob D {S\<in>set_pmf D.  f S \<noteq> h S}"
  unfolding PredErr_def apply(rule pmf_prob_cong) by (auto simp add: set_pmf_iff) 


text \<open>Definition of the Training Error (2.2). \<close>
definition TrainErr :: " ('c \<Rightarrow> ('a * 'b)) \<Rightarrow> 'c set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "TrainErr S I h = sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) I / card I"

lemma TrainErr_nn: "TrainErr S I h \<ge> 0"
proof -
  have "0 \<le> (\<Sum>i\<in>I. 0::real)" by simp
  also have "\<dots> \<le> (\<Sum>i\<in>I. case S i of (x, y) \<Rightarrow> if h x \<noteq> y then 1 else 0)"
    apply(rule sum_mono) by (simp add: split_beta') 
  finally show ?thesis 
    unfolding TrainErr_def by auto
qed

lemma TrainErr_correct: "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> TrainErr S I h = 0 \<Longrightarrow> i\<in>I \<Longrightarrow> h (fst (S i)) = snd (S i)"
proof (rule ccontr)
  assume  "finite I" "I \<noteq> {}"
  then have ii: "card I > 0" by auto
  assume i: "i\<in>I"
  then have I: "insert i (I-{i}) = I" by auto
  assume h: "h (fst (S i)) \<noteq> snd (S i)" thm sum.remove
  let ?f = "(\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)"
  have "\<And>i. ?f i \<ge> 0"
    by (simp add: case_prod_beta')
  then have sumnn: "sum ?f (I-{i}) \<ge> 0"
    by (simp add: sum_nonneg) 
  have "0 < ?f i" using h
    by (simp add: case_prod_beta')
  also have "\<dots> \<le> ?f i + sum ?f (I-{i})" using sumnn by auto
  also have "\<dots> = sum ?f I" apply(rule sum.remove[symmetric]) by fact+
  finally have "0 < sum ?f I" .
  then have "TrainErr S I h > 0" unfolding TrainErr_def using ii by auto
  moreover assume "TrainErr S I h = 0"
  ultimately show "False" by simp
qed

(* Sample D f, takes a sample x of the distribution D and pairs it with its
    label f x; the result is a distribution on pairs of (x, f x). *)
definition Sample ::"'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) pmf" where
  "Sample D f = do {  a \<leftarrow> D;
                      return_pmf (a,f a) }"

lemma Sample_map: "Sample D f = map_pmf (\<lambda>x. (x, f x)) D"
  unfolding Sample_def by (auto simp: map_pmf_def)

(* Samples n D f, generates a distribution of training sets of length n, which are
     independently and identically distribution wrt. to D.  *)
definition Samples :: "nat \<Rightarrow> 'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ((nat \<Rightarrow> 'a \<times> 'b)) pmf" where
  "Samples n D f = Pi_pmf {0..<n} undefined (\<lambda>_. Sample D f)"

(* The Event `repeated_event n P` is the event, where n times the event P occurs *)
definition "repeated_event n P = (PiE_dflt {0..<n} undefined (\<lambda>_. P))"

(* as `Samples` executes identical and independent samples, the probability of the `repeated_event`
    is just the nth power of the probability to hit the event S in a single sample *)
lemma iid: "measure_pmf.prob (Samples n D f) (repeated_event n S) = measure_pmf.prob (Sample D f) S ^ n"
proof -
  have "measure_pmf.prob (Samples n D f) (repeated_event n S)
        = (\<Prod>x\<in>{0..<n}. measure_pmf.prob ((\<lambda>_. Sample D f) x) ((\<lambda>_. S) x))" 
  unfolding Samples_def repeated_event_def
  apply(rule measure_Pi_pmf_PiE_dflt) by auto
  also have "\<dots> = (measure_pmf.prob (Sample D f) S)^n" 
    apply(subst prod_constant) by auto
  finally show ?thesis .
qed

subsection "Definition of PAC learnability"

text \<open>The definition of PAC learnability following Definition 3.1.:\<close>

definition PAC_learnable :: "((nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where
  "PAC_learnable L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y \<longrightarrow> (\<exists>h'\<in>H. PredErr D f h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. PredErr D f (L S m) \<le> \<epsilon>} \<ge> 1 - \<delta>)))"


definition ERM :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "ERM S n = {h. is_arg_min (TrainErr S {0..<n}) (\<lambda>s. s\<in>H) h}"

definition ERMe :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "ERMe S n = (SOME h. h\<in> ERM S n)"
 
lemma ERM_0_in: "h' \<in> H \<Longrightarrow> TrainErr S {0..<n} h' = 0 \<Longrightarrow> h' \<in>ERM S n"
  unfolding ERM_def by (simp add: TrainErr_nn is_arg_min_linorder)

(*lemma ERM_nonempty: "H\<noteq>{} \<Longrightarrow> ERM S n \<noteq> {}" unfolding ERM_def 
  by (simp add: ex_is_arg_min_if_finite fH) *)   

lemma ERM_subset: "ERM S n \<subseteq> H" 
  by (simp add: is_arg_min_linorder subset_iff ERM_def)   

lemma ERM_aux: "h' \<in> ERM S m \<Longrightarrow> TrainErr S {0..<m} h' = 0
        \<Longrightarrow> h \<in> ERM S m
        \<Longrightarrow> TrainErr S {0..<m} h = 0"
  unfolding ERM_def using TrainErr_nn
  by (metis is_arg_min_def less_eq_real_def mem_Collect_eq)

lemma hinnonempty: "h' \<in> ERM S m \<Longrightarrow> ERM S m \<noteq> {}" by auto

lemma ERMe_minimal: assumes "h' \<in> ERM S m" "TrainErr S {0..<m} h' = 0"
  shows "TrainErr S {0..<m} (ERMe S m) = 0"
  unfolding ERMe_def using ERM_aux[OF assms] hinnonempty[OF assms(1)]
  by (simp add: some_in_eq) 


end
end