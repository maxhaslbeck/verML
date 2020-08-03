theory LearningTheory
  imports Complex_Main Pi_pmf
begin

section auxiliaries

lemma set_Pi_pmf: "finite A \<Longrightarrow>  f \<in> set_pmf (Pi_pmf A dflt (%_. D)) \<Longrightarrow> i\<in>A \<Longrightarrow> f i \<in> set_pmf D"
  apply (auto simp: set_pmf_eq pmf_Pi)
  by (meson prod_zero) 

lemma subsetlesspmf: "A\<subseteq>B \<Longrightarrow> measure_pmf.prob Q A \<le> measure_pmf.prob Q B"
  using measure_pmf.finite_measure_mono by fastforce

section "Error Definitions"
text {* Error terms:
In machine learning, typically two different errors are measured when training a model. The training
error is the error achieved by the model on the data used for training while the validation error
is measured on a seperate data set that is retrieved from the same source. This is done to approximate
the error that can be expected when using the model to predict on new data from the same source
distribution. In the book and in this work this error will therefore be referred to as prediction
error. We can derive bounds for this error that do not require an actual validation set using
learning theory. *}

text \<open>Definition of the Prediction Error (3.1). 
    This is the Isabelle way to write: 
      @{text "L\<^sub>D(h) =  D({(x,y). y \<noteq> h x})"} \<close>
definition PredErr :: "('a \<times> 'b) pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "PredErr D h = measure_pmf.prob D {S. snd S \<noteq> h (fst S)}" 

lemma PredErr_nn: "PredErr D h \<ge> 0"
  unfolding PredErr_def by simp
lemma PredErr_le1: "PredErr D h \<le> 1"
  unfolding PredErr_def by simp

lemma PredErr_alt: "PredErr D h = measure_pmf.prob D {S\<in>set_pmf D.  snd S \<noteq> h (fst S)}"
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

lemma TrainErr_le1: 
  assumes "I\<noteq>{}" "finite I"
  shows "TrainErr S I h \<le> 1"
proof -
  from assms have *: "card I > 0" by auto
  have "(\<Sum>i\<in>I. case S i of (x, y) \<Rightarrow> if h x \<noteq> y then 1 else 0) \<le> (\<Sum>i\<in>I. 1::real)" 
    apply(rule sum_mono) by (simp add: split_beta') 
  also have "\<dots> = real (card I)"
    using real_of_card by simp
  finally show ?thesis 
    unfolding TrainErr_def using * by auto
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
(*definition Sample ::"'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) pmf" where
  "Sample D f = do {  a \<leftarrow> D;
                      return_pmf (a,f a) }"

lemma Sample_map: "Sample D f = map_pmf (\<lambda>x. (x, f x)) D"
  unfolding Sample_def by (auto simp: map_pmf_def)
*)

(* Samples n D f, generates a distribution of training sets of length n, which are
     independently and identically distribution wrt. to D.  *)
(* definition Samples :: "nat \<Rightarrow> 'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ((nat \<Rightarrow> 'a \<times> 'b)) pmf" where
  "Samples n D f = Pi_pmf {0..<n} undefined (\<lambda>_. Sample D f)" *)
definition Samples :: "nat \<Rightarrow> ('c) pmf \<Rightarrow> ((nat \<Rightarrow> 'c)) pmf" where
  "Samples n D = Pi_pmf {0..<n} undefined (\<lambda>_. D)"

(* The Event `repeated_event n P` is the event, where n times the event P occurs *)
definition "repeated_event n P = (PiE_dflt {0..<n} undefined (\<lambda>_. P))"

(* as `Samples` executes identical and independent samples, the probability of the `repeated_event`
    is just the nth power of the probability to hit the event S in a single sample *)
lemma iid: "measure_pmf.prob (Samples n D) (repeated_event n S) = measure_pmf.prob (D) S ^ n"
proof -
  have "measure_pmf.prob (Samples n D) (repeated_event n S)
        = (\<Prod>x\<in>{0..<n}. measure_pmf.prob ((\<lambda>_. D) x) ((\<lambda>_. S) x))" 
  unfolding Samples_def repeated_event_def
  apply(rule measure_Pi_pmf_PiE_dflt) by auto
  also have "\<dots> = (measure_pmf.prob D S)^n" 
    apply(subst prod_constant) by auto
  finally show ?thesis .
qed

section "Definition of PAC learnability"

locale learning_basics =
  fixes X :: "'a set"
    and Y :: "'b set"
    and H :: "('a \<Rightarrow> 'b) set"
assumes cardY: "card Y = 2"
    and Hdef: "\<forall>h x. h\<in>H \<longrightarrow> h x \<in> Y"
    and nnH: "H \<noteq> {}"
begin


definition RealizabilityAssumption where
  "RealizabilityAssumption D = (\<exists>h'\<in>H. PredErr D h' = 0)"

text \<open>The definition of PAC learnability following Definition 3.1.:\<close>

definition PAC_learnable :: "((nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where
  "PAC_learnable L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow> (\<exists>h'\<in>H. PredErr D h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le> \<epsilon>} \<ge> 1 - \<delta>)))"

lemma PAC_learnable_alt: "PAC_learnable L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow> RealizabilityAssumption D \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le> \<epsilon>} \<ge> 1 - \<delta>)))"
  unfolding PAC_learnable_def RealizabilityAssumption_def ..

text \<open>The definition of agnostic PAC learnablity following definition 3.3:\<close>


definition agnostic_PAC_learnable :: "((nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where
  "agnostic_PAC_learnable L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le> (LEAST x. x\<in>((\<lambda>h'. PredErr D h') ` H)) + \<epsilon>} \<ge> 1 - \<delta>)))"
 

lemma Least_gt0: "(\<exists>x\<in>Q:: real set. x=0) \<Longrightarrow> (\<forall>x\<in>Q. x \<ge> 0) \<Longrightarrow> Least (\<lambda>x. x\<in>Q) = 0"
  unfolding Least_def
  apply safe
  apply(rule the1_equality) 
  subgoal apply auto  
    by force   
  subgoal apply auto done
  done



lemma RealizabilityAssumption_LeastPredError_0:
  "RealizabilityAssumption D \<Longrightarrow> (LEAST x. x\<in>((\<lambda>h'. PredErr D h') ` H)) = 0"
  apply(rule Least_gt0)
  unfolding RealizabilityAssumption_def using PredErr_nn by auto

lemma agnostic_PAC_learnable_implies_PAC_learnable:
  assumes "agnostic_PAC_learnable L" shows "PAC_learnable L"
proof - 
  {
    from `agnostic_PAC_learnable L` obtain M where *: "\<And>D m \<epsilon> \<delta>. set_pmf D \<subseteq> X \<times> Y \<Longrightarrow> 
           0 < \<epsilon> \<Longrightarrow>  0 < \<delta>  \<Longrightarrow>  \<delta> < 1  \<Longrightarrow>  M \<epsilon> \<delta> \<le> m
             \<Longrightarrow> 1 - \<delta> \<le> measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le> (LEAST x. x\<in>((\<lambda>h'. PredErr D h') ` H)) +  \<epsilon>}"
      unfolding agnostic_PAC_learnable_def by blast
    have "\<exists>M. \<forall>D. set_pmf D \<subseteq> X \<times> Y \<longrightarrow> RealizabilityAssumption D \<longrightarrow>
            (\<forall>m \<epsilon>. 0 < \<epsilon> \<longrightarrow> 
                   (\<forall>\<delta>\<in>{x. 0 < x \<and> x < 1}.
                       M \<epsilon> \<delta> \<le> m \<longrightarrow> 1 - \<delta> \<le> measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le> \<epsilon>}))" 
    proof (rule exI[where x=M], safe)
      fix D m \<epsilon> \<delta>
      assume "RealizabilityAssumption D"
      then have **: "(LEAST x. x\<in>((\<lambda>h'. PredErr D h') ` H)) = 0" 
        using RealizabilityAssumption_LeastPredError_0 by auto
      assume "set_pmf D \<subseteq> X \<times> Y" "0 < \<epsilon>"  "0 < \<delta>" "\<delta> < 1" "M \<epsilon> \<delta> \<le> m"
      from *[OF this]
      show " 1 - \<delta> \<le> measure_pmf.prob (Samples m D) {S. PredErr D (L S m) \<le>  \<epsilon>}"
        by (simp add: **)
    qed
  }
  then show ?thesis unfolding PAC_learnable_alt .
qed


text \<open>"Empirical Risk Minimization" 
Its learning rule ERMe chooses for a given training set S an Hypothesis h from H
which minimizes the Training Error. \<close>

definition ERM :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "ERM S n = {h. is_arg_min (TrainErr S {0..<n}) (\<lambda>s. s\<in>H) h}"

definition ERMe :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "ERMe S n = (SOME h. h\<in> ERM S n)"
 
lemma ERM_0_in: "h' \<in> H \<Longrightarrow> TrainErr S {0..<n} h' = 0 \<Longrightarrow> h' \<in>ERM S n"
  unfolding ERM_def by (simp add: TrainErr_nn is_arg_min_linorder)

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

section "Uniform convergence"

definition representative :: "(nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('a \<times> 'b) pmf  \<Rightarrow> bool" where
  "representative S m \<epsilon> D \<longleftrightarrow> (\<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>)"


definition "uniform_convergence = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D. set_pmf D \<subseteq> (X\<times>Y)  \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D} \<ge> 1 - \<delta>)))"



lemma assumes "representative S m \<epsilon> D"
          and "S\<in>Samples m D"
          and "set_pmf D \<subseteq> (X\<times>Y)"
          and RealizabilityAssumption: "\<exists>h'\<in>H. PredErr D h' = 0"
        shows reptopred: "PredErr D (ERMe S m) \<le> \<epsilon>"
proof -
      from RealizabilityAssumption  
    obtain h' where h'H: "h'\<in>H" and u: "PredErr D h' = 0" by blast

    from u have "measure_pmf.prob D {S \<in> set_pmf D. snd S \<noteq> h' (fst S)} = 0" unfolding PredErr_alt .
    with measure_pmf_zero_iff[of D "{S \<in> set_pmf D. snd S \<noteq> h' (fst S)}"]       
    have correct: "\<And>x. x\<in>set_pmf D \<Longrightarrow> snd x = h' (fst x)" by blast

 from assms(2) set_Pi_pmf[where A="{0..<m}"]
      have tD: "\<And>i. i\<in>{0..<m} \<Longrightarrow> S i \<in> set_pmf D"
        unfolding Samples_def by auto 


    have z: "\<And>i. i\<in>{0..<m} \<Longrightarrow> (case S i of (x, y) \<Rightarrow> if h' x \<noteq> y then 1::real else 0) = 0"
    proof -
      fix i assume "i\<in>{0..<m}"
      then have i: "S i \<in> set_pmf D" using tD by auto
      from i correct  have "(snd (S i))  = h' (fst (S i))" by auto                
      then show "(case S i of (x, y) \<Rightarrow> if h' x \<noteq> y then 1::real else 0) = 0"
        by (simp add: prod.case_eq_if)
    qed

    have Th'0: "TrainErr S {0..<m} h' = 0" 
      unfolding TrainErr_def   using z  
      by fastforce

    then have "h' \<in>ERM S m" using ERM_0_in h'H by auto
    then have "ERMe S m \<in> ERM S m" using ERMe_def by (metis some_eq_ex)
    then have "ERMe S m \<in> H" using ERM_subset by blast     
    moreover have "(\<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>)"
      using representative_def assms(1) by blast
    ultimately have "abs(PredErr D (ERMe S m) - TrainErr S {0..<m} (ERMe S m)) \<le> \<epsilon>"
      using assms by auto
    moreover have "TrainErr S {0..<m} (ERMe S m) = 0" 
        proof -
          have f1: "is_arg_min (TrainErr S {0..<m}) (\<lambda>f. f \<in> H) (ERMe S m)"
            using ERM_def \<open>ERMe S m \<in> ERM S m\<close> by blast
          have f2: "\<forall>r ra. (((ra::real) = r \<or> ra \<in> {}) \<or> \<not> r \<le> ra) \<or> \<not> ra \<le> r"
            by linarith
          have "(0::real) \<notin> {}"
            by blast
          then show ?thesis
        using f2 f1 by (metis ERM_def Th'0 TrainErr_nn \<open>h' \<in> ERM S m\<close> is_arg_min_linorder mem_Collect_eq)
        qed
     ultimately show ?thesis by auto
qed



lemma assumes "(\<forall>D. set_pmf D \<subseteq> (X\<times>Y)  \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D} \<ge> 1 - \<delta>))"
  shows aux44:"set_pmf D \<subseteq> (X\<times>Y)  \<Longrightarrow> (\<exists>h'\<in>H. PredErr D h' = 0) \<Longrightarrow>  \<epsilon> > 0 \<Longrightarrow> \<delta>\<in>{x.0<x\<and>x<1} \<Longrightarrow> m \<ge> M \<epsilon> \<delta> \<Longrightarrow> 
          measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>"
  proof -
  fix D m \<epsilon> \<delta>
  assume a1: "set_pmf D \<subseteq> (X\<times>Y)" "\<exists>h'\<in>H. PredErr D h' = 0" "\<epsilon> > 0" "\<delta>\<in>{x.0<x\<and>x<1}" "m \<ge> M \<epsilon> \<delta>"
  from this assms have "measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D} \<ge> 1 - \<delta>" by auto
  then have "measure_pmf.prob (Samples m D) 
  {S. set_pmf D \<subseteq> (X\<times>Y) \<and> (\<exists>h'\<in>H. PredErr D h' = 0) \<and> (S\<in>Samples m D) \<and> representative S m \<epsilon> D} \<ge> 1 - \<delta>"
    using a1
    by (smt DiffE mem_Collect_eq pmf_prob_cong set_pmf_iff)
  moreover have "{S. set_pmf D \<subseteq> (X\<times>Y) \<and> (\<exists>h'\<in>H. PredErr D h' = 0) \<and> (S\<in>Samples m D) \<and> representative S m \<epsilon> D}
        \<subseteq> {S. PredErr D (ERMe S m) \<le> \<epsilon>}" using reptopred by blast
  ultimately show "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>"
    using subsetlesspmf order_trans by fastforce
qed


(* lemma 4.2*)
lemma assumes "uniform_convergence"
  shows "PAC_learnable (ERMe)" 
proof -
  obtain M where f1: "(\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D} \<ge> 1 - \<delta>))"
    using assms uniform_convergence_def by auto
  from aux44 f1 have "(\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow> (\<exists>h'\<in>H. PredErr D h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>))"
  by blast
  then show ?thesis using PAC_learnable_def by auto
qed


end
end