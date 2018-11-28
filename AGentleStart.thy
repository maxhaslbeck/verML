theory AGentleStart
  imports "HOL-Probability.Probability" Pi_pmf
begin

section "Preface" 

subsection "auxiliary lemmas"

lemma set_Pi_pmf: "finite A \<Longrightarrow>  f \<in> set_pmf (Pi_pmf A dflt (%_. D)) \<Longrightarrow> i\<in>A \<Longrightarrow> f i \<in> set_pmf D"
  apply (auto simp: set_pmf_eq pmf_Pi)
  by (meson prod_zero) 

(*
lemma set_integral_at_point':
  fixes a 
  assumes "set_integrable M {a} f"
  and [simp]: "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * measure M {a}"
proof-
  have "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (intro set_lebesgue_integral_cong) simp_all
  then show ?thesis using assms   by simp
qed  *)

lemma fixes m :: nat and  h \<delta> \<epsilon> :: real
  assumes 
    nn: "h >0"  and
        epos: "\<epsilon> > 0" and m: "real m \<ge> (ln ( h / \<delta>)) / \<epsilon>" 
      and dd: "\<delta> > 0" "\<delta> < 1"
  shows aux_estim: "h * exp (-\<epsilon> * m) \<le> \<delta>"
proof -  
  from m epos have "ln ( h / \<delta>) \<le> real m * \<epsilon>"
    by (smt divide_cancel_right mult_imp_le_div_pos nonzero_mult_div_cancel_right)
  then have "( h / \<delta>) \<le> exp (real m * \<epsilon>)" using dd nn
    by (metis (full_types) divide_pos_pos exp_le_cancel_iff exp_ln of_nat_0_less_iff)
  then have "h \<le> \<delta> * exp (real m * \<epsilon>)" using dd
    by (smt divide_divide_eq_left exp_gt_zero less_divide_eq_1_pos linordered_field_class.sign_simps(44))
  then have A: "h / exp (real m * \<epsilon>) \<le> \<delta>"
    by (smt dd(1) divide_divide_eq_left exp_gt_zero less_divide_eq_1_pos mult.commute mult_pos_pos) 
  have B: "h / exp (real m * \<epsilon>) = h * exp (-\<epsilon> * m)"
  proof -
    have "h / exp (real m * \<epsilon>) = h * (exp 0) / exp (real m * \<epsilon>)"
      by auto
    also have "\<dots> = h * exp (0 - real m * \<epsilon>)" apply(subst exp_diff) by auto
    also have "\<dots> =  h * exp (- \<epsilon> * real m)" by auto
    finally show ?thesis .
  qed
  from A B show ed: "h * exp (-\<epsilon> * m) \<le> \<delta>" by auto
qed


section "Definition of PAC learnable"      

locale PAC =
  fixes X :: "'a set"
    and Y :: "'b set"  
  assumes 
      "X \<noteq> {}" 
    and "card Y = 2" (* is never used! *)
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

definition PAC_learnable :: "('a\<Rightarrow>'b) set \<Rightarrow> ((nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where
  "PAC_learnable H L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y \<longrightarrow> (\<exists>h'\<in>H. PredErr D f h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. PredErr D f (L S m) \<le> \<epsilon>} \<ge> 1 - \<delta>)))"

end



section "finite Hypothesis classes are PAC learnable"    

(* now assume we have a finite class of Hypotheses *)
locale finiteHypothesisClass = PAC where X=X and Y=Y for X::"'a set" and Y::"'b set"  + 
  fixes H :: "('a \<Rightarrow> 'b) set"
  assumes fH: "finite H"
    and nnH: "H \<noteq> {}"
begin

subsection "ERM and its learning rule"

text \<open>Let us now analyze the performance of the "Empirical Risk Minimization" rule
w.r.t. to the finite Hypothesis Class H.
Its learning rule ERMe chooses for a given training set S an Hypothesis h from H
which minimizes the Training Error. \<close>

definition ERM :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "ERM S n = {h. is_arg_min (TrainErr S {0..<n}) (\<lambda>s. s\<in>H) h}"

definition ERMe :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "ERMe S n = (SOME h. h\<in> ERM S n)"
 
lemma ERM_0_in: "h' \<in> H \<Longrightarrow> TrainErr S {0..<n} h' = 0 \<Longrightarrow> h' \<in>ERM S n"
  unfolding ERM_def by (simp add: TrainErr_nn is_arg_min_linorder)

lemma ERM_nonempty: "H\<noteq>{} \<Longrightarrow> ERM S n \<noteq> {}" unfolding ERM_def 
  by (simp add: ex_is_arg_min_if_finite fH)   

lemma ERM_subset: "ERM S n \<subseteq> H" 
  by (simp add: is_arg_min_linorder subset_iff ERM_def)   

lemma ERM_aux: "h' \<in> ERM S m \<Longrightarrow> TrainErr S {0..<m} h' = 0
        \<Longrightarrow> h \<in> ERM S m
        \<Longrightarrow> TrainErr S {0..<m} h = 0"
  unfolding ERM_def using TrainErr_nn
  by (metis is_arg_min_def less_eq_real_def mem_Collect_eq)  

lemma ERMe_minimal: assumes "h' \<in> ERM S m" "TrainErr S {0..<m} h' = 0"
  shows "TrainErr S {0..<m} (ERMe S m) = 0"
  unfolding ERMe_def using ERM_nonempty[OF nnH] ERM_aux[OF assms]
  by (simp add: some_in_eq)  
 
subsection "ERM with finite H is PAC learnable"

text \<open>In this subsection we show that the ERM rule is PAC learnable,
      if we assume a finite hypotheses class H.\<close>

lemma fixes 
      D :: "'a pmf" and f :: "'a \<Rightarrow> 'b"
    and \<epsilon> \<delta> :: real 
    and m :: nat
  assumes
        epos: "\<epsilon> > 0" and m: "real m \<ge> (ln ( real (card H) / \<delta>)) / \<epsilon>" 
      and dd: "\<delta> > 0" "\<delta> < 1"
      and DX: "set_pmf D \<subseteq> X"
      and    "f ` X = Y"
    and RealizabilityAssumption: "\<exists>h'\<in>H. PredErr D f h' = 0"

  shows corollary_2_3_aux: "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>} 
        \<ge> 1 - \<delta>" (is "?LHS \<ge> 1 - \<delta>")
proof -

  text \<open>Fixing some Distribution @{term D} and labelling function @{term f} we are
    interested in upperbounding the probability to sample m-tuple of instances that 
    will lead to failure of the learner.
  
    Formally we would like to upperbound @{term "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>}"}.\<close>

  text \<open>Let ?S be the carrier set of m-times labelled sample pairs (x,f x) from D.\<close>
  let ?S = "set_pmf (Samples m D f)"

  text \<open>Let ?Hb be the set of "bad" hypotheses, that is,\<close>
  let ?Hb = "{h\<in>H. PredErr D f h > \<epsilon>}"

  have fHb: "finite ?Hb" using fH by simp
  from fH have cHb: "card ?Hb \<le> card H"
    by (simp add: card_mono) 

  text \<open>In addition,\<close>
  let ?M = "{S\<in>?S. \<exists>h\<in>?Hb. TrainErr S {0..<m} h = 0}"
  text \<open>be the set of misleading samples: Namely, for every S in M, there is a "bad" hypothesis
        h in H, that looks  like a "good" hypothesis on S.\<close>

  text \<open>We can upperbound the "bad" events (in which we are interested) by ?M:\<close>
  have A: "{S\<in>?S. PredErr D f (ERMe S m) > \<epsilon>} \<subseteq> ?M"
  proof  
    from RealizabilityAssumption  
    obtain h' where h'H: "h'\<in>H" and u: "PredErr D f h' = 0" by blast

    from u have "measure_pmf.prob D {S \<in> set_pmf D. f S \<noteq> h' S} = 0" unfolding PredErr_alt .
    with measure_pmf_zero_iff[of D "{S \<in> set_pmf D. f S \<noteq> h' S}"]       
      have correct: "\<And>x. x\<in>set_pmf D \<Longrightarrow> f x = h' x" by blast 
    
    fix S
    assume "S \<in> {S \<in>?S.   \<epsilon> < PredErr D f (ERMe S m)}" 
    then have SS: "S\<in>?S" and 2: "\<epsilon> < PredErr D f (ERMe S m)" by auto


    from SS set_Pi_pmf[where A="{0..<m}"]
      have "\<And>i. i\<in>{0..<m} \<Longrightarrow> S i \<in> set_pmf (Sample D f)"
        unfolding Samples_def by auto 

    then have tD: "\<And>i. i\<in>{0..<m} \<Longrightarrow> fst (S i) \<in> set_pmf D \<and> f (fst (S i)) = snd (S i)"
      unfolding Sample_def by fastforce+ 

    have z: "\<And>i. i\<in>{0..<m} \<Longrightarrow> (case S i of (x, y) \<Rightarrow> if h' x \<noteq> y then 1::real else 0) = 0"
    proof -
      fix i assume "i\<in>{0..<m}"
      with tD have i: "fst (S i) \<in> set_pmf D" and ii: "f (fst (S i)) = snd (S i)" by auto
      from i correct  have "f (fst (S i))  = h' (fst (S i))" by auto                
      with ii have "h' (fst (S i)) = snd (S i)" by auto
      then show "(case S i of (x, y) \<Rightarrow> if h' x \<noteq> y then 1::real else 0) = 0"
        by (simp add: prod.case_eq_if)
    qed

    have Th'0: "TrainErr S {0..<m} h' = 0" 
      unfolding TrainErr_def   using z  
      by fastforce
    
    with h'H ERM_0_in have h'ERM: "h' \<in> ERM S m" by blast
    then have "TrainErr S {0..<m} (ERMe S m) = 0" using Th'0 by(rule ERMe_minimal)
    have "ERMe S m \<in> H" unfolding ERMe_def using ERM_subset ERM_nonempty
      using nnH some_in_eq by blast  
 
    have "\<exists>h\<in>{h \<in> H. \<epsilon> < PredErr D f h}. TrainErr S {0..<m} h = 0"
      apply(rule bexI[where x="ERMe S m"]) 
       apply auto by fact+ 
    with SS show "S \<in> ?M" by auto
  qed

  text \<open>Note that we can rewrite ?M as\<close>
  have prop_2_5: "?M = (\<Union>h\<in>?Hb. {S\<in>?S. TrainErr S {0..<m} h = 0})"
    by auto

  text \<open>Next, let us bound the probability of the preceding events for each of the inner sets.\<close>
  have prop_2_9: "\<And>h. h\<in>?Hb \<Longrightarrow> measure_pmf.prob (Samples m D f) ({S\<in>?S. TrainErr S {0..<m} h = 0}) \<le> exp (-\<epsilon> * m)"
  proof -
    text \<open>Fix some "bad" hypothesis h:?Hb.\<close>
    fix h
    assume "h\<in>?Hb"
    then have z: "PredErr D f h > \<epsilon>" by auto  

    (* magic ^^, `m>0` seems to follow from `real m \<ge> (ln ( real (card H) / \<delta>)) / \<epsilon>` *)
    from nnH fH have "card H > 0" by auto
    with m have mnn: "m>0" using epos dd
      using fH leD real_of_nat_ge_one_iff by fastforce 
    from mnn have  "finite {0..<m}" "{0..<m} \<noteq>{}" by auto 

    from TrainErr_correct[OF this] have Tc: "\<And>S h i. TrainErr S {0..<m} h = 0 \<Longrightarrow> i \<in> {0..<m} \<Longrightarrow> h (fst (S i)) = snd (S i)" .

    text \<open>We first estimate the probability that the "bad" hypothesis makes a "good" prediction.\<close>
    have individual_estim: "measure_pmf.prob D {x. f x = h x} \<le> exp (-\<epsilon>)"
    proof -
      have "measure_pmf.prob D {x. f x = h x} = 1 - PredErr D f h" (is "?L = ?R") 
      proof - 
        have "?L = measure_pmf.prob D {S \<in> space (measure_pmf D). \<not> (S\<in>{x. f x \<noteq> h x})}"
          by auto  
        also have "\<dots> = 1 - measure_pmf.prob D {x \<in> space (measure_pmf D). x \<in> {x. f x \<noteq> h x}}"
          apply(rule measure_pmf.prob_neg) by simp
        also have "\<dots> = ?R" unfolding PredErr_def by auto
        finally show ?thesis .
      qed 
      also have "\<dots> \<le> 1 - \<epsilon>" using z by force
        (* using the inequality `1-\<epsilon> \<le> exp (-\<epsilon>)` *)
      also have "\<dots> \<le> exp (-\<epsilon>)" using epos
        by (metis add_uminus_conv_diff exp_ge_add_one_self) 
      finally show"measure_pmf.prob D {x. f x = h x} \<le> exp (-\<epsilon>)" .
    qed
 
    have *: "{S \<in> set_pmf (Samples m D f). \<forall>i\<in>{0..<m}. h (fst (S i)) = snd (S i)}
    \<subseteq> {S \<in> set_pmf (Samples m D f). \<forall>i\<in>{0..<m}. f (fst (S i)) = h (fst (S i))}"  
    proof 
      fix S
      assume "S \<in> {S \<in> set_pmf (Samples m D f). \<forall>i\<in>{0..<m}. h (fst (S i)) = snd (S i)} "
      then have S: "S\<in>set_pmf (Samples m D f)" and i: "\<forall>i\<in>{0..<m}. h (fst (S i)) = snd (S i)" by auto
      show "S\<in>{S \<in> set_pmf (Samples m D f). \<forall>i\<in>{0..<m}. f (fst (S i)) = h (fst (S i))}"
      proof (safe) 
        fix i 
        assume ini: "i \<in> {0..<m}" 
         
        have "S i \<in> set_pmf (Sample D f)"
          apply(rule set_Pi_pmf[where A="{0..<m}" and f=S and i=i and dflt="undefined"])
          using S ini by (auto simp: Samples_def)
        then show "f (fst (S i)) = h (fst (S i))" unfolding Sample_def using i ini by auto
      qed fact 
    qed

    have reduce: "measure_pmf.prob (Sample D f) {(x,y). f x = h x}
            = measure_pmf.prob D {x. f x = h x}" unfolding Sample_map 
      apply(subst Probability_Mass_Function.measure_map_pmf) 
      by fastforce 

    \<comment> \<open>The event @{text "L\<^sub>S(h)=0"} is equivalent to the event @{text "\<forall>i. h(x\<^sub>i) = f(x\<^sub>i)"}\<close>
    have "measure_pmf.prob (Samples m D f) {S\<in>?S. TrainErr S {0..<m} h = 0}
        \<le> measure_pmf.prob (Samples m D f) {S\<in>?S. (\<forall>i\<in>{0..<m}. h (fst (S i)) = snd (S i))}"       
      by (auto simp add: Tc intro: measure_pmf.finite_measure_mono)         
    also have "\<dots> \<le> measure_pmf.prob (Samples m D f) {S\<in>?S. (\<forall>i\<in>{0..<m}. f (fst (S i)) = h (fst (S i)))}"
      apply (rule measure_pmf.finite_measure_mono) apply (fact *) by auto
     \<comment> \<open>Since the examples in the training set are sampled i.i.d. we get that:\<close>
    also have "\<dots> \<le> measure_pmf.prob (Samples m D f)  (repeated_event m {(x,y). f x = h x})" (* equality should also be correct, but \<le> takes less effort *)
    proof (rule measure_pmf.finite_measure_mono, safe)
      fix S
      assume S: "S \<in> set_pmf (Samples m D f)"
      then have 1: "\<And>x. x \<notin> {0..<m} \<Longrightarrow> S x = undefined"
        using set_Pi_pmf_subset[of "{0..<m}" undefined "(\<lambda>_. Sample D f)"] unfolding Samples_def
        by blast
      assume A: "\<forall>i\<in>{0..<m}. f (fst (S i)) = h (fst (S i))"
      { fix i
        assume i: "i \<in> {0..<m}"
        with  set_Pi_pmf[OF _ S[unfolded Samples_def]] have Si: "S i \<in> set_pmf (Sample D f)" by auto
        fix x y assume "S i = (x,y)"
        with Si 
        have "f x = h x" unfolding Sample_def using A i by force
      } note 2=this      
      show "S \<in> repeated_event m {(x, y). f x = h x}" unfolding repeated_event_def PiE_dflt_def apply safe by (fact 1 2)+
    qed simp
    also have "\<dots> = (measure_pmf.prob (Sample D f) {(x,y). f x = h x}) ^ m" 
      by(rule iid)
    also have "\<dots> = (measure_pmf.prob D {x. f x = h x}) ^ m" 
      by(simp only: reduce)
    \<comment> \<open>by estimating each individual sampling we obtain\<close>
    also have "\<dots> \<le>  (exp (-\<epsilon>)) ^ m"
        apply(rule power_mono) apply(fact individual_estim) by auto
    also have "\<dots> \<le> exp (-\<epsilon> * m)"
      by (metis exp_of_nat2_mult order_refl) 
    finally show "measure_pmf.prob (Samples m D f) ({S\<in>?S. TrainErr S {0..<m} h = 0}) \<le> exp (-\<epsilon> * m)" .
  qed


          
  text "now we can plug all the estimations together:"

  have "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) > \<epsilon>}
      = measure_pmf.prob (Samples m D f) {S\<in>?S. PredErr D f (ERMe S m) > \<epsilon>}"
    by (auto intro: pmf_prob_cong simp add: set_pmf_iff) 
  \<comment> \<open>the overapproximation by ?M:\<close>
  also have "\<dots> \<le> measure_pmf.prob (Samples m D f) ?M"
    apply(rule measure_pmf.finite_measure_mono) apply (fact A) by auto   
  \<comment> \<open>the rewrite of ?M as a big Union:\<close>
  also have "\<dots> = measure_pmf.prob (Samples m D f) (\<Union>h\<in>?Hb. {S\<in>?S. TrainErr S {0..<m} h = 0})" 
    using prop_2_5 by auto 
  \<comment> \<open>bounding the probability of a Union of events by the sum of the probability of the events:\<close>
  also have "\<dots> \<le> sum (\<lambda>h. measure_pmf.prob (Samples m D f) ({S\<in>?S. TrainErr S {0..<m} h = 0})) ?Hb"
      apply(rule measure_pmf.finite_measure_subadditive_finite) using fHb by auto
  \<comment> \<open>applying the estimation:\<close>
  also have "\<dots> \<le> sum (\<lambda>h. exp (-\<epsilon> * m)) ?Hb"
    apply(rule sum_mono) using prop_2_9  by blast
  \<comment> \<open>some final rewrites:\<close>
  also have "\<dots> \<le> (card ?Hb) * exp (-\<epsilon> * m)" using fHb by auto
  also have "\<dots> \<le> (card H) * exp (-\<epsilon> * m)" using cHb by simp
  finally have k: "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) > \<epsilon>} \<le> (card H) * exp (-\<epsilon> * m)" .

  text \<open>solve the bound for m for \<delta>\<close>
  from nnH fH have nn: "0 < real (card H)" by fastforce 
  note bound = \<open>m \<ge> (ln ( card H / \<delta>)) / \<epsilon>\<close>
  from aux_estim[OF nn epos bound dd]
    have ed: "(card H) * exp (-\<epsilon> * m) \<le> \<delta>" by auto

  text \<open>Put everything together to yield the final result:\<close>
  have "1 - \<delta> \<le> 1 - (card H) * exp (-\<epsilon> * m)" using ed by simp
  also have "\<dots> \<le> 1 - measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) > \<epsilon>}"
    using k by linarith
  also have "\<dots> = ?LHS" (is "?R = _")
  proof -
    thm measure_pmf.prob_neg
    have "?LHS = measure_pmf.prob (Samples m D f) {S \<in> space (measure_pmf (Samples m D f)). \<not> (S\<in>{S. \<epsilon> < PredErr D f (ERMe S m)})}"
      apply auto  by (meson not_le)
    also have "\<dots> = 1 - measure_pmf.prob (Samples m D f) {x \<in> space (measure_pmf (Samples m D f)). x \<in> {S. \<epsilon> < PredErr D f (ERMe S m)}}"
      apply(rule measure_pmf.prob_neg) by simp
    also have "\<dots> = ?R" by auto
    finally show ?thesis by simp
  qed 
  finally show "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>" by simp
qed

definition "ERMbound \<epsilon> \<delta> = nat \<lceil> (ln ( real (card H) / \<delta>)) / \<epsilon>\<rceil>"

lemma corollary_2_3: "PAC_learnable H ERMe"
  unfolding PAC_learnable_def
  apply(rule exI[where x="ERMbound"])
  apply safe unfolding ERMbound_def
  using corollary_2_3_aux  by fastforce

end

end