theory FiniteHypClasses
  imports "HOL-Probability.Probability" Pi_pmf LearningTheory
begin

section "auxiliary lemmas"



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



section "finite Hypothesis classes are PAC learnable"    

(* now assume we have a finite class of Hypotheses *)
locale finiteHypothesisClass = learning_basics where X=X and Y=Y and H = H 
  for X::"'a set" and Y::"'b set" and H :: "('a \<Rightarrow> 'b) set" +
  assumes fH: "finite H"
begin


text \<open>Let us now analyze the performance of the "Empirical Risk Minimization" rule
w.r.t. to the finite Hypothesis Class H.
Its learning rule ERMe chooses for a given training set S an Hypothesis h from H
which minimizes the Training Error. \<close>

lemma ERM_nonempty: "H\<noteq>{} \<Longrightarrow> ERM S n \<noteq> {}" unfolding ERM_def 
  by (simp add: ex_is_arg_min_if_finite fH)


text \<open>Now we show that the ERM rule is PAC learnable,
      if we assume a finite hypotheses class H.\<close>

lemma fixes 
      D :: "('a\<times>'b) pmf"
    and \<epsilon> \<delta> :: real 
    and m :: nat
  assumes
        epos: "\<epsilon> > 0" and m: "real m \<ge> (ln ( real (card H) / \<delta>)) / \<epsilon>" 
      and dd: "\<delta> > 0" "\<delta> < 1"
      and DX: "set_pmf D \<subseteq> (X\<times>Y)"
    and RealizabilityAssumption: "\<exists>h'\<in>H. PredErr D h' = 0"

  shows corollary_2_3_aux: "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>} 
        \<ge> 1 - \<delta>" (is "?LHS \<ge> 1 - \<delta>")
proof -

  text \<open>Fixing some Distribution @{term D} we are
    interested in upperbounding the probability to sample m-tuple of instances that 
    will lead to failure of the learner.
  
    Formally we would like to upperbound @{term "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>}"}.\<close>

  text \<open>Let ?S be the carrier set of m-times labelled sample pairs (x,f x) from D.\<close>
  let ?S = "set_pmf (Samples m D)"

  text \<open>Let ?Hb be the set of "bad" hypotheses, that is,\<close>
  let ?Hb = "{h\<in>H. PredErr D h > \<epsilon>}"

  have fHb: "finite ?Hb" using fH by simp
  from fH have cHb: "card ?Hb \<le> card H"
    by (simp add: card_mono) 

  text \<open>In addition,\<close>
  let ?M = "{S\<in>?S. \<exists>h\<in>?Hb. TrainErr S {0..<m} h = 0}"
  text \<open>be the set of misleading samples: Namely, for every S in M, there is a "bad" hypothesis
        h in H, that looks  like a "good" hypothesis on S.\<close>

  text \<open>We can upperbound the "bad" events (in which we are interested) by ?M:\<close>
  have A: "{S\<in>?S. PredErr D (ERMe S m) > \<epsilon>} \<subseteq> ?M"
  proof  
    from RealizabilityAssumption  
    obtain h' where h'H: "h'\<in>H" and u: "PredErr D h' = 0" by blast

    from u have "measure_pmf.prob D {S \<in> set_pmf D. snd S \<noteq> h' (fst S)} = 0" unfolding PredErr_alt .
    with measure_pmf_zero_iff[of D "{S \<in> set_pmf D. snd S \<noteq> h' (fst S)}"]       
    have correct: "\<And>x. x\<in>set_pmf D \<Longrightarrow> snd x = h' (fst x)" by blast
    
    fix S
    assume "S \<in> {S \<in>?S.   \<epsilon> < PredErr D (ERMe S m)}" 
    then have SS: "S\<in>?S" and 2: "\<epsilon> < PredErr D (ERMe S m)" by auto


    from SS set_Pi_pmf[where A="{0..<m}"]
      have tD: "\<And>i. i\<in>{0..<m} \<Longrightarrow> S i \<in> set_pmf D"
        unfolding Samples_def by auto 


      have z: "\<And>i. i\<in>{0..<m} \<Longrightarrow> (case S i of (x, y) \<Rightarrow> if h' x \<noteq> y then 1::real else 0) = 0"
        using tD correct
        by (simp add: case_prod_beta') 


    have Th'0: "TrainErr S {0..<m} h' = 0" 
      unfolding TrainErr_def   using z  
      by fastforce
    
    with h'H ERM_0_in have h'ERM: "h' \<in> ERM S m" by blast
    then have "TrainErr S {0..<m} (ERMe S m) = 0" using Th'0 by(rule ERMe_minimal)
    have "ERMe S m \<in> H" unfolding ERMe_def using ERM_subset ERM_nonempty
      using nnH some_in_eq by blast  
 
    have "\<exists>h\<in>{h \<in> H. \<epsilon> < PredErr D h}. TrainErr S {0..<m} h = 0"
      apply(rule bexI[where x="ERMe S m"]) 
       apply auto by fact+ 
    with SS show "S \<in> ?M" by auto
  qed

  text \<open>Note that we can rewrite ?M as\<close>
  have prop_2_5: "?M = (\<Union>h\<in>?Hb. {S\<in>?S. TrainErr S {0..<m} h = 0})"
    by auto

  text \<open>Next, let us bound the probability of the preceding events for each of the inner sets.\<close>
  have prop_2_9: "\<And>h. h\<in>?Hb \<Longrightarrow> measure_pmf.prob (Samples m D) ({S\<in>?S. TrainErr S {0..<m} h = 0}) \<le> exp (-\<epsilon> * m)"
  proof -
    text \<open>Fix some "bad" hypothesis h:?Hb.\<close>
    fix h
    assume "h\<in>?Hb"
    then have z: "PredErr D h > \<epsilon>" by auto  

    (* magic ^^, `m>0` seems to follow from `real m \<ge> (ln ( real (card H) / \<delta>)) / \<epsilon>` *)
    from nnH fH have "card H > 0" by auto
    with m have mnn: "m>0" using epos dd
      using fH leD real_of_nat_ge_one_iff by fastforce 
    from mnn have  "finite {0..<m}" "{0..<m} \<noteq>{}" by auto 

    from TrainErr_correct[OF this] have Tc: "\<And>S h i. TrainErr S {0..<m} h = 0 \<Longrightarrow> i \<in> {0..<m} \<Longrightarrow> h (fst (S i)) = snd (S i)" .

    text \<open>We first estimate the probability that the "bad" hypothesis makes a "good" prediction.\<close>
    have individual_estim: "measure_pmf.prob D {x. snd x = h (fst x)} \<le> exp (-\<epsilon>)"
    proof -
      have "measure_pmf.prob D {x. snd x = h (fst x)} = 1 - PredErr D h" (is "?L = ?R") 
      proof - 
        have "?L = measure_pmf.prob D {S \<in> space (measure_pmf D). \<not> (S\<in>{x. snd x \<noteq> h (fst x)})}"
          by auto  
        also have "\<dots> = 1 - measure_pmf.prob D {x \<in> space (measure_pmf D). x \<in> {x. snd x \<noteq> h (fst x)}}"
          apply(rule measure_pmf.prob_neg) by simp
        also have "\<dots> = ?R" unfolding PredErr_def by auto
        finally show ?thesis .
      qed 
      also have "\<dots> \<le> 1 - \<epsilon>" using z by force
        (* using the inequality `1-\<epsilon> \<le> exp (-\<epsilon>)` *)
      also have "\<dots> \<le> exp (-\<epsilon>)" using epos
        by (metis add_uminus_conv_diff exp_ge_add_one_self) 
      finally show"measure_pmf.prob D {x. snd x = h (fst x)} \<le> exp (-\<epsilon>)" .
    qed
 
   
    \<comment> \<open>The event @{text "L\<^sub>S(h)=0"} is equivalent to the event @{text "\<forall>i. h(x\<^sub>i) = f(x\<^sub>i)"}\<close>
    have "measure_pmf.prob (Samples m D) {S\<in>?S. TrainErr S {0..<m} h = 0}
        \<le> measure_pmf.prob (Samples m D) {S\<in>?S. (\<forall>i\<in>{0..<m}. snd (S i) = h (fst (S i)))}"       
      by (auto simp add: Tc intro: measure_pmf.finite_measure_mono)         
     \<comment> \<open>Since the examples in the training set are sampled i.i.d. we get that:\<close>
    also have "\<dots> \<le> measure_pmf.prob (Samples m D)  (repeated_event m {(x,y). y = h x})" (* equality should also be correct, but \<le> takes less effort *)
    proof (rule measure_pmf.finite_measure_mono, safe)
      fix S
      assume S: "S \<in> set_pmf (Samples m D)"
      then have 1: "\<And>x. x \<notin> {0..<m} \<Longrightarrow> S x = undefined"
        using set_Pi_pmf_subset[of "{0..<m}" undefined "(\<lambda>_. D)"] unfolding Samples_def
        by blast
      assume A: "\<forall>i\<in>{0..<m}. (snd (S i)) = h (fst (S i))"
      { fix i
        assume i: "i \<in> {0..<m}"
        with  set_Pi_pmf[OF _ S[unfolded Samples_def]] have Si: "S i \<in> set_pmf D" by auto
        fix x y assume "S i = (x,y)"
        with Si 
        have "y = h x" unfolding Sample_def using A i by force
      } note 2=this      
      show "S \<in> repeated_event m {(x, y). y = h x}" unfolding repeated_event_def PiE_dflt_def apply safe by (fact 1 2)+
    qed simp
    also have "\<dots> = (measure_pmf.prob D {(x,y). y = h x}) ^ m" 
      by(rule iid)
   (* also have "\<dots> = (measure_pmf.prob D {x. f x = h x}) ^ m" 
      by(simp only: reduce) *)
    \<comment> \<open>by estimating each individual sampling we obtain\<close>
    also have "\<dots> \<le>  (exp (-\<epsilon>)) ^ m"
        apply(rule power_mono)
       apply (metis (mono_tags, lifting) Collect_cong case_prod_beta individual_estim)
      by auto
    also have "\<dots> \<le> exp (-\<epsilon> * m)"
      by (metis exp_of_nat2_mult order_refl) 
    finally show "measure_pmf.prob (Samples m D) ({S\<in>?S. TrainErr S {0..<m} h = 0}) \<le> exp (-\<epsilon> * m)" .
  qed


          
  text "now we can plug all the estimations together:"

  have "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) > \<epsilon>}
      = measure_pmf.prob (Samples m D) {S\<in>?S. PredErr D (ERMe S m) > \<epsilon>}"
    by (auto intro: pmf_prob_cong simp add: set_pmf_iff) 
  \<comment> \<open>the overapproximation by ?M:\<close>
  also have "\<dots> \<le> measure_pmf.prob (Samples m D) ?M"
    apply(rule measure_pmf.finite_measure_mono) apply (fact A) by auto   
  \<comment> \<open>the rewrite of ?M as a big Union:\<close>
  also have "\<dots> = measure_pmf.prob (Samples m D) (\<Union>h\<in>?Hb. {S\<in>?S. TrainErr S {0..<m} h = 0})" 
    using prop_2_5 by auto 
  \<comment> \<open>bounding the probability of a Union of events by the sum of the probability of the events:\<close>
  also have "\<dots> \<le> sum (\<lambda>h. measure_pmf.prob (Samples m D) ({S\<in>?S. TrainErr S {0..<m} h = 0})) ?Hb"
      apply(rule measure_pmf.finite_measure_subadditive_finite) using fHb by auto
  \<comment> \<open>applying the estimation:\<close>
  also have "\<dots> \<le> sum (\<lambda>h. exp (-\<epsilon> * m)) ?Hb"
    apply(rule sum_mono) using prop_2_9  by blast
  \<comment> \<open>some final rewrites:\<close>
  also have "\<dots> \<le> (card ?Hb) * exp (-\<epsilon> * m)" using fHb by auto
  also have "\<dots> \<le> (card H) * exp (-\<epsilon> * m)" using cHb by simp
  finally have k: "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) > \<epsilon>} \<le> (card H) * exp (-\<epsilon> * m)" .

  text \<open>solve the bound for m for \<delta>\<close>
  from nnH fH have nn: "0 < real (card H)" by fastforce 
  note bound = \<open>m \<ge> (ln ( card H / \<delta>)) / \<epsilon>\<close>
  from aux_estim[OF nn epos bound dd]
    have ed: "(card H) * exp (-\<epsilon> * m) \<le> \<delta>" by auto

  text \<open>Put everything together to yield the final result:\<close>
  have "1 - \<delta> \<le> 1 - (card H) * exp (-\<epsilon> * m)" using ed by simp
  also have "\<dots> \<le> 1 - measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) > \<epsilon>}"
    using k by linarith
  also have "\<dots> = ?LHS" (is "?R = _")
  proof -
    thm measure_pmf.prob_neg
    have "?LHS = measure_pmf.prob (Samples m D) {S \<in> space (measure_pmf (Samples m D)). \<not> (S\<in>{S. \<epsilon> < PredErr D (ERMe S m)})}"
      apply auto  by (meson not_le)
    also have "\<dots> = 1 - measure_pmf.prob (Samples m D) {x \<in> space (measure_pmf (Samples m D)). x \<in> {S. \<epsilon> < PredErr D (ERMe S m)}}"
      apply(rule measure_pmf.prob_neg) by simp
    also have "\<dots> = ?R" by auto
    finally show ?thesis by simp
  qed 
  finally show "measure_pmf.prob (Samples m D) {S. PredErr D (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>" by simp
qed

definition "ERMbound \<epsilon> \<delta> = nat \<lceil> (ln ( real (card H) / \<delta>)) / \<epsilon>\<rceil>"

lemma corollary_2_3: "PAC_learnable ERMe"
  unfolding PAC_learnable_def
  apply(rule exI[where x="ERMbound"])
  apply safe unfolding ERMbound_def
  using corollary_2_3_aux  by fastforce

end

end