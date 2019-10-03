theory NewTry
imports LearningTheory
begin

                  

lemma expectation_pair_pmf:
    "measure_pmf.expectation (pair_pmf p q) f
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda>y. f (x, y)))"
  using nn_integral_pair_pmf'
  sorry

lemma 
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"
  shows expectation_Pi_pmf_prod:
    "finite A \<Longrightarrow>  measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. prod (\<lambda>x. f x (y x)) A) =
    (prod (\<lambda>x. measure_pmf.expectation (p x) (\<lambda>v. f x v)) A)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert a A) 
  have p: "\<And>x y. (\<Prod>xa\<in>A. f xa (if xa = a then x else y xa)) = (\<Prod>xa\<in>A. f xa (y xa))"
    apply(rule prod.cong) apply simp using insert by auto
 

  have "measure_pmf.expectation (Pi_pmf (insert a A) dflt p) (\<lambda>y. \<Prod>x\<in>insert a A. f x (y x))
        = measure_pmf.expectation (p a) (\<lambda>x. f a x * measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Prod>xa\<in>A. f xa (y xa)))"
    apply(subst Pi_pmf_insert) apply fact apply fact
    apply simp thm integral_mult_left_zero integral_map_pmf
    unfolding expectation_pair_pmf
    apply(subst prod.insert) apply fact apply fact
    apply simp unfolding p by simp
  also have "\<dots> = (\<Prod>x\<in>insert a A. measure_pmf.expectation (p x) (f x))"
    apply(subst insert(3))
    apply(subst prod.insert) apply fact apply fact by simp
  finally  show ?case .
qed

(*
lemma expectation_Pi_pmf_sum:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"
  assumes [simp]: "finite A"
  shows   "measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Sum>x\<in>A. (f x) (y x)) =
             (\<Sum>x\<in>A. measure_pmf.expectation (p x) (f x))" 
  using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert a A) 
  have p: "\<And>x y. (\<Sum>xa\<in>A. f xa (if xa = a then x else y xa)) = (\<Sum>xa\<in>A. f xa (y xa))"
    apply(rule sum.cong) apply simp using insert by auto

  have "measure_pmf.expectation (Pi_pmf (insert a A) dflt p) (\<lambda>y. \<Sum>x\<in>insert a A. f x (y x))
        = measure_pmf.expectation (p a) (\<lambda>x. f a x + measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Sum>xa\<in>A. f xa (y xa)))"
    apply(subst Pi_pmf_insert) apply fact apply fact
    apply(subst integral_map_pmf)
    apply(subst  Bochner_Integration.integral_add)
    subgoal sorry
    subgoal sorry
    apply simp
    unfolding expectation_pair_pmf
    apply(subst sum.insert) apply fact apply fact
    apply simp
    apply(subst  Bochner_Integration.integral_add)
    subgoal sorry
    subgoal sorry
    apply(subst  Bochner_Integration.integral_add)
    subgoal sorry
    subgoal sorry    
    unfolding p by simp
  also have "\<dots> = (\<Sum>x\<in>insert a A. measure_pmf.expectation (p x) (f x))"
    apply(subst insert(3))
    apply(subst sum.insert) apply fact apply fact 
    apply(subst  Bochner_Integration.integral_add)
    subgoal sorry
    subgoal sorry
    by simp 
  finally  show ?case .
qed
  *)


 
lemma Pi_pmf_map2:
  assumes [simp]: "finite A" and "\<And>x. x\<notin>A \<Longrightarrow> f x dflt = dflt'"
  shows   "Pi_pmf A dflt' (\<lambda>x. map_pmf (f x) (g x)) = map_pmf (\<lambda>h. (\<lambda>x. (f x) (h x))) (Pi_pmf A dflt g)"
    (is "?lhs = ?rhs")
proof (rule pmf_eqI)
  fix h
  show "pmf ?lhs h = pmf ?rhs h"
  proof (cases "\<forall>x. x \<notin> A \<longrightarrow> h x = dflt'")
    case True
    hence "pmf ?lhs h = (\<Prod>x\<in>A. measure_pmf.prob (g x) (f x -` {h x}))"
      by (subst pmf_Pi) (auto simp: pmf_map)
    also have "\<dots> = measure_pmf.prob (Pi_pmf A dflt g) (PiE_dflt A dflt (\<lambda>x. f x -` {h x}))"
      by (rule measure_Pi_pmf_PiE_dflt [symmetric]) auto
    also have "PiE_dflt A dflt (\<lambda>x. f x -` {h x}) = ((\<lambda>g x. f x (g x))  -` {h}) \<inter> PiE_dflt A dflt (\<lambda>_. UNIV)"
      using True by (fastforce simp: assms(2) [symmetric] fun_eq_iff PiE_dflt_def o_def)
    also have "measure_pmf.prob (Pi_pmf A dflt g) \<dots> = 
                 measure_pmf.prob (Pi_pmf A dflt g) ((\<lambda>g x. f x (g x)) -` {h})"
      by (intro pmf_prob_cong) (auto simp: PiE_dflt_def pmf_Pi_outside)
    also have "\<dots> = pmf ?rhs h" by (simp add: pmf_map)
    finally show ?thesis .
  next
    case False
    have "pmf ?rhs h = infsetsum (pmf (Pi_pmf A dflt g)) ((\<lambda>g x. f x (g x)) -` {h})"
      by (simp add: pmf_map measure_pmf_conv_infsetsum)
    also from False have "\<dots> = infsetsum (\<lambda>_. 0) ((\<lambda>g x. f x (g x)) -` {h})"
      by (intro infsetsum_cong pmf_Pi_outside) (auto simp: fun_eq_iff o_def assms(2) [symmetric])
    also have "\<dots> = 0" by simp
    also from False have "\<dots> = pmf ?lhs h"
      by (subst pmf_Pi_outside) auto
    finally show ?thesis ..
  qed
qed




definition "mapify f = (\<lambda>x. Some (f x))"
definition "allmaps C D = {m. dom m = C \<and> ran m \<subseteq> D}"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"




lemma "H\<noteq>{} \<Longrightarrow> card C \<ge> 1 \<Longrightarrow> card D \<ge> 2 \<Longrightarrow> card (restrictH H C D) \<ge> 4"
  oops

lemma finitemaps: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (allmaps C D)"
  by (simp add: allmaps_def finite_set_of_finite_maps)

lemma finiteres: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (restrictH H C D)"
  by (simp add: finitemaps restrictH_def)

lemma auxtemp: "\<forall>h\<in>H. dom h = UNIV \<Longrightarrow> \<forall>h\<in>H. ran h \<subseteq> D \<Longrightarrow> restrictH H C D = (\<lambda>h. restrict_map h C) ` H" 
proof safe
  fix m
  assume "m \<in> restrictH H C D"
  then have s1: "dom m = C"
    by (simp add: allmaps_def restrictH_def)
  moreover obtain h where o1: "h\<in>H" "m \<subseteq>\<^sub>m h" using restrictH_def
proof -
assume a1: "\<And>h. \<lbrakk>h \<in> H; m \<subseteq>\<^sub>m h\<rbrakk> \<Longrightarrow> thesis"
  have "m \<in> {f \<in> allmaps C D. \<exists>fa. fa \<in> H \<and> f \<subseteq>\<^sub>m fa}"
    using \<open>m \<in> restrictH H C D\<close> restrictH_def by blast
then show ?thesis
  using a1 by blast
qed

  ultimately have "\<forall>x\<in>C. m x = h x"
    by (simp add: map_le_def)
  then have "\<forall>x. m x = (h |` C) x" using s1
    by (metis domIff restrict_map_def)
  then have "m = h |` C" by auto
  then show "m\<in>(\<lambda>h. h |` C) ` H" using o1(1) by auto
next
  fix h
  assume a1: "h\<in>H" "\<forall>h\<in>H. ran h \<subseteq> D" "\<forall>h\<in>H. dom h = UNIV"
  then have "ran (h |` C) \<subseteq> D"
    by (meson ranI ran_restrictD subsetI subset_eq)
  moreover have "dom (h |` C) = C" by (simp add: a1)
  then show "h |` C \<in> restrictH H C D"
    by (metis (mono_tags, lifting) a1(1) allmaps_def calculation map_le_def
        mem_Collect_eq restrictH_def restrict_in) 
qed


locale vcd =learning_basics where X=X and Y=Y and H=H
  for X::"'a set" and Y::"'b set" and H :: "('a \<Rightarrow> 'b) set" +
assumes infx: "infinite X"
begin




abbreviation "H_map \<equiv> image mapify H"


definition "growth m = Max {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"

theorem growth_mono: "m \<le> m' \<Longrightarrow> growth m \<le> growth m'"
  (* maybe one needs infinite X here *)
  sorry

lemma "card X \<noteq> 0 \<Longrightarrow> growth m > 1"
proof -
  assume "card X \<noteq> 0"
  then have "X \<noteq> {}" by auto
  then obtain x where "x\<in>X" by blast
  
  show ?thesis 
    unfolding growth_def sorry
qed


term measure_pmf.expectation 

lemma nn_integral_Markov_inequality_strict:
  assumes u: "u \<in> borel_measurable M" and "A \<in> sets M"
  shows "(emeasure M) ({x\<in>space M. 1 < c * u x} \<inter> A) \<le> c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    (is "(emeasure M) ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using \<open>A \<in> sets M\<close> u by auto
  hence "(emeasure M) ?A = (\<integral>\<^sup>+ x. indicator ?A x \<partial>M)"
    using nn_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^sup>+ x. c * (u x * indicator A x) \<partial>M)"
    using u apply (auto intro!: nn_integral_mono_AE simp: indicator_def) by auto
  also have "\<dots> = c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    using assms by (auto intro!: nn_integral_cmult)
  finally show ?thesis .
qed

lemma integral_Markov_inequality_strict:
  assumes [measurable]: "integrable M u" and "AE x in M. 0 \<le> u x" "0 < (c::real)"
  shows "(emeasure M) {x\<in>space M. u x > c} \<le> (1/c) * (\<integral>x. u x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+ x. ennreal(u x) * indicator (space M) x \<partial>M) \<le> (\<integral>\<^sup>+ x. u x \<partial>M)"
    by (rule nn_integral_mono_AE, auto simp add: \<open>c>0\<close> less_eq_real_def)
  also have "... = (\<integral>x. u x \<partial>M)"
    by (rule nn_integral_eq_integral, auto simp add: assms)
  finally have *: "(\<integral>\<^sup>+ x. ennreal(u x) * indicator (space M) x \<partial>M) \<le> (\<integral>x. u x \<partial>M)"
    by simp

  have "{x \<in> space M. u x > c} = {x \<in> space M. ennreal(1/c) * u x > 1} \<inter> (space M)"
    using \<open>c>0\<close> by (auto simp: ennreal_mult'[symmetric])
  then have "emeasure M {x \<in> space M. u x > c} = emeasure M ({x \<in> space M. ennreal(1/c) * u x > 1} \<inter> (space M))"
    by simp
  also have "... \<le> ennreal(1/c) * (\<integral>\<^sup>+ x. ennreal(u x) * indicator (space M) x \<partial>M)"
    by (rule nn_integral_Markov_inequality_strict) (auto simp add: assms)
  also have "... \<le> ennreal(1/c) * (\<integral>x. u x \<partial>M)"
    apply (rule mult_left_mono) using * \<open>c>0\<close> by auto
  finally show ?thesis
    using \<open>0<c\<close> by (simp add: ennreal_mult'[symmetric])
qed


lemma markov_inequality:
  assumes 
      b: "integrable (measure_pmf D) f"
    and pos: "AE x in measure_pmf D. 0 \<le> f x"
    and apos: "a>0"
  shows 
  "measure_pmf.prob D {x. f x > a} \<le> (measure_pmf.expectation D f / a)"
proof -
  have "measure_pmf.expectation D f \<ge> 0"
    apply(rule integral_nonneg_AE) apply(rule pos) done
  then have a: "0 \<le> measure_pmf.expectation D f / a"
    apply(rule divide_nonneg_pos) using apos .

  have "ennreal (measure_pmf.prob D {x. f x > a})
        = emeasure (measure_pmf D) {x. a < f x}"
    unfolding measure_pmf.emeasure_eq_measure[symmetric] ..
  also have "\<dots>  = emeasure (measure_pmf D) {x\<in> space (measure_pmf D). a < f x}"
    by simp
  also have "\<dots> \<le> ennreal (1 / a * measure_pmf.expectation D f)" 
    apply(rule integral_Markov_inequality_strict)
    apply(fact b) apply (fact pos) apply (fact apos) done
  finally have"ennreal (measure_pmf.prob D {x. f x > a})
        \<le> ennreal (1 / a * measure_pmf.expectation D f)" .
  then show ?thesis apply simp
    apply(subst (asm) ennreal_le_iff) apply (fact a) by simp
qed 
 
thm integral_Markov_inequality[where c=a and u=f and M=D] measure_pmf.emeasure_eq_measure  integral_real_bounded
thm ennreal_le_iff

lemma markov_inequality':
  "
  integrable (measure_pmf D) f \<Longrightarrow>
  AE x in measure_pmf D. 0 \<le> f x \<Longrightarrow> a>0 \<Longrightarrow> measure_pmf.prob D {x. f x \<ge> a} \<le> (measure_pmf.expectation D f / a)"
  using integral_Markov_inequality[where c=a and u=f and M=D, unfolded measure_pmf.emeasure_eq_measure] 
  apply(subst (asm) ennreal_le_iff)
    sorry


thm integral_Markov_inequality
thm integral_Markov_inequality
thm nn_integral_Markov_inequality

   

lemma A :
  fixes a b :: real
  shows "a\<ge>1-b \<Longrightarrow> 1-a\<le>b" by auto

lemma "abs(PredErr D h - TrainErr S {0..<m} h) \<ge> 0"
  by auto

lemma abs_bound_neg: "\<And>a b :: real. b\<ge>0 \<Longrightarrow> abs a \<le> b \<Longrightarrow> -b \<le> a"  by auto
lemma abs_bound_pos: "\<And>a b :: real. b\<ge>0 \<Longrightarrow> abs a \<le> b \<Longrightarrow> a \<le> b"  by auto

lemma assumes mgt0: "m>0"
  shows TError_bounded: "abs(TrainErr S' {0..<m::nat} h - TrainErr S {0..<m::nat} h) \<le> 2"
proof - 
  have T: "\<And>S. abs(TrainErr S {0..<m} h) \<le> 1" using TrainErr_nn 
    apply(subst abs_of_nonneg) using mgt0 by (auto intro!: TrainErr_le1) 
  have "abs(TrainErr S' {0..<m::nat} h - TrainErr S {0..<m} h)
        \<le> abs(TrainErr S' {0..<m::nat} h) + abs (TrainErr S {0..<m} h)"
    by(rule abs_triangle_ineq4)
  also have "\<dots> \<le> 2" apply(rule order.trans) apply(rule add_mono) apply(rule T)+ by simp
  finally show ?thesis .
qed 


lemma assumes mgt0: "m>0"
  shows Error_bounded: "abs(PredErr D h - TrainErr S {0..<m::nat} h) \<le> 2"
proof -
  have P: "abs(PredErr D h) \<le> 1" using PredErr_nn PredErr_le1
    apply(subst abs_of_nonneg) by auto  
  have T: "abs(TrainErr S {0..<m} h) \<le> 1" using TrainErr_nn 
    apply(subst abs_of_nonneg) using mgt0 by (auto intro!: TrainErr_le1) 
  have "abs(PredErr D h - TrainErr S {0..<m} h)
        \<le> abs(PredErr D h) + abs (TrainErr S {0..<m} h)"
    by(rule abs_triangle_ineq4)
  also have "\<dots> \<le> 2" using P T by simp
  finally show ?thesis .
qed

 

lemma PredErr_as_expectation:
  "PredErr D h = measure_pmf.expectation (Samples m D) (\<lambda>S. TrainErr S {0..<m} h )"
  unfolding PredErr_def unfolding TrainErr_def sorry 



term measure

definition E :: "real pmf \<Rightarrow> real"  where
  "E M = (\<integral>x. x \<partial> measure_pmf M)"
term prob_space
(* abbreviation (in prob_space) "expectation \<equiv> integral\<^sup>L M" 
    abbreviation (in prob_space) "prob \<equiv> measure M" *)
lemma "E M = measure_pmf.expectation M id"
  unfolding E_def         
  by (metis comp_id fun.map_ident)  

lemma "E (map_pmf f M) = measure_pmf.expectation M f"
  unfolding E_def       
  by simp   
 
lemma expectation_mono:
  fixes f::"'c \<Rightarrow> real"
  shows 
    "integrable (measure_pmf M) f \<Longrightarrow>
    integrable (measure_pmf M) u \<Longrightarrow> (\<And>x. x\<in>set_pmf M \<Longrightarrow> f x \<le> u x) \<Longrightarrow> measure_pmf.expectation M f \<le> measure_pmf.expectation M u"
  apply(rule integral_mono_AE)
by (auto simp add: AE_measure_pmf_iff)


lemma expectation_const: "measure_pmf.expectation M (\<lambda>_. c::real) = c" 
  by simp 

lemma E_cong:
  fixes f::"'a \<Rightarrow> real"
  shows "(\<forall>x\<in> set_pmf S. (f x) = (u x)) \<Longrightarrow> E (map_pmf f S) = E (map_pmf u S)"
unfolding E_def integral_map_pmf apply(rule integral_cong_AE)
apply(simp add: integrable_measure_pmf_finite)+
by (simp add: AE_measure_pmf_iff)

lemma expectation_cong: "(\<And>m. m\<in>set_pmf M \<Longrightarrow> f m = g m) \<Longrightarrow> measure_pmf.expectation M f = measure_pmf.expectation M g"
  by (rule integral_cong_AE, simp_all add: AE_measure_pmf_iff) 


lemma expectation_Sup_le:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"
  assumes Hnn: "H\<noteq>{}"  
   and 2: "\<And>x. x \<in> H \<Longrightarrow> integrable (measure_pmf D) (f x)"
   and 3: "\<And>x. x \<in> H \<Longrightarrow> integrable (measure_pmf D) (\<lambda>S'. \<Squnion>h\<in>H. f h S')" (* could be deduced from 2 and a stronger 4 *)
   and 4: "\<And>d. d \<in> set_pmf D \<Longrightarrow> bdd_above ((\<lambda>h. f h d) ` H)"
  shows  "(\<Squnion>h\<in>H. measure_pmf.expectation D (f h))
         \<le> measure_pmf.expectation D (\<lambda>S'. \<Squnion>h\<in>H. f h S')"
proof -  
  show ?thesis  apply(rule cSUP_least)
    subgoal using Hnn by auto
  proof -
    fix x
    assume "x\<in>H"
    then show "measure_pmf.expectation D (f x) \<le> measure_pmf.expectation D (\<lambda>S'. \<Squnion>h\<in>H. f h S')"
      apply(intro expectation_mono)
      subgoal using 2 by simp
      subgoal using 3 by simp
      subgoal for d apply(rule cSUP_upper)
        apply simp using 4 by simp
      done
  qed
qed


lemma nn_integral_Sup_le:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> real"    
  shows  "(\<Squnion>h\<in>H. nn_integral (measure_pmf D) (f h))
         \<le> nn_integral (measure_pmf D) (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f h S'))"
proof -  
  show ?thesis  apply(rule SUP_least) 
  proof -
    fix x
    assume "x\<in>H"
    then show "nn_integral D (f x) \<le> nn_integral D (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f h S'))"
      apply(intro nn_integral_mono_AE) apply(rule AE_pmfI)
      subgoal for d 
        apply(rule SUP_upper)
        by simp
      done
  qed
qed


(* idea to compress integrability of two expectations into one:
    pair_sigma_finite.integrable_fst *)

(* idea, there is the tactic apply(measurable),
  what does it do? *)

thm pair_sigma_finite.Fubini_integrable


lemma "measure_pmf (pair_pmf M M2)
    = pair_measure (measure_pmf M) (measure_pmf M2)"
     sorry


lemma nn_integral_linear': 
  shows 
  "nn_integral M (\<lambda>S. nn_integral M2 (f S))
        = nn_integral M2 (\<lambda>S2. nn_integral M (\<lambda>S. f S S2))"
   (* fubini *)
  sorry


term prob_space
lemma expectation_linear':
  fixes
     f :: "_ \<Rightarrow> _ \<Rightarrow> real"
 
  shows 
  "measure_pmf.expectation M (\<lambda>S. measure_pmf.expectation M2 (f S))
        = measure_pmf.expectation M2 (\<lambda>S2. measure_pmf.expectation M (\<lambda>S. f S S2))"
proof -

  have "integrable (measure_pmf M2 \<Otimes>\<^sub>M measure_pmf M) (\<lambda>(x, S). f S x)"
    apply(rule pair_sigma_finite.Fubini_integrable)
    subgoal 
      by (simp add: measure_pmf.sigma_finite_measure_axioms pair_sigma_finite_def)  
    subgoal   sorry
    subgoal apply(rule measure_pmf.integrable_const_bound)
      sorry
    sorry


  thm pair_sigma_finite.Fubini_integral

  term "integral\<^sup>L M"

  show ?thesis apply(subst pair_sigma_finite.Fubini_integral)
    subgoal  
      by (simp add: measure_pmf.sigma_finite_measure_axioms pair_sigma_finite_def)  
    subgoal  by fact
    subgoal apply simp done
    done
qed


lemma expectation_linear:
    "measure_pmf.expectation M (\<lambda>S. measure_pmf.expectation M2 (f S))
        = measure_pmf.expectation M2 (\<lambda>S2. measure_pmf.expectation M (\<lambda>S. f S S2))"
  sorry
  
section "help by auto3"
(* by auto3 aka Manuel Eberl: *)
lemma convex_on_exp: 
  fixes l :: real
  assumes "l > 0"
  shows   "convex_on UNIV (\<lambda>x. exp(l*x))"
  using assms
  by (intro convex_on_realI[where f' = "\<lambda>x. l * exp (l * x)"]) (auto
intro!: derivative_eq_intros)

lemma mult_const_minus_self_real_le:
  fixes x :: real
  shows "x * (c - x) \<le> c\<^sup>2 / 4"
proof -
  have "x * (c - x) = -(x - c / 2)\<^sup>2 + c\<^sup>2 / 4"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 0 + c\<^sup>2 / 4"
    by (intro add_mono) auto
  finally show ?thesis by simp
qed

lemma outsourced:
  fixes a b l :: real
  assumes "l > 0" and ab: "a < 0" "b > 0"
  defines "p \<equiv> -a / (b - a)"
  defines "h \<equiv> l * (b - a)"
  defines "L \<equiv> (\<lambda>h. -h * p + ln (1 + p * (exp h - 1)))"
  shows   "L h \<le> h\<^sup>2 / 8"
proof -
  define L' where "L' = (\<lambda>h. -p + p * exp h / (1 + p * (exp h - 1)))"
  define L'' where "L'' = (\<lambda>h. -(p ^ 2) * exp h * exp h / (1 + p * (exp
h - 1)) ^ 2 +
                              p * exp h / (1 + p * (exp h - 1)))"
  define Ls where "Ls = (\<lambda>n. [L, L', L''] ! n)"

  from ab have "p > 0"
    by (auto simp: p_def field_simps)
  from ab and \<open>l > 0\<close> have "h > 0"
    by (auto simp: h_def)
  have [simp]: "L 0 = 0" "L' 0 = 0"
    by (auto simp: L_def L'_def)

  have L': "(L has_real_derivative L' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have "1 + p * (exp x - 1) > 0"
      using \<open>p > 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    thus ?thesis
      unfolding L_def L'_def by (auto intro!: derivative_eq_intros)
  qed

  have L'': "(L' has_real_derivative L'' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have *: "1 + p * (exp x - 1) > 0"
      using \<open>p > 0\<close> that by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      unfolding L'_def L''_def
      by (insert *, (rule derivative_eq_intros refl | simp)+) (auto
simp: divide_simps; algebra)
  qed

  have diff: "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> (Ls m has_real_derivative Ls
(Suc m) t) (at t)"
    using L' L'' by (auto simp: Ls_def nth_Cons split: nat.splits)
  from Taylor[of 2 Ls L 0 h 0 h, OF _ _ diff]
    obtain t where t: "t \<in> {0<..<h}" "L h = L'' t * h ^ 2 / 2"
      using \<open>h > 0\<close> ab by (auto simp: Ls_def lessThan_nat_numeral)
  define u where "u = p * exp t / (1 + p * (exp t - 1))"

  have "L'' t = u * (1 - u)"
    by (simp add: L''_def u_def divide_simps; algebra)
  also have "\<dots> \<le> 1 / 4"
    using mult_const_minus_self_real_le[of u 1] by simp
  finally have "L'' t \<le> 1 / 4" .

  note t(2)
  also have "L'' t * h\<^sup>2 / 2 \<le> (1 / 4) * h\<^sup>2 / 2"
    using \<open>L'' t \<le> 1 / 4\<close> by (intro mult_right_mono divide_right_mono) auto
  finally show "L h \<le> h\<^sup>2 / 8" by simp
qed


lemma hoeffdings_lemma:
  fixes a b :: real
  assumes range: "\<And>i. measure_pmf.prob D {x. a \<le> x \<and> x \<le> b} = 1" 
  and E0: "measure_pmf.expectation D id = 0" and lgt0: "l>0"
  and aleb: "a\<le>b" and al0: "a<0"and bg0: "0<b" (* those do actually follow from E0 I think *)
shows  "measure_pmf.expectation D (\<lambda>x. exp (l*x)) \<le> exp ( l^2 *(b-a)^2 / 8)"
proof -
  let ?f = "(\<lambda>x. exp (l * x))"

  from range have xbetweenab: "\<And>x. x\<in>set_pmf D \<Longrightarrow> x \<in> {x. a \<le> x \<and> x \<le> b}"
    sorry
  from al0 bg0 have ab: "a<b" by auto

  (* for integrable side conditions *)
  thm measure_pmf.integrable_const_bound 
  thm integrable_measure_pmf_finite

  then  have anb: "a\<noteq>b" by auto    
  have F: "\<And>x :: real. (1 - (b - x) / (b - a)) = (x-a)/(b-a)"
  proof -
    fix x
    have "1 = (b-a) / (b-a)" using anb by auto
    have "(1 - (b - x) / (b - a)) = ((b-a) / (b-a) -  (b - x) / (b - a))"
      using anb by auto
    also have "\<dots> = ( (b-a)  -  (b - x) ) /  (b - a)" using anb by argo
    also have "\<dots> = (x-a)/(b-a)" by auto
    finally show "(1 - (b - x) / (b - a)) = (x-a)/(b-a)" .
  qed

  have cvon: "convex_on UNIV (\<lambda>x. exp(l*x))" using  convex_on_exp assms(3) by auto

  have *: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> ?f x \<le> (b - x) / (b - a) * exp (l * a) + (x-a)/(b-a) * exp (l * b)"
  proof -
    fix x :: real
    let ?\<alpha> = "(b-x) / (b-a)"
    have g: "1 - ?\<alpha> = (x-a) / (b-a)" using F .
    assume "a \<le> x" "x \<le> b"
    then have C: "0 \<le> ?\<alpha>" "?\<alpha> \<le> 1" using ab by auto
  
    from convex_onD[OF cvon, of _ b a, simplified ] have A:
      "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> exp (l * ((1 - t) * b + t * a)) \<le> (1 - t) * exp (l * b) + t * exp (l * a)" .

    have B: "(1 - ?\<alpha>) * b + ?\<alpha> * a = x"
    proof -
      have "(1 - ?\<alpha>) * b + ?\<alpha> * a =  ((x-a) / (b-a)) * b + ((b-x) / (b-a)) * a" 
        unfolding g .. 
      also have "\<dots> = (x*(b-a)) / (b-a)" by algebra
      also have "\<dots> = x" using ab by simp
      finally show ?thesis .
    qed

    from A[of ?\<alpha>, simplified B, OF C]
    show "exp (l * x) \<le> (b - x) / (b - a) * exp (l * a) + (x-a)/(b-a) * exp (l * b)"
      unfolding  g by simp
  qed
  
  have i: "\<And>y Z. 0 \<le> Z \<Longrightarrow> a\<le>y \<Longrightarrow> y\<le>b \<Longrightarrow> a<b \<Longrightarrow> b>0 \<Longrightarrow>  (b - y) * Z / (b - a) \<le> Z"
  proof -
    fix y Z :: real
    assume A: "0 \<le> Z" "a\<le>y" "y\<le>b" "a<b" "b>0"
    have "(b - y) * Z / (b - a) = ((b - y) / (b - a)) * Z" by auto
    also have "\<dots> \<le> Z" apply(rule mult_left_le_one_le)
      using A by auto
    finally show "(b - y) * Z / (b - a) \<le> Z" .
  qed
  
  have ii: "\<And>y Z. 0 \<le> Z \<Longrightarrow> a\<le>y \<Longrightarrow> y\<le>b \<Longrightarrow> a<b \<Longrightarrow> b>0 \<Longrightarrow>  (y - a) * Z / (b - a) \<le> Z"
  proof -
    fix y Z :: real
    assume A: "0 \<le> Z" "a\<le>y" "y\<le>b" "a<b" "b>0"
    have "(y - a) * Z / (b - a) = ((y - a) / (b - a)) * Z" by auto
    also have "\<dots> \<le> Z" apply(rule mult_left_le_one_le)
      using A by auto
    finally show "(y - a) * Z / (b - a) \<le> Z" .
  qed

  have "measure_pmf.expectation D ?f \<le> measure_pmf.expectation D (\<lambda>x. (b - x) / (b - a) * exp (l * a) + (x-a)/(b-a) * exp (l * b))"
    apply(rule expectation_mono) 
    subgoal
      apply(rule measure_pmf.integrable_const_bound[where B="exp (l * b)"])   using lgt0 
      by (auto intro!: AE_pmfI dest: xbetweenab)    
       
    subgoal 
      apply(rule measure_pmf.integrable_const_bound[where B="exp (l * a) + exp (l * b)"])
      using lgt0 
       apply (auto intro!: AE_pmfI dest!: xbetweenab)   
      apply(rule add_mono) 
      subgoal apply(rule i) using ab bg0 by auto
      subgoal apply(rule ii) using ab bg0 by auto
      done
    apply(rule *)
    using xbetweenab by auto
  also 
  have "\<dots> = (b - measure_pmf.expectation D id) / (b - a) * exp (l * a) + (measure_pmf.expectation D id-a)/(b-a) * exp (l * b)"
    (is "?L = ?R")  
  proof -
    have "?L = measure_pmf.expectation D (\<lambda>x. (b + (x * -1)) / (b - a) * exp (l * a) + (x + (- a)) / (b - a) * exp (l * b))" by simp
    also have "\<dots> = measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a) * exp (l * a)) + measure_pmf.expectation D (\<lambda>x. (x + - a) / (b - a) * exp (l * b))"
      apply(rule Bochner_Integration.integral_add)
      subgoal using bg0 ab
        apply (auto intro!: measure_pmf.integrable_const_bound[where B="exp (l * a) "]
                AE_pmfI dest!: xbetweenab)  apply(rule i) by auto   
      subgoal using bg0 ab
        apply (auto intro!: measure_pmf.integrable_const_bound[where B="exp (l * b) "]
                AE_pmfI dest!: xbetweenab)  apply(rule ii) by auto  
      done
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a) * exp (l * a)) = measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a))  * exp (l * a)"
      by (rule integral_mult_left_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a)) =  measure_pmf.expectation D (\<lambda>x. (b + x * -1) ) / (b - a)  " 
      by(rule integral_divide_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) ) = measure_pmf.expectation D (\<lambda>_. b) +  measure_pmf.expectation D (\<lambda>x. x * -1 )" 
      apply(rule Bochner_Integration.integral_add)
      subgoal by auto
      subgoal 
        by(auto intro!: measure_pmf.integrable_const_bound[where B="max (abs a) (abs b)"]
                AE_pmfI dest!: xbetweenab) 
      done
    also have "measure_pmf.expectation D (\<lambda>_. b) = b"
      using expectation_const by simp
    also have "measure_pmf.expectation D (\<lambda>x. x * -1) = - measure_pmf.expectation D id"
      apply(subst integral_mult_left_zero) unfolding id_def by simp


    also have "measure_pmf.expectation D (\<lambda>x. (x + - a) / (b - a) * exp (l * b)) = measure_pmf.expectation D (\<lambda>x. (x + - a) / (b - a) )  * exp (l * b)"
      by (rule integral_mult_left_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (x + - a) / (b - a) ) =  measure_pmf.expectation D (\<lambda>x. (x + - a) ) / (b - a)  " 
      by(rule integral_divide_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (x + - a) ) = measure_pmf.expectation D (\<lambda>x. x) +  measure_pmf.expectation D (\<lambda>_. -a )" 
      apply(rule Bochner_Integration.integral_add)
      subgoal        
        by(auto intro!: measure_pmf.integrable_const_bound[where B="max (abs a) (abs b)"]
                AE_pmfI dest!: xbetweenab) 
      subgoal by auto
      done
    also have "measure_pmf.expectation D (\<lambda>_. -a) = -a"
      using expectation_const by simp
    also have "measure_pmf.expectation D (\<lambda>x. x ) =  measure_pmf.expectation D id"
      unfolding id_def by simp

    finally
    show "?L = ?R" by argo
  qed
    (*
    thm integral_add integral_mult_left_zero integral_divide_zero expectation_const
    thm integral_bij_count_space
    thm integral_bounded_linear
    apply(subst integral_bounded_linear[symmetric, where M=D and T="?f" and f=id])
    by simp  *)
  also have "\<dots> = b / (b - a) * exp (l * a) - a/(b-a) * exp (l * b)"
    by (simp add: E0)
  finally have 1: "measure_pmf.expectation D ?f \<le> (b / (b - a)) * ?f a - (a/(b-a)) * ?f b" .

  let ?h = "l*(b-a)"
  let ?p = "-a / (b-a)"
  let ?L = "\<lambda>h. -h * ?p + ln (1- ?p + ?p * exp h)"

  have 2: "(b / (b - a)) * ?f a - (a/(b-a)) * ?f b = exp (?L ?h)"
  proof -
    have nn: "1 - ?p + ?p * exp ?h > 0"
    proof -
      have i: "?p \<ge> 0" using ab al0  
        by (smt divide_nonneg_pos) 
      have ii: "exp ?h > 1" apply(subst one_less_exp_iff) using assms(3) ab by auto
      then have "(exp ?h -1) \<ge>0" by simp
      have "(exp ?h -1) * ?p \<ge> 0" apply(intro mult_nonneg_nonneg) by fact+
      moreover have "1 - ?p + ?p * exp ?h = 1 + (exp ?h -1) * ?p" by algebra
      ultimately show ?thesis by argo
    qed
    have "exp (?L ?h) = exp (- ?h * ?p) *  exp ( ln (1- ?p + ?p * exp ?h))"
      using exp_add by fast 
    also have "exp ( ln (1- ?p + ?p * exp ?h)) = 1- ?p + ?p * exp ?h" using nn by simp
    finally have "exp (?L ?h) = exp (- ?h * ?p) * (1- ?p + ?p * exp ?h)" . 
    also have "\<dots> = (exp (- ?h * ?p) - ?p * exp (- ?h * ?p)) + ?p * exp ?h * exp (- ?h * ?p)" by algebra
    also have "(exp (- ?h * ?p) - ?p * exp (- ?h * ?p)) = (b / (b - a)) * ?f a"
    proof - 
      have expand: "exp (l * a) = ((b-a) * exp (l * a)) / (b-a)" using ab by auto
      have "(exp (- ?h * ?p) - ?p * exp (- ?h * ?p)) = exp (l * a) + a * exp (l * a) / (b - a)" 
        using ab by simp
      also have "\<dots> = ((b-a) * exp (l * a) + a * exp (l * a)) / (b - a)"
        apply(subst expand) by algebra
      also have "((b-a) * exp (l * a) + a * exp (l * a)) = b *  exp (l * a)" by algebra
      finally show ?thesis by simp
    qed
    also have "?p * exp ?h * exp (- ?h * ?p) = - (a/(b-a)) * ?f b" 
    proof - 
      have collapse: "exp (l * (b - a)) * exp (l * a) = exp (l * (b-a) + l *a)" using mult_exp_exp by blast
      have "?p * exp ?h * exp (- ?h * ?p) = - (a * (exp (l * (b - a)) * exp (l * a)) / (b - a))" 
        using ab by simp
      also have "\<dots> = - (a * exp (l * b) / (b - a))"
        apply(subst collapse) by argo 
      finally show ?thesis by simp
    qed
    finally 
    show ?thesis by simp
  qed

  have G: "1 + a / (b - a) - a * exp (l * (b - a)) / (b - a)
      = 1 - a * (exp (l * (b - a)) - 1) / (b - a) "
    using al0 bg0 apply (auto simp: algebra_simps)
    unfolding add_divide_distrib[symmetric] by simp 

  have 3: "?L ?h \<le> ?h^2 / 8"
    apply(rule order.trans[OF _ outsourced])
    using al0 bg0 lgt0   apply auto unfolding G by simp

  have 4: "?h^2 = l^2 *(b-a)^2" by algebra

  note 1
  also have "(b / (b - a)) * ?f a - (a/(b-a)) * ?f b = exp (?L ?h)" using 2 by simp
  also have "\<dots> \<le> exp (?h^2 / 8)" using 3 ..
  also have "\<dots> \<le> exp ( l^2 *(b-a)^2 / 8)" unfolding 4 ..
  finally show ?thesis .
qed


lemma set_Pi_pmf': "finite A \<Longrightarrow>  f \<in> set_pmf (Pi_pmf A dflt D) \<Longrightarrow> (\<forall>i\<in>A. f i \<in> set_pmf (D i))"
  apply (auto simp: set_pmf_eq pmf_Pi)
  by (meson prod_zero) 

lemma 
  assumes 
   range: "measure_pmf.prob D {x. a \<le> x \<and> x \<le> b} = 1" 
  shows setofDi: "set_pmf D \<subseteq> {a..b}"
proof -
    have "measure_pmf.prob D (space (measure_pmf D) - {x. a \<le> x \<and> x \<le> b}) = 0" 
      using range  by (subst measure_pmf.prob_compl) (auto)
    also have "(space (measure_pmf D) - {x. a \<le> x \<and> x \<le> b}) = -{x. a \<le> x \<and> x \<le> b}"
      by auto
    finally have "set_pmf D \<inter> -{x. a \<le> x \<and> x \<le> b} = {}"
      by (subst (asm) measure_pmf_zero_iff) 
    thus "set_pmf D \<subseteq> {a..b}"
      by auto
qed

lemma hoeffding_ineq:
  assumes
      "\<And>i::nat. i < m \<Longrightarrow> measure_pmf.expectation (D i) id = \<mu> i"
    and range: "\<And>i. i<m \<Longrightarrow> measure_pmf.prob (D i) {x. a \<le> x \<and> x \<le> b} = 1"  and "(\<epsilon>::real)>0"
  and PA: "\<And>i. i < m \<Longrightarrow> a - \<mu> i < 0" and PB: "\<And>i. i < m \<Longrightarrow> 0 < b - \<mu> i" and ab2: "a<b" and mgt0: "m>0"
  shows "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. abs(sum  (\<lambda>i. (\<sigma> i) - \<mu> i) {0..<m} / m) > \<epsilon> }
             \<le> 2 * exp (- 2 * m * \<epsilon>^2 / (b-a)^2 )"
proof - 



  from setofDi[OF range]  have xbetweenab: "\<And>x i. i<m \<Longrightarrow>  x\<in>set_pmf (D i) \<Longrightarrow> x \<in> {x. a \<le> x \<and> x \<le> b}"
    by fastforce
     

  {
    fix D :: "nat \<Rightarrow> real pmf" and a b :: "nat \<Rightarrow> real" and d :: real
    assume ONE: "\<And>i. i<m \<Longrightarrow> measure_pmf.prob (D i) {x. a i \<le> x \<and> x \<le> b i} = 1"  
    assume TWO: "\<And>x. x<m \<Longrightarrow> measure_pmf.expectation (D x) (\<lambda>x. id (x / real m)) = 0"
    assume defd: "\<And>i. i<m \<Longrightarrow> b i - a i = d"
    assume dgt0: "d>0" 
    assume ab: "\<And>i. i<m \<Longrightarrow> a i \<le> b i"  
    assume ab2: "\<And>i. i<m \<Longrightarrow> a i < b i"  
    assume ai: "\<And>i. i<m \<Longrightarrow> a i < 0 "
    assume bi: "\<And>i. i<m \<Longrightarrow> 0 < b i"
  thm markov_inequality
  { fix M and \<epsilon>::real and l :: real
    assume "integrable (measure_pmf M) (\<lambda>x. exp (l * x))"
    assume "l>0"
    then 
    have "measure_pmf.prob M {x. x > \<epsilon>} = measure_pmf.prob M {x. exp (l * x) > exp (l * \<epsilon>)}"
      by simp
    also have "\<dots> \<le>  measure_pmf.expectation M (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)"
      apply(rule markov_inequality) 
      subgoal by fact
      subgoal by simp 
      subgoal by simp
      done
    finally have "measure_pmf.prob M {x. x > \<epsilon>} \<le> measure_pmf.expectation M (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)" .
  } note first = this
  { 
    fix   p and Q and l :: real 
    have "measure_pmf.expectation (Pi_pmf  {0..<m} dflt p) (\<lambda>y. exp (l * (\<Sum>x\<in> {0..<m}. (Q x) (y x) / m) ))
          = measure_pmf.expectation (Pi_pmf  {0..<m} dflt p) (\<lambda>y. ( \<Prod>x\<in> {0..<m}. exp (l * (Q x) (y x) / m)))"
      by (auto simp:  sum_distrib_left exp_sum)     
    also have "\<dots> = (\<Prod>x\<in> {0..<m}. measure_pmf.expectation (p x) (\<lambda>y. ( exp (l * (Q x) y / m))))"
      by (auto intro: expectation_Pi_pmf_prod)
    finally have "measure_pmf.expectation (Pi_pmf {0..<m} dflt p) (\<lambda>y. exp (l * (\<Sum>x = 0..<m. Q x (y x) / real m))) =
                    (\<Prod>x = 0..<m. measure_pmf.expectation (p x) (\<lambda>y. exp (l * Q x y / real m))) ".
  } note second = this
  note second' = second[of _ _ "(\<lambda>x y. y)"]
  note second'_sym = second[of _ _ "(\<lambda>x y. -y)"]


  { 
    fix x :: nat   and l :: real
    assume xm: "x<m"
    assume lgt0: "l>0"
    from mgt0 have p: "\<And>x y. (x / real m \<le> y / real m) \<longleftrightarrow> x \<le> y"  
      by (smt divide_strict_right_mono of_nat_0_less_iff)      
    have ahhhh: "\<And>a b. {y. a / real m \<ge>   (y / real m) \<and>  (y / real m) \<ge> b / real m} = {x. a \<ge> x \<and> x \<ge> b}"
      unfolding p  
      by simp

    have "measure_pmf.expectation (D x) (\<lambda>y. exp (l * (-y / real m)))
          = measure_pmf.expectation (map_pmf (\<lambda>y. (-y / real m)) (D x) ) (\<lambda>y. exp (l * y))"
      by simp 
    also have "\<dots> \<le>  exp (l\<^sup>2 * (b x / real m - a x / real m)\<^sup>2 / 8)"  
      apply(rule order.trans)
       apply(rule hoeffdings_lemma[where a="-b x/m" and b="-a x/m"])
      subgoal apply(subst measure_map_pmf) 
        apply simp unfolding ahhhh apply(subst conj_commute)
        using ONE[OF xm] .
      subgoal unfolding integral_map_pmf using TWO[OF xm] by simp
      subgoal using lgt0 .
      subgoal using mgt0 ab[OF xm] divide_right_mono by force 
      subgoal using bi[OF xm] mgt0  by auto
      subgoal apply(rule divide_pos_pos) using ai[OF xm] mgt0 by auto
      apply simp
      done
    also have "\<dots> =  exp (l\<^sup>2 * (b x  - a x)\<^sup>2 / (8 * (real m)^2))" apply simp
      unfolding power2_eq_square using ab mgt0 apply (auto simp: algebra_simps)
      unfolding add_divide_distrib[symmetric] by simp
    also have "\<dots> =  exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)^2))"
      using defd[OF xm] by simp
    finally have "measure_pmf.expectation (D x) (\<lambda>y. exp (l * (-y / real m))) \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2)) " .
  } note third_sym = this

  { 
    fix x :: nat   and l :: real
    assume xm: "x<m"
    assume lgt0: "l>0"
    from mgt0 have p: "\<And>x y. (x / real m \<le> y / real m) \<longleftrightarrow> x \<le> y"  
      by (smt divide_strict_right_mono of_nat_0_less_iff)      
    have ahhhh: "\<And>a b. {y. a / real m \<le> y / real m \<and> y / real m \<le> b / real m} = {x. a \<le> x \<and> x \<le> b}"
      unfolding p  
      by simp

    have "measure_pmf.expectation (D x) (\<lambda>y. exp (l * (y / real m)))
          = measure_pmf.expectation (map_pmf (\<lambda>y. (y / real m)) (D x) ) (\<lambda>y. exp (l * y))"
      by simp 
    also have "\<dots> \<le>  exp (l\<^sup>2 * (b x / real m - a x / real m)\<^sup>2 / 8)"  
       apply(rule hoeffdings_lemma[where a="a x/m" and b="b x/m"])
      subgoal apply(subst measure_map_pmf) 
        apply simp unfolding ahhhh
        using ONE[OF xm]  .
      subgoal unfolding integral_map_pmf using TWO[OF xm] .
      subgoal using lgt0 .
      subgoal using mgt0 ab[OF xm] divide_right_mono by force 
      subgoal apply(rule divide_neg_pos) using ai[OF xm] mgt0 by simp_all 
      subgoal using bi[OF xm] mgt0  by auto
      done
    also have "\<dots> =  exp (l\<^sup>2 * (b x  - a x)\<^sup>2 / (8 * (real m)^2))" apply simp
      unfolding power2_eq_square using ab mgt0 apply (auto simp: algebra_simps)
      unfolding add_divide_distrib[symmetric] by simp
    also have "\<dots> =  exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)^2))"
      using defd[OF xm] by simp
    finally have "measure_pmf.expectation (D x) (\<lambda>y. exp (l * (y / real m))) \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2)) " .
  } note third = this

  note first second
  {
    fix l::real
    assume lgt0: "l>0"

    have "(\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l *  y / real m)))
            = (\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l * (y / real m))))" by simp
    also have "\<dots> \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2)))"
      apply(rule prod_mono)
      apply rule
      subgoal for x apply(rule Bochner_Integration.integral_nonneg) by simp  
      subgoal apply(rule third) using lgt0 by simp_all
      done
    finally have "(\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l *   y / real m)))
           \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) " .
  } note third' = this 
  {
    fix l::real
    assume lgt0: "l>0"

    have "(\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l *  -y / real m)))
            = (\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l * (-y / real m))))" by simp
    also have "\<dots> \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2)))"
      apply(rule prod_mono)
      apply rule
      subgoal for x apply(rule Bochner_Integration.integral_nonneg) by simp  
      subgoal apply(rule third_sym) using lgt0 by simp_all
      done
    finally have "(\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l *   -y / real m)))
           \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) " .
  } note third'_sym = this 

  note first second third'

  let ?avg = "(\<lambda>y. (\<Sum>x = 0..<m. y x / real m))"
  { fix l :: real and \<epsilon> :: real
    assume lgt0: "0<l" 
    have blaub: "(real m * (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) - l * \<epsilon> = ( (l\<^sup>2 * d\<^sup>2 / (8 * (real m)))) - l * \<epsilon>" 
      using mgt0 lgt0  unfolding power2_eq_square 
      by(auto) 

    have p: "finite  {0..<m}" by auto
    have t': "\<And>y B. y \<in> set_pmf (Pi_pmf {0..<m} dflt D) \<Longrightarrow>   (l * (\<Sum>x = 0..<m. y x / real m)) \<le>   (l * (\<Sum>x = 0..<m. b x / real m))"
    proof -
      fix y B
      assume "y \<in> set_pmf (Pi_pmf {0..<m} dflt D)"
      from set_Pi_pmf'[OF p this] have i: "\<And>i. i\<in>{0..<m} \<Longrightarrow> y i \<in> set_pmf (D i)" ..

        

      show "  (l * (\<Sum>x = 0..<m. y x / real m)) \<le>   (l * (\<Sum>x = 0..<m. b x / real m))"
        apply(rule mult_left_mono)
        subgoal 
          apply(rule sum_mono) apply(rule divide_right_mono)
          subgoal for x using i[of x] setofDi[of "D x", OF ONE] by auto
          subgoal using mgt0 by simp
          done
        subgoal using lgt0 by simp
        done
    qed
     
    have t: "integrable (measure_pmf (map_pmf ?avg (Pi_pmf {0..<m} dflt D))) (\<lambda>x. exp (l * x))"
      apply(rule measure_pmf.integrable_const_bound[where B="exp (l*(\<Sum>x = 0..<m. b x / real m))"])
      subgoal
        apply(rule AE_pmfI) apply auto  apply(rule t') .
      subgoal apply simp done
      done
    from first[OF t lgt0, of  \<epsilon>]
    have "measure_pmf.prob (map_pmf ?avg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
          \<le> measure_pmf.expectation (map_pmf ?avg (Pi_pmf {0..<m} dflt D)) (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)" .
    also have "\<dots> = measure_pmf.expectation (Pi_pmf {0..<m} dflt D) (\<lambda>x. exp (l * ?avg x)) / exp (l * \<epsilon>)" 
      by simp
    also have "\<dots> = (\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l * y / real m))) / exp (l * \<epsilon>)" 
      apply(subst second'[of D l]) ..
    also have "\<dots> \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) / exp (l * \<epsilon>)" 
       apply(rule divide_right_mono) apply(rule third') subgoal by fact
      subgoal by simp
      done
    also
    have "\<dots> \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * real m) - l * \<epsilon>)"
      apply simp apply(subst exp_of_nat_mult[symmetric])
      apply(subst exp_diff[symmetric])
      apply(subst blaub) ..
    finally have "measure_pmf.prob (map_pmf ?avg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
                   \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * real m) - l * \<epsilon>) " .
  } note oneside = this


  let ?mavg = "(\<lambda>y. -(\<Sum>x = 0..<m. y x / real m))"
  { fix l :: real and \<epsilon> :: real
    assume lgt0: "0<l" 
    have blaub: "(real m * (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) - l * \<epsilon> = ( (l\<^sup>2 * d\<^sup>2 / (8 * (real m)))) - l * \<epsilon>" 
      using mgt0 lgt0  unfolding power2_eq_square 
      by(auto) 


    have p: "finite  {0..<m}" by auto
    have t': "\<And>y B. y \<in> set_pmf (Pi_pmf {0..<m} dflt D) \<Longrightarrow>   (l * (\<Sum>x = 0..<m. a x / real m)) \<le>   (l * (\<Sum>x = 0..<m. y x / real m))"
    proof -
      fix y B
      assume "y \<in> set_pmf (Pi_pmf {0..<m} dflt D)"
      from set_Pi_pmf'[OF p this] have i: "\<And>i. i\<in>{0..<m} \<Longrightarrow> y i \<in> set_pmf (D i)" ..

        

      show "  (l * (\<Sum>x = 0..<m. a x / real m)) \<le>   (l * (\<Sum>x = 0..<m. y x / real m))"
        apply(rule mult_left_mono)
        subgoal 
          apply(rule sum_mono) apply(rule divide_right_mono)
          subgoal for x using i[of x] setofDi[of "D x", OF ONE] by auto
          subgoal using mgt0 by simp
          done
        subgoal using lgt0 by simp
        done
    qed
     
    have t: "integrable (measure_pmf (map_pmf ?mavg (Pi_pmf {0..<m} dflt D))) (\<lambda>x. exp (l * x))"
      apply(rule measure_pmf.integrable_const_bound[where B="exp (-l*(\<Sum>x = 0..<m. a x / real m))"])
      subgoal
        apply(rule AE_pmfI) apply auto  apply(rule t') .
      subgoal apply simp done
      done

    have ppa: "\<And>x. ?mavg x = (\<Sum>xa = 0..<m. - x xa / real m)"
      using mgt0 unfolding sum_negf[symmetric] by simp
    from first[OF t lgt0, of  \<epsilon>]
    have "measure_pmf.prob (map_pmf ?mavg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
          \<le> measure_pmf.expectation (map_pmf ?mavg (Pi_pmf {0..<m} dflt D)) (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)" .
    also have "\<dots> = measure_pmf.expectation (Pi_pmf {0..<m} dflt D) (\<lambda>x. exp (l * ?mavg x)) / exp (l * \<epsilon>)" 
      by simp
    also have "\<dots> = measure_pmf.expectation (Pi_pmf {0..<m} dflt D) (\<lambda>x. exp (l * (\<Sum>xa = 0..<m. - x xa / real m))) / exp (l * \<epsilon>)" 
      unfolding ppa by simp
    also have "\<dots> = (\<Prod>x = 0..<m. measure_pmf.expectation (D x) (\<lambda>y. exp (l * -y / real m))) / exp (l * \<epsilon>)"  
      apply(subst second'_sym[of D l]) ..
    also have "\<dots> \<le> (\<Prod>x = 0..<m. exp (l\<^sup>2 * d\<^sup>2 / (8 * (real m)\<^sup>2))) / exp (l * \<epsilon>)" 
       apply(rule divide_right_mono) apply(rule third'_sym) subgoal by fact
      subgoal by simp
      done
    also
    have "\<dots> \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * real m) - l * \<epsilon>)"
      apply simp apply(subst exp_of_nat_mult[symmetric])
      apply(subst exp_diff[symmetric])
      apply(subst blaub) ..
    finally have "measure_pmf.prob (map_pmf ?mavg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
                   \<le> exp (l\<^sup>2 * d\<^sup>2 / (8 * real m) - l * \<epsilon>) " .
  } note otherside = this

  have aaah: "(4 * real m * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m) - 4 * real m * \<epsilon> * \<epsilon> / d\<^sup>2
        = - 2 * m * \<epsilon>^2 / d^2"
  proof -
    have p: "(4 * real m * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m)
         = (4 * real m * \<epsilon>)^2 * d^2 / (8 * real m*(d^2)*(d^2))"
      unfolding power2_eq_square using ab  by(auto simp: algebra_simps) 
    also have "\<dots> = (4 * real m * \<epsilon>)^2  / (8 * real m*(d^2))"
      using ab by simp
    finally have 1: "(4 * real m * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m) = (4 * real m * \<epsilon>)\<^sup>2 / (8 * real m * d\<^sup>2) " .

    have 2: "4 * real m * \<epsilon> * \<epsilon> / d\<^sup>2 = 4 * real m * \<epsilon> * \<epsilon> * 8 * real m / (8 * real m * d\<^sup>2)"
      using mgt0 by auto

    have "(4 * real m * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m) - 4 * real m * \<epsilon> * \<epsilon> / d\<^sup>2
        = (4 * real m * \<epsilon>)\<^sup>2 / (8 * real m * d\<^sup>2) - 4 * real m * \<epsilon> * \<epsilon> * 8 * real m / (8 * real m * d\<^sup>2)"
      unfolding 1 2 ..
    also have "\<dots> = ( (4 * real m * \<epsilon>)*(4 * real m * \<epsilon>)  - 4 * real m * \<epsilon> * \<epsilon> * 8 * real m) / (8 * real m * d\<^sup>2)"
      by algebra
    also have "\<dots> = ( (8 * real m )*(2 * real m * \<epsilon>* \<epsilon>)  - (8 * real m )*  \<epsilon> * \<epsilon> * 4 * real m) / (8 * real m * d\<^sup>2)"
      by algebra
    also have "\<dots> = ( (2 * real m * \<epsilon>* \<epsilon>)  -   \<epsilon> * \<epsilon> * 4 * real m) / (  d\<^sup>2)"
      using mgt0 by auto
    
    also have "\<dots> = - 2 * m * \<epsilon>^2 / d^2" unfolding power2_eq_square using ab mgt0 by (auto simp: algebra_simps) 
    finally show ?thesis .
  qed
  have br: "0 < real (4 * m) * \<epsilon> / d\<^sup>2" apply(rule divide_pos_pos)
    unfolding power2_eq_square using dgt0  assms(3) mgt0  by auto
  from oneside[of "4*m*\<epsilon>/d^2" \<epsilon>, OF br] have 
      "measure_pmf.prob (map_pmf ?avg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
          \<le> exp ((real (4 * m) * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m) - real (4 * m) * \<epsilon> / d\<^sup>2 * \<epsilon>)"
    .
  also have "\<dots> = exp (- 2 *  m * \<epsilon>\<^sup>2 / d\<^sup>2)"
    apply auto unfolding aaah  by simp
  finally have
      "measure_pmf.prob (map_pmf ?avg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
                   \<le> exp (- 2 * m * \<epsilon>\<^sup>2 / d\<^sup>2)" .
  then have ONESIDE: "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {x. \<epsilon> < ?avg x}
                   \<le> exp (- 2 * m * \<epsilon>\<^sup>2 / d\<^sup>2)" by simp

  have gr: "\<And>f. {y. \<epsilon> < - f y} = {x. f x < - \<epsilon>}" by auto
  from otherside[of "4*m*\<epsilon>/d^2" \<epsilon>, OF br] have 
      "measure_pmf.prob (map_pmf ?mavg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
          \<le> exp ((real (4 * m) * \<epsilon> / d\<^sup>2)\<^sup>2 * d\<^sup>2 / (8 * real m) - real (4 * m) * \<epsilon> / d\<^sup>2 * \<epsilon>)"
    .
  also have "\<dots> = exp (- 2 *  m * \<epsilon>\<^sup>2 / d\<^sup>2)"
    apply auto unfolding aaah  by simp
  finally  
  have 
      "measure_pmf.prob (map_pmf ?mavg (Pi_pmf {0..<m} dflt D)) {x. \<epsilon> < x}
                   \<le> exp (- 2 * m * \<epsilon>\<^sup>2 / d\<^sup>2)" .
  then have OTHERSIDE: "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {x. -\<epsilon> > ?avg x}
                   \<le> exp (- 2 * m * \<epsilon>\<^sup>2 / d\<^sup>2)" apply simp
    unfolding gr . 

  have p: "\<And>f. {\<sigma>. \<epsilon> < \<bar>f \<sigma>\<bar>} \<subseteq> {x. \<epsilon> < f x} \<union> {x. -\<epsilon> > f x}"
    by auto  
  have a: "\<And>\<sigma>. (\<Sum>i = 0..<m. (\<sigma> i)) / real m = (\<Sum>i = 0..<m. (\<sigma> i) / real m)" 
    using mgt0 sum_divide_distrib by blast  
  have blub: "{\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m. (\<sigma> i)) / real m\<bar>} \<subseteq> {x. \<epsilon> < ?avg x} \<union> {x. -\<epsilon> > ?avg x}"
    unfolding a apply(rule p) .


  have "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m. (\<sigma> i)) / real m\<bar>}
           \<le> 2 * exp (- 2 * real m * \<epsilon>\<^sup>2 / d\<^sup>2)"
    apply(rule order.trans)
     apply(rule subsetlesspmf) apply(rule blub)
    apply(rule order.trans)
     apply(rule measure_pmf.finite_measure_subadditive)
    subgoal by simp
    subgoal by simp
    apply(rule order.trans)
     apply(rule add_mono)
      apply(rule  ONESIDE)
     apply(rule OTHERSIDE)
    by simp 
} note aname = this

  let ?\<mu> = "\<lambda>i. measure_pmf.expectation (D i) id"
  thm aname[of "\<lambda>i. map_pmf (\<lambda>x. x - measure_pmf.expectation (D i) id) (D i)"
            "\<lambda>x. a-?\<mu> x" "\<lambda>x. b-?\<mu> x" "b-a", simplified ] Pi_pmf_map

  have "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m.  (\<sigma> i) - \<mu> i) / real m\<bar>}
    = measure_pmf.prob (map_pmf (\<lambda>\<sigma>. (\<lambda>i. if i<m then \<sigma> i - \<mu> i else dflt)) (Pi_pmf {0..<m} dflt D))
          {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m. \<sigma> i) / real m\<bar>}" by simp
    also have "\<dots>  = measure_pmf.prob (Pi_pmf {0..<m} dflt
          (\<lambda>i. map_pmf (\<lambda>v. if i<m then v - \<mu> i else dflt)  (D i))
        ) {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m. \<sigma> i) / real m\<bar>}"
      apply(subst Pi_pmf_map2[where dflt =dflt]) by simp_all 
  also have "\<dots> \<le> 2 * exp (- 2 * real m * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" 
     apply(rule aname[of _ "\<lambda>x.   a-\<mu> x" "\<lambda>x.   b-\<mu> x" "b-a"]) 
    subgoal apply simp using assms(2) .
    subgoal for i apply simp
    proof -
      assume *: " i < m"
      have "measure_pmf.expectation (D i) (\<lambda>x. x - \<mu> i) = measure_pmf.expectation (D i) (\<lambda>x. x + (- \<mu> i))" by simp
      also have "\<dots> = measure_pmf.expectation (D i) (\<lambda>x. x) + measure_pmf.expectation (D i) (\<lambda>x. (- \<mu> i))"
        apply(rule Bochner_Integration.integral_add)
        subgoal using *
          by(auto intro!: measure_pmf.integrable_const_bound[where B="max (abs a) (abs b)"]
                AE_pmfI dest: xbetweenab) 
        subgoal by simp
        done
      also have "measure_pmf.expectation (D i) (\<lambda>x. x) = \<mu> i"  using assms(1)[OF *] unfolding id_def  by simp
      also have "measure_pmf.expectation (D i) (\<lambda>x. (- \<mu> i))  = - \<mu> i"
        by simp
      finally show "measure_pmf.expectation (D i) (\<lambda>x. x - \<mu> i) = 0 " by simp
    qed
    subgoal by simp
    subgoal using ab2 by simp
    subgoal using ab2 by simp
    subgoal using ab2 by simp
    subgoal using PA by simp
    subgoal using PB by simp
    done
  finally show "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m.   (\<sigma> i) - \<mu> i) / real m\<bar>}
           \<le> 2 * exp (- 2 * real m * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" .
qed

 
lemma
  fixes g :: "nat \<Rightarrow> real" and
    R :: "real pmf"
  assumes "incseq g"   
    and tends_to_inf: "filterlim g at_top at_top"
    and "\<And>i. g i \<ge> 0" 
    and nn: "\<And>x. x \<in>set_pmf R \<Longrightarrow> x \<ge> 0"
  shows first_step': 
    "nn_integral (measure_pmf R) (\<lambda>x. x)
      \<le> g 0 + suminf (\<lambda>i. ennreal ( indicator {1..} i * (g i * measure_pmf.prob R {x. x > g (i-1)})) ) "
proof -
  let ?step = "\<lambda>x. g (LEAST i. x \<le> g i)"


  have tendstoinf: "\<And>K. \<exists>n\<^sub>0.\<forall>n\<ge>n\<^sub>0. (g n) \<ge> K" 
    using tends_to_inf 
    apply (subst (asm) filterlim_at_top[of g sequentially])
    using  eventually_at_top_linorder 
    using eventually_gt_at_top eventually_sequentially  
    by (metis gt_ex less_le_trans)  
  then have p: "\<And>K. \<exists>n. (g n) \<ge> K" by blast

  have *: "\<And>x.  x \<le> g (LEAST i. x \<le> g i)"     
    apply(rule LeastI_ex) by(rule p) 

  have char0': "\<And>x.  x \<le> g 0 \<Longrightarrow> (LEAST i. x \<le> g i) = 0 " by auto 
  have char0'': "\<And>x. (LEAST i. x \<le> g i) = 0  \<Longrightarrow>  x \<le> g 0 " 
    using * by metis
  have charn': "\<And>x n. n>0 \<Longrightarrow> (g (n-1) < x \<and> x \<le> g n) \<Longrightarrow> (LEAST i. x \<le> g i) = n "
    apply auto apply(rule Least_equality) apply simp
    using assms(1)[unfolded incseq_def]  
    by (metis Suc_pred less_Suc_eq_le less_le_trans not_le)  
  have charn'': "\<And>x n. n>0  \<Longrightarrow> (LEAST i. x \<le> g i) = n  \<Longrightarrow> (g (n-1) < x \<and> x \<le> g n)"
    apply auto
    subgoal 
      by (metis diff_Suc_Suc gr0_implies_Suc le_less_linear less_irrefl minus_nat.diff_0 not_less_Least not_less_less_Suc_eq)
    subgoal by (rule *)  
    done



  have char0: "\<And>x. (LEAST i. x \<le> g i) = 0 \<longleftrightarrow> (  x \<le> g 0)"  
    using char0' char0'' by metis
  have charn: "\<And>x n. n>0 \<Longrightarrow> (LEAST i. x \<le> g i) = n \<longleftrightarrow> (g (n-1) < x \<and> x \<le> g n)"
    using charn' charn'' by metis

  have a1: "nn_integral (measure_pmf R) (\<lambda>x. x)
    \<le> nn_integral (measure_pmf R) ?step"
    apply(rule nn_integral_mono_AE)
    apply (auto intro!: AE_pmfI)
    using * ennreal_leI by fastforce  
  also have "\<dots> = suminf (\<lambda>i. ennreal ( if i=0 then g 0 *  measure_pmf.prob R {x. x \<in> {0..g 0}}
                        else g i * measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}}))" 
  proof -
    let ?B = "\<lambda>n. if n = 0 then {..g 0} else {g (n-1)<..g n}"

    have dF: "disjoint_family ?B"
      unfolding disjoint_family_on_def  apply auto
        subgoal using  assms(1)[unfolded incseq_def]  
          by (meson not_less order_trans zero_le)  
        subgoal  using  assms(1)[unfolded incseq_def]    
          by (smt less_eq_nat.simps(1))  
        subgoal using  assms(1)[unfolded incseq_def]    
          by (smt Suc_pred assms(1) le_less_Suc_eq linorder_neqE_nat mono_invE)   
        done

    have *: "(\<Union>n. ?B n) = UNIV "
    proof (rule, simp, rule)
      fix x
      show "x \<in> (\<Union>n. if n = 0 then {..g 0} else {g (n - 1)<..g n})"
        apply(rule UN_I[where a="(LEAST i. x \<le> g i)"])
         apply simp 
        apply(cases "(LEAST i. x \<le> g i) = 0")
        subgoal apply simp using char0'' by blast
        subgoal apply simp using charn'' by auto
        done 
    qed

    have klar: "\<And>a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by simp
    have auchklar: "\<And>a b.{a<..b} =  {x. a < x \<and> x \<le> b}"
      unfolding greaterThanAtMost_def greaterThan_def atMost_def by auto

    have "nn_integral (measure_pmf R) ?step = 
       set_nn_integral (measure_pmf R) (\<Union>n. ?B n) ?step" unfolding * by simp 
    term "set_nn_integral (measure_pmf R) (\<Union>n. ?B n) ?step"
    also have "\<dots> = suminf  (\<lambda>i. ( if i=0 then nn_integral (measure_pmf R) (\<lambda>x. g 0 * indicator {0..g 0} x)
                        else nn_integral (measure_pmf R) (\<lambda>x. g i * indicator {g (i-1)<..g i} x)))"
      apply(subst nn_integral_disjoint_family)
      subgoal apply simp done
      subgoal apply simp done
      subgoal using dF .
      apply(rule suminf_cong)
      unfolding indicator_def apply auto 
      subgoal apply(rule nn_integral_cong_AE) apply(rule AE_pmfI)
        apply(drule assms(4))         
        by auto (* apply(rule ennreal_cong) using char0 by metis *) 
      subgoal for x apply(rule nn_integral_cong_AE) apply(rule AE_pmfI)
        apply(drule assms(4))  apply auto apply(subst charn'[of x]) by auto
      done
    also have "\<dots> = suminf  (\<lambda>i. ( if i=0 then ennreal (g 0) * nn_integral (measure_pmf R) (\<lambda>x.  indicator {0..g 0} x)
                        else  ennreal (g i) * nn_integral (measure_pmf R) (\<lambda>x. indicator {g (i-1)<..g i} x)))"
      using assms(3)  
      by (auto simp add: ennreal_mult nn_integral_cmult ennreal_indicator
          intro!:  suminf_cong nn_integral_cong klar)    
    also have "\<dots> = suminf  (\<lambda>i. ( if i=0 then ennreal  (g 0) * ennreal (measure_pmf.prob R {x. x \<in> {0..g 0}})
                        else  ennreal (g i) * ennreal (measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})))"
      apply(rule suminf_cong) apply auto
      subgoal apply(rule klar) apply simp 
        by (metis (mono_tags, lifting) antisym atLeastAtMost_iff measure_pmf.emeasure_eq_measure mem_Collect_eq subsetI)  
      subgoal apply(rule klar) apply simp
        apply(subst measure_pmf.emeasure_eq_measure) by (auto simp: auchklar)
      done
    also have "\<dots> = suminf  (\<lambda>i. ennreal ( if i=0 then  (g 0) *  (measure_pmf.prob R {x. x \<in> {0..g 0}})
                        else   (g i) *  (measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})))"
      apply(rule suminf_cong) apply auto
      subgoal apply(subst ennreal_mult) using assms(3) by auto
      subgoal apply(subst ennreal_mult) using assms(3) by auto
      done 
    finally show  ?thesis .
  qed    
  also have "\<dots> = g 0 * measure_pmf.prob R {x. x \<in> {0..g 0}}
                   + suminf (\<lambda>i. ennreal ( indicator {1..} i * (g i * measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})) ) "
  proof -
    have " suminf  (\<lambda>i. ennreal ( if i=0 then  (g 0) *  (measure_pmf.prob R {x. x \<in> {0..g 0}})
                        else   (g i) *  (measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})))
        = suminf (\<lambda>i. ennreal ( if i=0 then (g 0) *  (measure_pmf.prob R {x. x \<in> {0..g 0}}) else 0))
           + suminf (\<lambda>i. ennreal ( if i=0 then 0 else (g i) *  (measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})))"
      apply(subst suminf_add) by (auto intro: suminf_cong)
    also have " suminf (\<lambda>i. ennreal ( if i=0 then (g 0) *  (measure_pmf.prob R {x. x \<in> {0..g 0}})
                        else 0)) = (g 0) *  (measure_pmf.prob R {x. x \<in> {0..g 0}})"
      apply(subst suminf_finite[where N="{0}"]) by auto
    also have " suminf (\<lambda>i. ennreal ( if i=0 then 0 else (g i) *  (measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})))
        = suminf (\<lambda>i. ennreal ( indicator {1..} i * (g i * measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})) ) "
      by (auto intro!: suminf_cong)
    finally show "(\<Sum>i. ennreal (if i = 0 then g 0 * measure_pmf.prob R {x. x \<in> {0..g 0}} else g i * measure_pmf.prob R {x. x \<in> {g (i - 1)<..g i}})) =
            ennreal (g 0 * measure_pmf.prob R {x. x \<in> {0..g 0}}) + (\<Sum>i. ennreal (indicat_real {1..} i * (g i * measure_pmf.prob R {x. x \<in> {g (i - 1)<..g i}})))" .
  qed
  also have "\<dots> \<le> g 0 
                   + suminf (\<lambda>i. ennreal (indicator {1..} i * (g i * measure_pmf.prob R {x. x \<in> {g (i-1)<..g i}})) ) "
    apply(rule add_right_mono) apply(rule ennreal_leI)
    apply(rule order.trans) apply(rule mult_left_mono[of _ 1]) using assms(3) by auto
  also have "\<dots> \<le> g 0 
                   + suminf (\<lambda>i. ennreal (indicator {1..} i * (g i * measure_pmf.prob R {x. x > g (i-1)}) )) "
    apply(rule add_left_mono) apply(rule suminf_le)
    subgoal apply safe apply(rule ennreal_leI) apply(rule mult_left_mono) apply(rule mult_left_mono)
      apply(rule subsetlesspmf) using assms(3) by auto
    by auto 
  finally 
  show "nn_integral (measure_pmf R) (\<lambda>x. x)
      \<le> g 0 
                   + suminf (\<lambda>i. ennreal (indicator {1..} i * (g i * measure_pmf.prob R {x. x > g (i-1)}) )) "
    .

qed


(* by Max W. Haslbeck & Manuel Eberl *)
lemma nn_integral_nats_reals:
  shows "(\<integral>\<^sup>+ i. ennreal (f i) \<partial>count_space UNIV) =
         \<integral>\<^sup>+x\<in>{0::real..}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel"
proof -
  have "x < 1 + (floor x)"for x::real
    by linarith
  then have "\<exists>n. real n \<le> x \<and> x < 1 + real n" if "x \<ge> 0" for x
    using that of_nat_floor by (intro exI[of _ "nat (floor x)"]) auto
  then have "{0..} = (\<Union>n. {real n..<real (Suc n)})"
    by auto
  then have "\<integral>\<^sup>+x\<in>{0::real..}. f (nat \<lfloor>x\<rfloor>)\<partial>lborel = 
             (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel)"
    by (auto simp add: disjoint_family_on_def nn_integral_disjoint_family)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f n)\<partial>lborel)"
    by(subst suminf_cong,rule nn_integral_cong_AE)
      (auto intro!: eventuallyI  simp add: indicator_def floor_eq4)
  also have "\<dots> = (\<Sum>n. ennreal (f n))"
    by (auto intro!: suminf_cong simp add: nn_integral_cmult)
  also have "\<dots> = (\<integral>\<^sup>+ i. ennreal (f i) \<partial>count_space UNIV)"
    by (simp add: nn_integral_count_space_nat)
  finally show ?thesis
    by simp
qed


lemma Lemma_A4:
  assumes agt0: "a>0" and b: "b\<ge>exp 1"
    and absch: "\<And>t. t>0 \<Longrightarrow> measure_pmf.prob R {x. abs(f x-x')>t}\<le> 2*b*exp(-(t^2)/a^2)"
  shows "measure_pmf.expectation R (\<lambda>x. abs(f x-x')) \<le> a * (2+ sqrt (ln b))"
proof -
  let ?g = "\<lambda>i. a * (i + sqrt ( ln b ))"
 
  have bgt0: "b > 0" using b  
    using exp_gt_zero less_le_trans by blast  

  have bgt1: "ln b \<ge> 1" using b  
    by (simp add: bgt0 ln_ge_iff) 
  then have "ln b > 0"  
    by (smt ln_gt_zero)
  then have b': "sqrt (ln b) > 0" by simp 
  have g_pos: "\<And>i. i\<ge>0 \<Longrightarrow> ?g i > 0"
    apply(rule mult_pos_pos)
    subgoal using agt0 by simp
    subgoal using b' by linarith
    done
 
  from bgt1 have sqrtln_ge1: "sqrt (ln b) \<ge> 1" by simp
  then have sqrtb_D: "\<And>x. sqrt (ln b) \<le> x \<Longrightarrow> 1 \<le> x" by linarith

  have g_mono: "\<And>i j. i \<le> j \<Longrightarrow> ?g i \<le> ?g j"  
    using agt0 by auto 


  have ff: "\<And>n. n>0 \<Longrightarrow> real (n - Suc 0) = real n - 1" by simp
  have A: "\<integral>\<^sup>+ x. ennreal \<bar>f x - x'\<bar> \<partial>measure_pmf R
      \<le>  ?g 0 +
          (\<Sum>i. ennreal (indicat_real {1..} i * (?g i * measure_pmf.prob R {y. ?g (i-1) < \<bar>f y - x'\<bar>})))"
    apply(rule ord_le_eq_trans)
    apply(rule first_step'[where R="map_pmf (\<lambda>x. abs(f x-x')) R" and g="?g"
              ,  simplified nn_integral_map_pmf measure_map_pmf])
    subgoal unfolding incseq_def using g_mono by simp
    subgoal 
      (* LIM x sequentially. a * (real x + sqrt (ln b)) :> at_top *)
      using agt0 b'
      thm filterlim_real_sequentially
      sorry
    subgoal for i apply(cases i) using g_pos[of i] by auto 
    subgoal by auto
    subgoal apply simp done (*
      apply(rule ennreal_cong)  apply simp apply(rule suminf_cong)
      by(auto simp add: indicator_def ff )        *)
    done


  have kl: "\<And>x. x \<in> (\<lambda>x. x + sqrt (ln b)) ` {0..} \<longleftrightarrow> 1 \<le> x - (sqrt (ln b) - 1) " 
    unfolding  image_iff atLeast_def  apply auto subgoal for x
      apply(rule exI[where x="x-sqrt (ln b)"]) by simp 
    done
  { fix x :: real
    assume A: "1\<le>x"
    have "a * (b * ((x + 1) * exp (- ( x\<^sup>2 )))) \<le> a * (b * ((2 * x) * exp (- ( x\<^sup>2 ))))"
    apply(rule mult_left_mono)
    apply(rule mult_left_mono)
        apply(rule mult_right_mono)
        using A  agt0 bgt0 by auto
      also have "... = 2 * (a * (b   * (x * exp (- x\<^sup>2 ))))"
        apply simp done
      finally 
      have h: "a * (b * ((x + 1) * exp (- x\<^sup>2 ))) \<le> 2 * (a * (b   * (x * exp (- ( x\<^sup>2 )))))" .
    } note h = this


  have "( \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. (  ennreal (y * exp (- y\<^sup>2)))\<partial>lborel) = ennreal (exp (- (sqrt (ln b))\<^sup>2)/2)"
    apply(subst nn_integral_FTC_atLeast[where F="\<lambda>y. (-1) * exp (- y\<^sup>2)/2" and T=0])
    subgoal apply simp done
    subgoal for x apply(drule sqrtb_D)
      (* 1 \<le> x \<Longrightarrow> ((\<lambda>y. - 1 * exp (- y\<^sup>2) / 2) has_real_derivative x * exp (- x\<^sup>2)) (at x) *)
      sorry
    subgoal apply(drule sqrtb_D) by simp
    subgoal 
      (* ((\<lambda>y. - 1 * exp (- y\<^sup>2) / 2) \<longlongrightarrow> 0) at_top *)
      sorry
    subgoal by simp
    done

  also have "\<dots> = ennreal (exp (-  ln b)/2)"   using bgt1 by simp
  also have "\<dots> = ennreal (1 / (2 * b))" using exp_diff[where x="0" and y="ln b"] bgt0 by simp 
  finally have FTC: "( \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. (  ennreal (y * exp (- y\<^sup>2)))\<partial>lborel) = ennreal (1/(2*b))" .

  term summable
  have "suminf (\<lambda>i. ennreal ( indicat_real {Suc 0..} i * ?g i * measure_pmf.prob R {x. abs(f x-x')> ?g (i-1)  }))
        \<le> suminf (\<lambda>i. ennreal( indicat_real {Suc 0..} i * ?g i * (2*b*exp(-((?g (i-1))^2)/a^2))))"
    apply(rule suminf_le)
    subgoal
      apply safe
      subgoal for i
        apply(cases "i>0")
        subgoal  apply(rule ennreal_leI)
          apply(rule mult_left_mono) 
           apply(rule absch)
          subgoal using g_pos by simp
          subgoal   using g_pos[of "i"] by simp    
          done
        subgoal by simp
        done
      done
    subgoal by simp
    subgoal by simp
    done 
  also have "\<dots> = suminf (\<lambda>i. ennreal ( (2 * b * a) * (indicat_real {Suc 0..} i * ((real i + sqrt (ln b)) * (exp(-((?g (i-1))^2)/a^2))))))"
    by (auto simp: algebra_simps) (*
  also have "\<dots> = suminf (\<lambda>i. ( (ennreal (2 * b * a)) * ennreal (indicat_real {Suc 0..} i * ((real i + sqrt (ln b)) * (exp(-((?g (i-1))^2)/a^2))))))"
    sorry
  also have "\<dots> = (ennreal (2 * b * a)) * suminf (\<lambda>i. ennreal (indicat_real {Suc 0..} i *  ((real i + sqrt (ln b)) * (exp(-((?g (i-1))^2)/a^2)))))"
    apply(rule suminf_mult) 
    subgoal sorry
    done *)
  also have "\<dots> = suminf (\<lambda>i. ennreal ( (2 * b * a) * (indicat_real {Suc 0..} (real i) * ((real i + sqrt (ln b)) * (exp(-((a * (real (i) - 1 + sqrt (ln b)))^2)/a^2))))))"
    apply(rule suminf_cong) unfolding indicator_def 
    by(auto simp: ff) 
  also have "\<dots> = suminf (\<lambda>i. ennreal ( (2 * b * a) * (indicat_real {Suc 0..} (real i) * ((real i + sqrt (ln b)) * (exp(-(( (real (i) - 1 + sqrt (ln b)))^2)))))))"
    using agt0  by(simp add:  power2_eq_square)
  also have "\<dots> \<le> \<integral>\<^sup>+x\<in>{1..}. ennreal ( (2 * b * a) * ((x + sqrt (ln b)) * exp (- ((x - 1 + sqrt (ln b)))\<^sup>2)))\<partial>lborel"
      (is "suminf (\<lambda>i. ennreal (?f (real i))) \<le> nn_integral _  (\<lambda>x. ?g x * indicator ?A x)")
  proof -
    term set_nn_integral
    thm nn_integral_disjoint_family
    have is1: "\<And>n. emeasure (restrict_space lborel {real n..<1 + real n}) {real n..<1 + real n} = (1::ennreal)"
      apply(subst emeasure_restrict_space) by simp_all

    let ?B ="%i. {real i..<1 + real i}"
    have "disjoint_family ?B" by(auto simp: disjoint_family_on_def)

  have "x < 1 + (floor x)"for x::real
    by linarith
  then have "\<exists>n. real n \<le> x \<and> x < 1 + real n" if "x \<ge> 0" for x
    using that of_nat_floor by (intro exI[of _ "nat (floor x)"]) auto
  then have pf: " (\<Union>i.{real i..<1 + real i}) = {0..} "
    by auto


    have "suminf (\<lambda>i. ennreal (?f i)) = suminf (\<lambda>i. set_nn_integral lborel {real i..<1 + real i} (\<lambda>x. ?f i) )"
      
      apply(rule suminf_cong)
      apply(subst nn_integral_restrict_space[symmetric]) apply simp
      apply(subst nn_integral_const)  
      apply simp apply(subst is1) by simp  
    also have "\<dots> \<le>  suminf (\<lambda>i. set_nn_integral lborel {real i..<1 + real i} (\<lambda>x. ?f x) )"
      apply(rule suminf_le)
      subgoal apply safe
        apply(rule nn_integral_mono)
        unfolding indicator_def apply auto
        apply(rule ennreal_leI) apply(rule mult_left_mono)
        subgoal for n x  (* shit, I assumed that ?f is monotonically increasing, 
                              but it is actually monotonically decreasing! *)
          apply(rule mult_mono)
          subgoal by simp
          subgoal
            (* because of the exp ( - ... ), we can not show this!
              TODO: add 1 ?
             *)
            using b' apply (auto simp add: power2_eq_square )
            apply(rule mult_mono)  subgoal   sorry
            sorry
          sorry
        using agt0 bgt0 by simp
      apply simp_all done
    also have "\<dots> = \<integral>\<^sup>+x. ennreal (2 * b * a * (indicat_real {real (Suc 0)..} x * ((x + sqrt (ln b)) * exp (- ((x - 1 + sqrt (ln b)))\<^sup>2))))\<partial>lborel" 
      apply(subst nn_integral_disjoint_family[symmetric, where M=lborel and B="?B" and f="?f"])
      subgoal apply simp done
      subgoal apply simp done
      subgoal apply fact done
      subgoal unfolding pf apply(rule nn_integral_cong) unfolding indicator_def by simp
      done 
    also have "\<dots> = \<integral>\<^sup>+x\<in>{1..}. ennreal (2 * b * a * ( ((x + sqrt (ln b)) * exp (- ((x - 1 + sqrt (ln b)))\<^sup>2))))\<partial>lborel" 
      apply(rule nn_integral_cong)  unfolding indicator_def by auto
    finally 
    show ?thesis . 
  qed
    also have "\<dots> = \<integral>\<^sup>+x\<in>{1..}. ennreal ( (2 * b * a) * ((((sqrt (ln b) - 1) + x) + 1) * exp (- (((sqrt (ln b) - 1) + x))\<^sup>2)))\<partial>lborel"
      by(simp add: algebra_simps ) 
    also
    let ?f = "\<lambda>x. ennreal ( (2 * b * a) * ((x + 1) * exp (- ((x  ))\<^sup>2 ))) *  indicator {1..} (x- (sqrt (ln b)-1))"
    have "\<dots> = \<integral>\<^sup>+ x. ?f ((sqrt (ln b) - 1 ) + x) \<partial>lborel" by simp 
    also 
    have "\<dots> = \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. ennreal (2 * b * a * ((y+1) * exp (-  y\<^sup>2 )))\<partial>lborel"         
      apply(subst nn_integral_real_affine[where c=1 and t="sqrt (ln b)-1", symmetric,  simplified])
      subgoal by simp  
      subgoal by (simp add: indicator_def) 
      done 
    also have "\<dots> \<le> \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. ennreal (2 * b * a * (2*y * exp (- y\<^sup>2 )))\<partial>lborel"   
      apply(rule nn_integral_mono_AE) apply(rule AE_I2)
      subgoal for x apply(auto simp : indicator_def intro!: ennreal_leI  split: if_splits)
        apply(rule h) using sqrtln_ge1 by linarith
      done
    also 
    have "\<dots> = \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. (ennreal (4* b * a) * ennreal (y * exp (- y\<^sup>2)))\<partial>lborel"
      apply(rule nn_integral_cong)
      apply(auto simp: indicator_def)
      apply(subst  ennreal_mult[symmetric]) using agt0 bgt0  apply auto
       apply(rule mult_nonneg_nonneg) subgoal using b' by linarith
      subgoal apply simp done
      apply(rule ennreal_cong) by simp
    also have "\<dots> = ennreal (4* b * a) * ( \<integral>\<^sup>+y\<in>{sqrt (ln b)..}. (  ennreal (y * exp (-  y\<^sup>2 )))\<partial>lborel)"
      (* linear combination *) sorry
    also have "\<dots> = ennreal (2 * a)"
      apply(subst FTC) 
      apply(subst  ennreal_mult[symmetric]) using agt0 bgt0 by auto 
    finally have 2: "(\<Sum>i. ennreal (indicat_real {Suc 0..} i * (a * (real i + sqrt (ln b))) * measure_pmf.prob R {x. a * (real (i - 1) + sqrt (ln b)) < \<bar>f x - x'\<bar>}))
  \<le> ennreal (2 * a) " .    


    have nontopI: "\<And>T f . T \<le> ennreal f \<Longrightarrow> T \<noteq> \<top>"  
      using ennreal_less_top leD by blast  

      have p: "(\<Sum>i. ennreal (indicat_real {Suc 0..} i * (a * (real i + sqrt (ln b))) * measure_pmf.prob R {x. a * (real (i - 1) + sqrt (ln b)) < \<bar>f x - x'\<bar>}))
        = ennreal (\<Sum>i.  (indicat_real {Suc 0..} i * (a * (real i + sqrt (ln b))) * measure_pmf.prob R {x. a * (real (i - 1) + sqrt (ln b)) < \<bar>f x - x'\<bar>}))"
        apply(rule suminf_ennreal)
        subgoal apply simp apply(rule mult_nonneg_nonneg) apply(rule mult_nonneg_nonneg) using agt0 apply auto
          using b' by(auto intro!: mult_nonneg_nonneg)
        subgoal apply(rule nontopI[OF 2]) .
        done

      have 22: "(\<Sum>i.  (indicat_real {1..} i * (a * (real i + sqrt (ln b))) * measure_pmf.prob R {x. a * (real (i - 1) + sqrt (ln b)) < \<bar>f x - x'\<bar>})) 
              \<le> 2*a"
        using 2[unfolded p]
        apply(subst (asm) ennreal_le_iff) using agt0 by auto

      thm suminf_ennreal

  thm nn_integral_real_affine[where c=1 and t="sqrt (ln b)", symmetric, simplified]
 


  term "integral\<^sup>L"

      find_theorems "_ has_derivative _" exp
      find_theorems "_ has_derivative _" "( * )"
      find_theorems "_ has_field_derivative _" "( * )"
      find_theorems "_ has_real_derivative _" "( * )"

  (* letzter schritt in der abschätzung *)
  thm nn_integral_FTC_atLeast
  thm nn_integral_real_affine[where c = 1 and t = 1, simplified] (* Integral-Shift um 1 *)
  find_theorems set_nn_integral

  thm pmf_expectation_eq_infsetsum


  have "\<integral>\<^sup>+ x. ennreal \<bar>f x - x'\<bar> \<partial>measure_pmf R
  \<le> ennreal (a * (0 + sqrt (ln b))) 
      + (\<Sum>x. ennreal ( indicat_real {1..} x * (a * (real x + sqrt (ln b))
                       * measure_pmf.prob R {y. a * (real (x - 1) + sqrt (ln b)) < \<bar>f y - x'\<bar>})))"
    using A .
  also have "\<dots> = ennreal (a * (0 + sqrt (ln b)))
       + (\<Sum>x. ennreal (indicat_real {1..} x * (a * (real x + sqrt (ln b))) * measure_pmf.prob R {y. a * (real (x - 1) + sqrt (ln b)) < \<bar>f y - x'\<bar>}))"
    apply simp   apply(rule suminf_cong)
    by(auto simp add: indicator_def   ) 
  also have "\<dots> \<le> ennreal (a * (0 + sqrt (ln b))) + ennreal (  2 * a)"
    apply(rule add_left_mono)
    using 2 apply simp done
  also have "\<dots> = ennreal (a * (0 + sqrt (ln b))+ 2 * a)"
    apply(subst ennreal_plus[symmetric]) using agt0 b' by auto
  also have "\<dots> \<le> ennreal (a * (2 + sqrt (ln b)))" by (simp add: algebra_simps)
  finally have ALL: "\<integral>\<^sup>+ x. ennreal \<bar>f x - x'\<bar> \<partial>measure_pmf R \<le> ennreal (a * (2 + sqrt (ln b)))" .

  find_theorems measure_pmf.expectation ennreal 
  term "integral\<^sup>L"

  show "measure_pmf.expectation R (\<lambda>x. abs(f x-x')) \<le> (a* (2+sqrt(ln b)))"
    apply(rule integral_real_bounded)
    subgoal apply(rule mult_nonneg_nonneg) using agt0 b' by auto
    subgoal using ALL .
    done  
qed

lemma PP': " nn_integral p (\<lambda>x. nn_integral p (\<lambda>y. f x y))
    = nn_integral p (\<lambda>x. nn_integral p (\<lambda>y. f y x))"
  using nn_integral_linear' by auto

lemma PP: "(\<And>x y. f y x = g y x) \<Longrightarrow> nn_integral p (\<lambda>x. nn_integral p (\<lambda>y. f x y))
    = nn_integral p (\<lambda>x. nn_integral p (\<lambda>y. g y x))"
  apply(subst PP') by simp


lemma nn_hardstep'': 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> ennreal"
  shows "finite A \<Longrightarrow> A \<subseteq> {0..<m} \<Longrightarrow> 
        nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H.   (f (  (\<lambda>i. g (S' i) h - g (S i) h) ))))
      = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H.   (f ( (\<lambda>i. if i\<in>A then (g (S i) h - g (S' i) h) else (g (S' i) h - g (S i) h)) ))))"
  unfolding Samples_def
proof (induction  rule: Finite_Set.finite_induct)
  case empty 
  then show ?case by simp
next
  case (insert x F) 
  then have "x < m" by auto
  then have B: "{0..<m} = insert x ({0..<m} - {x})"
    "finite ({0..<m} - {x})" "x\<notin>  ({0..<m} - {x})"
    by auto
  from insert(4) have F: "F \<subseteq> {0..<m}" by auto
  have "nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D)) (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. g (S' i) h - g (S i) h))) =
    nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D))
           (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. if i \<in> F then g (S i) h - g (S' i) h else g (S' i) h - g (S i) h)))"
    using insert(3)[OF F] .
  also have "\<dots> = 
    nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. nn_integral (Pi_pmf {0..<m} undefined (\<lambda>_. D))
           (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. if i \<in> insert x F then g (S i) h - g (S' i) h else g (S' i) h - g (S i) h)))"
  
    apply(subst B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst nn_integral_map_pmf)
    apply(subst nn_integral_pair_pmf')
    apply(subst nn_integral_linear')

    apply(subst (2)B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst nn_integral_map_pmf)
    apply(subst nn_integral_pair_pmf')
    apply(subst (3) nn_integral_linear')
    apply(subst (2) nn_integral_linear')

    apply simp


    apply(subst (3) B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst nn_integral_map_pmf)
    apply(subst nn_integral_pair_pmf')
    apply(subst (4) nn_integral_linear')
    apply(subst (5) nn_integral_linear')


    apply(subst (4) B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst nn_integral_map_pmf)
    apply(subst nn_integral_pair_pmf')
    apply(subst (5) nn_integral_linear')
    apply(subst (6) nn_integral_linear') 

    apply(rule nn_integral_cong)
    
    apply(rule nn_integral_cong)

    subgoal for S S'  
      apply(rule PP)
    apply(rule SUP_cong) apply simp
    apply(rule arg_cong[where f=f]) apply(rule ext)
    subgoal for  v v' h i using insert(2) by auto
    done
  done
  finally show ?case .
qed 


lemma nn_hardstep': 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  assumes "finite A" "A={i. \<sigma> i = -1}" "(\<And>i. \<sigma> i \<in>{-1,1})" "A\<subseteq>{0..<m}"
  shows "nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal ( f (  (\<lambda>i. g (S' i) h - g (S i) h) ))))
      = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) ))))"
proof -
  from assms have inA: "\<And>i. i\<in>A \<Longrightarrow> \<sigma> i = -1" by auto
  from assms have notinA: "\<And>i. i\<notin>A  \<Longrightarrow> \<sigma> i = 1" by auto

  have "nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal ( f (  (\<lambda>i. g (S' i) h - g (S i) h) ))))
      = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f ( (\<lambda>i. if i\<in>A then (g (S i) h - g (S' i) h) else (g (S' i) h - g (S i) h)) ))))"
    apply(rule nn_hardstep'') by fact+ 
  also have "\<dots> 
      = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) ))))"
    apply(rule nn_integral_cong)
    apply(rule nn_integral_cong) 
    apply(rule SUP_cong) apply simp apply(rule ennreal_cong)
    apply(rule arg_cong[where f=f]) apply (rule ext)

    using inA notinA apply auto done
  finally show ?thesis .
qed 
  


lemma nn_hardstep: 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  shows "finite {i. \<sigma> i = -1} \<Longrightarrow> (\<And>i. \<sigma> i \<in>{-1,1}) \<Longrightarrow> {i. \<sigma> i = -1}\<subseteq>{0..<m}
      \<Longrightarrow> nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal ( f ( (\<lambda>i. g (S' i) h - g (S i) h) ))))
      = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) ))))"
  using nn_hardstep' by blast


definition Samples1 :: "nat \<Rightarrow> (real) pmf \<Rightarrow> ((nat \<Rightarrow> real)) pmf" where
  "Samples1 n D = Pi_pmf {0..<n} (1::real) (\<lambda>_. D)"

lemma Samples1_set_pmf : "y \<in> set_pmf (Samples1 m (pmf_of_set {- 1, 1}))
  \<Longrightarrow> (\<forall>i< m. y i \<in> {-1,1})"
  sorry

lemma assumes "f \<in> set_pmf (Samples1 m (pmf_of_set {- 1, 1}))"
  shows Samples1_finite:  " finite {i. f i = - 1}"
    and Samples1_subm: "{i. f i = -1} \<subseteq> {0..<m}"
proof -
  have *: "finite {0..<m}" by auto
  from assms set_Pi_pmf_subset[OF *, where dflt=1]
  have "f \<in> {f. \<forall>x. x \<notin> {0..<m} \<longrightarrow> f x = 1}" 
  unfolding Samples1_def by blast
  then have "\<And>x. x \<notin> {0..<m} \<Longrightarrow> f x = 1" by auto
  then have "{i. f i \<noteq> 1} \<subseteq> {0..<m}" by blast
  then show "{i. f i = -1} \<subseteq> {0..<m}" by force
  with * finite_subset  show " finite {i. f i = - 1}"  by blast
qed 
                  
lemma set_pmf_Pi_pmf2: "set_pmf (Pi_pmf S dflt D) \<subseteq> {f. \<forall>s\<in>S. f s \<in> set_pmf (D s)}"
  unfolding Pi_pmf_def apply(subst set_embed_pmf)
  subgoal by (auto simp add: prod_nonneg)  
  subgoal  sorry
  subgoal apply auto sorry
  done

lemma Samples1_set: "f \<in> set_pmf (Samples1 m (pmf_of_set {- 1, 1})) \<Longrightarrow> f i \<in> {- 1, 1}"
  unfolding Samples1_def
proof -
  have *: "finite {0..<m}" by auto
  assume **: "f \<in> set_pmf (Pi_pmf {0..<m} 1 (\<lambda>_. pmf_of_set {- 1, 1}))"
  show ?thesis
  proof (cases "i<m")
    case True
    from ** have "f : {f. \<forall>s\<in>{0..<m}. f s \<in> set_pmf (pmf_of_set {- 1, 1})}"
      using set_pmf_Pi_pmf2 by fast
    then have "\<And>s. s < m \<Longrightarrow> f s \<in>  {- 1, 1}"
      apply(subst (asm) set_pmf_of_set) by auto
    with True show ?thesis by simp
  next
    case False
    with ** set_Pi_pmf_subset[OF *, where dflt=1]
    have "f \<in> {f. \<forall>x. x \<notin> {0..<m} \<longrightarrow> f x = 1}" by blast
    then have "\<And>x. x \<notin> {0..<m} \<Longrightarrow> f x = 1" by auto
    then have "\<And>i. i\<ge>m \<Longrightarrow> f i = 1" by auto
    then show ?thesis using False by auto
  qed
qed



lemma ranh: "\<forall>h\<in>H_map. ran h \<subseteq> Y" using Hdef mapify_def
  by (smt imageE mem_Collect_eq option.simps(1) ran_def subset_iff)

lemma domh: "\<forall>h\<in>H_map. dom h = UNIV"
  by (simp add: mapify_def) 

lemma restrictH_map_conv: "restrictH H_map C Y = (\<lambda>h. restrict_map h C) ` H_map" 
  using auxtemp domh ranh by blast

lemma restrictH_nonempty: "restrictH H_map C Y \<noteq> {}"
  unfolding restrictH_map_conv using nnH by auto



lemma "h\<in>H \<Longrightarrow> mapify h |` C \<in> restrictH H_map C Y"
  by (auto simp: restrictH_map_conv)
  

lemma restrict_mapify_same: "\<And>x. (x\<in>C \<Longrightarrow> (mapify h |` C) x = Some (h x))"
  unfolding mapify_def restrict_map_def by auto   



lemma fixes f :: "'e \<Rightarrow> 'd \<Rightarrow> real"
  shows braa: "\<And>\<rho>. finite S \<Longrightarrow> S \<noteq>{} \<Longrightarrow>
      {\<sigma>. MAXIMUM S (\<lambda>h. f \<sigma> h) > \<rho> } \<subseteq> \<Union> { {\<sigma>. f \<sigma> h > \<rho>}   |h. h\<in>S }" 
  apply rule  
  apply simp   
  by (metis (no_types, lifting) Max_in finite_imageI imageE image_is_empty mem_Collect_eq)  


lemma set_pmf_Samples: "\<And>S i. S \<in> set_pmf (Samples m D) \<Longrightarrow> i < m \<Longrightarrow> S i \<in> set_pmf D"
  sorry

lemma convex_abs: "convex_on UNIV abs" unfolding convex_on_def apply auto   
        subgoal for a b c d apply(cases "a\<ge>0"; cases "b\<ge>0"; cases "c * a + d * b\<ge>0") apply auto
          subgoal  
            by (simp add: mult_nonneg_nonpos)  
          subgoal  
            by (simp add: mult_nonpos_nonneg) 
          subgoal  
            by (smt mult_nonpos_nonneg)  
          done
        done

lemma nervig1: 
  fixes Z :: "real set"
  assumes bdd: "bdd_above Z" 
    and ne: "Z\<noteq>{}" 
  and *: "(\<forall>x\<in>Z. y \<le> x)"
  shows
    "y \<le> Sup Z"
proof -
  from ne obtain z where "z\<in>Z" by blast
  with * show ?thesis
    apply(intro cSup_upper2[where x=z])
    using bdd by auto
qed
lemma nervig2: 
  fixes Z :: "real set"
  assumes bdd: "bdd_above Z" 
    and ne: "Z\<noteq>{}" 
  and *: "(\<forall>x\<in>Z. x \<le> y)"
  shows
    " Sup Z \<le> y"
proof -
  from ne obtain z where "z\<in>Z" by blast
  with * show ?thesis
    apply(subst cSup_le_iff) 
    using bdd by auto
qed

lemma a[simp]: "m > 0 \<Longrightarrow> integrable (measure_pmf (Samples m D)) (\<lambda>xa. \<bar>TrainErr xa {0..<m} h - TrainErr x {0..<m} h\<bar>)"
  apply(auto intro!: measure_pmf.integrable_const_bound AE_pmfI)
  using TError_bounded .


lemma bdd_above_expectation: 
  "m>0 \<Longrightarrow> bdd_above ((\<lambda>h. measure_pmf.expectation (Samples m D) (\<lambda>S'. \<bar>TrainErr S' {0..<m} h - TrainErr x {0..<m} h\<bar>)) ` H)"
      unfolding bdd_above_def
      apply(rule exI)
      apply safe
      apply(rule measure_pmf.integral_le_const)
      apply simp 
        apply(rule AE_pmfI)
        apply(rule TError_bounded)   by simp 
    
lemma abs_nnI: 
  fixes a b :: real
  shows "0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b"
  apply(subst abs_of_nonneg) by auto


lemma
  fixes f :: "_ \<Rightarrow> real" and m::nat and b :: real
  assumes "m>0"
  "(\<And>i. i\<in>{0..<m} \<Longrightarrow> f i \<le> b)"
shows sumabsch: "sum f {0..<m} \<le>  b * m"
proof -
  have "sum f {0..<m} \<le> sum (\<lambda>_. b) {0..<m}"
    apply(rule sum_mono) using assms by simp
  also have "\<dots> = b * m "
    apply(subst sum_constant) by simp
  finally show ?thesis .
qed




lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and delta_nn: "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(m/2))} \<ge> 1 - \<delta>"
      (is "measure_pmf.prob _ {S. \<forall>h\<in>H. ?err S h \<le> ?bnd } \<ge> _")
proof -
  have m_gt0: "m>0" sorry
  have "growth (2 * m) > 1" sorry
  then have "ln (growth (2 * m)) > 0" by simp
  then have "sqrt (ln (growth (2 * m))) > 0" by simp
  then have bnd_gt0: "?bnd > 0" using m_gt0 delta_nn
    by (auto intro!: divide_pos_pos add_pos_pos) 
  have finiteY: "finite Y" sorry (* hmm, not so sure here! *)

  
  have samples_domain: "\<And>S i. S \<in> set_pmf (Samples m D) \<Longrightarrow> i < m \<Longrightarrow> S i \<in> (X\<times>Y)"
    using assms(1)  set_pmf_Samples by blast


  thm measure_pmf.jensens_inequality[where q=abs]
  thm measure_pmf.jensens_inequality[where q=A]
  thm measure_pmf.jensens_inequality[where q="(\<lambda>x. abs (x - C))"]

 

  {
    fix S S' :: "nat \<Rightarrow> 'a \<times> 'b"
    let ?C = "{fst (S i)|i. i\<in>{0..<m}} \<union> {fst (S' i)|i. i\<in>{0..<m}}"
    text \<open>Next, fix @{term S} and @{term S'}, and let @{term ?C} be the instances appearing in
            @{term S} and @{term S'}. Then, we can take the supremum only over
             @{term "h\<in>(restrictH H_map ?C Y)"}. Therefore,\<close>

    have pp: "\<And>S. card {fst (S i)|i. i\<in>{0..<m}} \<le> m"
      apply(rule order.trans)
       apply(rule surj_card_le[where A="{0..<m}"])   by auto

    have "card ?C \<le> card {fst (S i)|i. i\<in>{0..<m}} + card {fst (S' i)|i. i\<in>{0..<m}}"
      by (rule card_Un_le)
    also have "\<dots> \<le> 2*m"
      using pp[of S] pp[of S'] by simp
    finally have cardC: "card ?C \<le> 2 * m" . 

    have C_nonempty: "?C \<noteq> {}" using m_gt0 by auto
    
    have finite_restrC: "finite (restrictH H_map ?C Y)"
      apply(rule finiteres) apply simp using finiteY by simp

    assume "S \<in> set_pmf (Samples m D)" "S' \<in> set_pmf (Samples m D)"
    with samples_domain have CX: "?C \<subseteq> X"  
      by fastforce  
    have *: "card (restrictH H_map ?C Y) \<le> growth (card ?C)"
      unfolding growth_def
      apply(rule Max_ge)
      subgoal apply auto sorry
      subgoal using CX by blast
      done
    have C_bd_growth: "card (restrictH H_map ?C Y) \<le> growth (2*m)"
      apply(rule order.trans)
      apply(rule *) apply(rule growth_mono)  apply(rule cardC) done
    have C_gt0: "card ?C > 0" using m_gt0 by(auto simp add: card_gt_0_iff)
    have finite_C: "finite ?C" using cardC C_nonempty m_gt0 by auto
    term "MAXIMUM"
    term "restrictH H_map ?C Y"
    term "integral\<^sup>N (measure_pmf (Samples1 m (pmf_of_set {-1,1::real})))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m )"
    have "
        measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m )
        \<le> measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0))) {0..<m})  \<bar>  / m ))" 
      (is "_ \<le> measure_pmf.expectation _ (\<lambda>\<sigma>. Max (?A \<sigma>))")
    proof -
      {
        fix \<sigma> and h :: "'a \<Rightarrow> 'b"
        have P: "\<And>x. x\<in>?C \<Longrightarrow> (mapify h |` ?C) x = Some (h x)"
          apply(rule restrict_mapify_same) by simp

        have pff: "(\<Sum>i = 0..<m. \<sigma> i * ((case S' i of (x, y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) - (case S i of (x, y) \<Rightarrow> if h x \<noteq> y then 1 else 0)))
        = (\<Sum>i = 0..<m.
           \<sigma> i *
           ((case S' i of
             (x, y) \<Rightarrow> if (mapify h |` ?C) x \<noteq> Some y then 1 else 0) -
            (case S i of
             (x, y) \<Rightarrow> if (mapify h |` ?C) x \<noteq> Some y then 1 else 0)))"
          apply(rule sum.cong) apply simp
          subgoal for x
            apply(cases "S' x") apply(simp only: prod.case)
            apply(subst P)
            subgoal by auto
            apply(cases "S x") apply(simp only: prod.case)
            apply(subst P) 
            subgoal by auto 
            by auto 
          done
      } note pff=this


      show ?thesis 
        apply(rule expectation_mono)
        subgoal unfolding Samples1_def apply(rule measure_pmf.integrable_const_bound[where B=1])
          apply auto
          sorry
        subgoal unfolding Samples1_def apply auto sorry
        subgoal for \<sigma>
      apply(rule ord_le_eq_trans[OF _ cSup_eq_Max])
      subgoal 
        apply(rule cSUP_mono)
        subgoal using nnH by simp
        subgoal unfolding bdd_above_def
          apply(rule exI[where x="Max (?A \<sigma>)"])
          apply simp apply safe
          apply(rule Max.coboundedI)
          subgoal using finite_restrC by simp 
          by blast
        subgoal for h
          apply(rule bexI[where x="restrict_map (mapify h) ?C"])
          subgoal 
            unfolding pff ..
          subgoal by (auto simp: restrictH_map_conv)  
          done
        done 
      subgoal using finite_restrC by simp  
      subgoal apply auto using restrictH_nonempty by simp
      done
    done
  qed 
  also
  let ?bl = "(\<lambda>v h i. v * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                         -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)))"
  let ?blub = "(\<lambda>\<sigma> h i.?bl (\<sigma> i) h i )"
      let ?bla = "\<lambda>\<sigma> h. (sum (?blub \<sigma> h) {0..<m})    / m "
    { 
      term measure_pmf.prob
      fix h :: "'a \<Rightarrow> 'b option"    

      fix \<rho>::real
      assume "\<rho>>0"
  let ?bl' = "(\<lambda>v h i. if i<m then v * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                         -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0))
                        else 1)"
      have "measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho> }
                   = measure_pmf.prob (Pi_pmf {0..<m} 1 (\<lambda>_. pmf_of_set {- 1, 1}))
          {\<sigma>. \<rho> < \<bar>(\<Sum>i = 0..<m. ?bl (\<sigma> i) h i) / real m\<bar>}" unfolding Samples1_def by simp
      also have "\<dots> = measure_pmf.prob 
            (map_pmf (\<lambda>\<sigma>. (\<lambda>i. ?bl' (\<sigma> i) h i)) (Pi_pmf {0..<m} 1 (\<lambda>_. pmf_of_set {- 1, 1})))
                  {\<sigma>. \<rho> < \<bar>(\<Sum>i = 0..<m. \<sigma> i) / real m\<bar>}"
        apply simp done
      also have "\<dots> = measure_pmf.prob (Pi_pmf {0..<m} 1 
              (\<lambda>i. map_pmf (\<lambda>v. ?bl' v h i) (pmf_of_set {- 1, 1})))
          {\<sigma>. \<rho> < \<bar>(\<Sum>i = 0..<m. \<sigma> i) / real m\<bar>}"
        apply (subst Pi_pmf_map2[where dflt=1]) apply simp apply simp apply simp done 
      also have "\<dots> = measure_pmf.prob (Pi_pmf {0..<m} 1 
              (\<lambda>i. map_pmf (\<lambda>v. ?bl' v h i) (pmf_of_set {- 1, 1})))
          {\<sigma>. \<rho> < \<bar>(\<Sum>i = 0..<m. \<sigma> i)\<bar> / real m}"
        apply(rule arg_cong[where f="measure_pmf.prob (Pi_pmf {0..<m} 1 
              (\<lambda>i. map_pmf (\<lambda>v. ?bl' v h i) (pmf_of_set {- 1, 1})))"])
        by auto
      also have "\<dots>   \<le> 2 * exp (-  real m  * \<rho>^2 / 2)"
        apply(rule order.trans) 
         apply(rule hoeffding_ineq[where \<mu>="\<lambda>i.0" and a="-1" and b="1", simplified])
        subgoal by (simp add: integral_pmf_of_set)  
        subgoal for i apply (simp add: measure_pmf_of_set)
          apply(cases "S i"; cases "S' i") by auto
        subgoal apply fact done
        subgoal using m_gt0 by simp
        subgoal by simp
        done
      finally have "measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho> }
                \<le> 2 * exp (-  real m  * \<rho>^2 / 2)" .
   
    } note gaga = this
 

    have argh: "\<And>\<rho>. {\<sigma>. MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar>) > \<rho> }
                  \<subseteq> (\<Union>h\<in>(restrictH H_map ?C Y).  {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho>} )"
      subgoal for \<rho>
        using braa[OF finite_restrC restrictH_nonempty, of \<rho> "\<lambda>\<sigma> h. \<bar>?bla \<sigma> h\<bar>"] by blast
      done

      thm measure_pmf.finite_measure_subadditive_finite

      {fix \<rho> :: real
        assume rhogt0: "\<rho>>0" 
        have "measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) {\<sigma>. MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar>) > \<rho> }
          \<le> measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) (\<Union>h\<in>(restrictH H_map ?C Y).  {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho>} )"
          apply(rule subsetlesspmf) by(rule argh)
        also have "\<dots> \<le> (\<Sum>h\<in>restrictH H_map ?C Y.
                     measure_pmf.prob (Samples1 m (pmf_of_set {- 1, 1})) {\<sigma>. \<rho> < \<bar>?bla \<sigma> h\<bar>})" 
           apply(rule measure_pmf.finite_measure_subadditive_finite)
          subgoal using finite_restrC by auto
          subgoal by auto
          done
        also have "\<dots> \<le> (\<Sum>h\<in>restrictH H_map ?C Y. 2 * exp (-  real m  * \<rho>^2 / 2) )" 
           apply(rule sum_mono) apply (rule gaga) using rhogt0 by simp
        also have "\<dots> = 2 * card (restrictH H_map ?C Y) * exp (-  m  * \<rho>^2 / 2)" 
          apply(subst sum_constant_scale) by simp
        finally
    (* using union_bound *)
    have " measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) {\<sigma>. MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar>) > \<rho> }
                    \<le> 2 * card (restrictH H_map ?C Y) * exp (-  m  * \<rho>^2 / 2)" .
  } note ppp = this


  thm Lemma_A4

  have "measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0))) {0..<m})  \<bar>  / m )) 
        \<le> ?bnd * \<delta>" 
  proof -
    have ff: "\<And>x::real. x-0 = x" by simp

    have pap: "\<And>(f::_\<Rightarrow>real) A. finite A \<Longrightarrow>  A\<noteq>{} \<Longrightarrow> \<bar>MAXIMUM A (\<lambda>i. \<bar>f i\<bar>)\<bar> = MAXIMUM A (\<lambda>i. \<bar>f i\<bar>)"
      apply(rule abs_of_nonneg)
      apply(subst Max_ge_iff) by auto 
       
    from Lemma_A4[where x'=0 and b="card (restrictH H_map ?C Y)" and a="1/sqrt(m/2)"
                                            and f="\<lambda>\<sigma>. MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar> )"  ]
    have therule: "\<And>R. 0 < 1 / sqrt (real m / 2) \<Longrightarrow>
exp 1 \<le> real (card (restrictH H_map ?C Y)) \<Longrightarrow>
(\<And>t. 0 < t \<Longrightarrow>
      measure_pmf.prob R
       {x. t < \<bar>(MAX h\<in>restrictH H_map ({fst (S i) |i. i \<in> {0..<m}} \<union> {fst (S' i) |i. i \<in> {0..<m}}) Y.
                    \<bar>?bla x h\<bar>) -
                0\<bar>}
      \<le> 2 * real (card (restrictH H_map ({fst (S i) |i. i \<in> {0..<m}} \<union> {fst (S' i) |i. i \<in> {0..<m}}) Y)) *
         exp (- t\<^sup>2 / (1 / sqrt (real m / 2))\<^sup>2)) \<Longrightarrow>
measure_pmf.expectation R
 (\<lambda>x. \<bar>(MAX h\<in>restrictH H_map ({fst (S i) |i. i \<in> {0..<m}} \<union> {fst (S' i) |i. i \<in> {0..<m}}) Y.
           \<bar>(\<Sum>i = 0..<m.
                x i *
                ((case S' i of (x, y) \<Rightarrow> if h x \<noteq> Some y then 1 else 0) - (case S i of (x, y) \<Rightarrow> if h x \<noteq> Some y then 1 else 0))) /
            real m\<bar>)\<bar>)
\<le> 1 / sqrt (real m / 2) *
   (2 + sqrt (ln (real (card (restrictH H_map ?C Y)))))" unfolding ff
      by blast

    have i: " (1 / sqrt (real m / 2))\<^sup>2 = 1 / (m/2)" using m_gt0 
      by (simp add: power_divide)  

    have "measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0))) {0..<m})  \<bar>  / m ))
         = measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar> ))"
      by simp 
    also have "\<dots> = measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<bar>MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar> )\<bar>)"
      apply(subst pap)
      subgoal using finite_restrC by simp
      subgoal using restrictH_nonempty by simp
      by simp
    also have "\<dots> \<le> 1 / sqrt (real m / 2) * (2 + sqrt (ln (real (card (restrictH H_map ?C Y)))))" 
      apply(rule therule)
      subgoal using m_gt0 by auto
      subgoal    sorry
      subgoal for t unfolding ff
        apply(rule order.trans) apply(subst pap)
        subgoal using finite_restrC by simp
        subgoal using restrictH_nonempty by simp
         apply(rule ppp[of t]) apply simp apply simp
        apply(rule mult_left_mono)
        subgoal using m_gt0 by (auto simp: power_divide)     
        subgoal by simp
        done
      done 
    also    
    have "\<dots> \<le> 1 / sqrt (real m / 2) * (2 + sqrt (ln (real (growth (2 * m)))))"
      apply(rule mult_left_mono)
      subgoal apply simp apply(subst ln_le_cancel_iff)
        subgoal  apply simp sorry
        subgoal sorry
        apply simp using  C_bd_growth by simp
      subgoal using m_gt0 by simp
      done
    also have "\<dots> \<le> ?bnd * \<delta>"
      using delta_nn m_gt0 apply auto 
      apply(rule divide_right_mono) by auto 
    finally show ?thesis .
  qed
  finally 
  have " 
        measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m )
          \<le> ?bnd * \<delta>" .
} note fff = this

  { fix S S'
  have " 
        nn_integral (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. ennreal ( \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m) )
          \<le> ?bnd * \<delta>" sorry
  } note fff' = this


  have "\<And>P M. (\<forall>x. x\<in>set_pmf M \<longrightarrow> P x) \<Longrightarrow> almost_everywhere (measure_pmf M) P"
     
    using AE_pmfI by blast  

  have abs_twoway: "\<And>a b:: real. b\<ge>0 \<Longrightarrow> -b \<le> a \<Longrightarrow> a\<le>b \<Longrightarrow> abs a \<le> b" by auto

  have abs_exp_diff_ub: 
    "\<And>y x. \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} x) - TrainErr y {0..<m} x\<bar> \<le> 1+1"
    apply(rule order.trans)
     apply(rule abs_triangle_ineq4)   apply(rule add_mono)
     apply(rule abs_nnI)
      apply(rule measure_pmf.integral_ge_const)
    using m_gt0 apply(auto intro!: measure_pmf.integrable_const_bound AE_pmfI abs_nnI TrainErr_le1  simp: TrainErr_nn )
     apply(rule TrainErr_le1) apply auto
    apply(rule measure_pmf.integral_le_const)
    using m_gt0 apply(auto intro!: measure_pmf.integrable_const_bound AE_pmfI abs_nnI TrainErr_le1  simp: TrainErr_nn )
    apply(rule TrainErr_le1) apply auto
    done 
  have abs_exp_diff_ub2: 
    "\<And>y x. \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} x - TrainErr y {0..<m} x)\<bar> \<le> 2" 
    apply(rule abs_twoway) apply simp
    subgoal  
      apply(rule measure_pmf.integral_ge_const)
      using m_gt0 by(auto intro!: measure_pmf.integrable_const_bound AE_pmfI abs_bound_neg TError_bounded TrainErr_le1) 
    subgoal 
      apply(rule measure_pmf.integral_le_const)
      using m_gt0 by(auto intro!: measure_pmf.integrable_const_bound AE_pmfI  TError_bounded TrainErr_le1 intro: abs_bound_pos) 
    done  

  thm ennreal_Sup
  have ennreal_Sup': "\<And>A. A \<noteq> {} \<Longrightarrow> ennreal (\<Squnion>A) \<le> (\<Squnion>a\<in>A. ennreal a)"
      subgoal for A apply(cases "(\<Squnion>a\<in>A. ennreal a) = \<top> ")
      subgoal by (metis top_greatest)  
      subgoal using ennreal_Sup by simp
      done
    done

  have "nn_integral (Samples m D) (\<lambda>S. Sup (?err S ` H))
      \<le> nn_integral (Samples m D) (\<lambda>S.  (\<Squnion>h\<in>H. ennreal \<bar>PredErr D h - TrainErr S {0..<m} h\<bar>))"
    apply(rule nn_integral_mono) apply(rule order.trans)
     apply(rule ennreal_Sup') using nnH apply simp 
    by simp
  also have "\<dots> = nn_integral (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. ennreal \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'.  TrainErr S' {0..<m} h )
               - TrainErr S {0..<m} h\<bar>)" apply(subst PredErr_as_expectation[where m=m]) ..
  also have "... = nn_integral (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. ennreal \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h - TrainErr S {0..<m} h )
               \<bar>)"
  proof -

    { fix S h
      have " measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h - TrainErr S {0..<m} h )
            = measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h + (- TrainErr S {0..<m} h) )" by simp
      also have "\<dots> = measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h) - TrainErr S {0..<m} h "

        apply(subst Bochner_Integration.integral_add)
        subgoal using m_gt0 apply (auto intro!: measure_pmf.integrable_const_bound AE_pmfI abs_nnI TrainErr_nn)
            apply(rule TrainErr_le1) by auto
        subgoal by simp
        by simp
      finally have "measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h - TrainErr S {0..<m} h )
          = measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h) - TrainErr S {0..<m} h".
    } note * = this

    show ?thesis
      unfolding * .. 
  qed
  also have "\<dots> \<le> nn_integral (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. ennreal (measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> )) )"
    apply(rule nn_integral_mono)  
    apply(rule SUP_mono ) (*
    subgoal (* bdd_above side condition *)
      using m_gt0 by(auto intro!: measure_pmf.integral_le_const bdd_aboveI2
            measure_pmf.integrable_const_bound AE_pmfI intro: TError_bounded ) *)
    subgoal for x n apply(rule bexI[where x=n])
      apply(rule ennreal_leI)
       apply(rule  measure_pmf.jensens_inequality[where q=abs, where I=UNIV])
      subgoal (* integrable side condition *)
        using m_gt0 by(auto intro!: measure_pmf.integrable_const_bound AE_pmfI intro: TError_bounded) 
      subgoal apply auto done
      subgoal by simp
      subgoal (* integrable side condition *)
        using m_gt0 by(auto intro!: measure_pmf.integrable_const_bound AE_pmfI intro: TError_bounded) 
      subgoal using convex_abs by simp         
      subgoal by simp
      done
    done
  thm measure_pmf.jensens_inequality[where q="(\<lambda>x. Sup ((f x)`H))", where I=UNIV]
  also have "\<dots> \<le> nn_integral (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. (nn_integral (Samples m D)
         (\<lambda>S'. ennreal \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> )) )"
    apply(rule nn_integral_mono)
    apply(rule SUP_mono) subgoal for x h apply(rule bexI[where x=h])  
       apply(subst measure_pmf.ennreal_integral_real[symmetric, where B=2])
      subgoal by simp
      subgoal apply(rule AE_pmfI) apply(rule ennreal_leI) apply simp using TError_bounded[OF m_gt0] by blast
      subgoal by simp
      subgoal by simp
      subgoal by simp
      done
    done  
  also
  let ?g = "(\<lambda>S' S h. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar>)" 
  
    have "\<dots> \<le> nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> ) )"
      apply(rule nn_integral_mono)  
       apply(rule nn_integral_Sup_le) done  
   also have "\<dots> = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal \<bar>sum (\<lambda>i. case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m} / card {0..<m}
                       - sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m} / card {0..<m}\<bar> ) )"
      unfolding TrainErr_def apply simp done
    also have "\<dots> = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal \<bar>(sum (\<lambda>i. case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}  
                       - sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}) / m  \<bar> ) )"
      apply(rule nn_integral_cong)
      apply(rule nn_integral_cong)
      apply(rule arg_cong[where f="SUPREMUM H"]) apply(rule ext)
      apply(rule ennreal_cong)
      apply(rule arg_cong[where f="abs"]) 
      using m_gt0  
      by (simp add: diff_divide_distrib) 
    also have "\<dots> = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal \<bar>(sum (\<lambda>i. (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)) {0..<m}) / m  \<bar> ) )"  
      apply(subst sum_subtractf) by auto
    also have "\<dots> = nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (\<bar>(sum (\<lambda>i. (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)) {0..<m})  \<bar>  / m) ) )" 
      by simp
    term "pmf_of_set {-1,1::real}"
    term " Pi_pmf {0..<m} undefined (\<lambda>_. pmf_of_set {-1,1::real})"
    term "Samples m (pmf_of_set {-1,1::real})"
    term "measure_pmf.expectation (Samples m (pmf_of_set {-1,1::real}))"
    also have "\<dots> = nn_integral (Samples1 m (pmf_of_set {-1,1::real})) (\<lambda>\<sigma>.
           nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. ennreal (\<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m )) ))"
      (is "?L = nn_integral ?U (\<lambda>\<sigma>. nn_integral ?M1 (\<lambda>S. nn_integral ?M2 (\<lambda>S'. 
             \<Squnion>h\<in>H. ennreal ((?f::(nat \<Rightarrow> real) \<Rightarrow> real) ((\<lambda>i. \<sigma> i * ( ?g (S' i) h -  ?g (S i) h )))))))")

    proof - 
      term ?f
      have "?L = nn_integral ?U (\<lambda>\<sigma>. ?L)"
        apply(subst nn_integral_const) by simp
      also have "\<dots> = nn_integral ?U (\<lambda>\<sigma>. nn_integral ?M1 (\<lambda>S. nn_integral ?M2 (\<lambda>S'. 
             \<Squnion>h\<in>H. ennreal ( ?f ((\<lambda>i. \<sigma> i * ( ?g (S' i) h -  ?g (S i) h )))))))"
        apply(rule nn_integral_cong_AE, rule AE_pmfI)
        apply(rule nn_hardstep)
        subgoal using Samples1_finite .    
        subgoal using Samples1_set .    
        subgoal using Samples1_subm .
        done
      finally show ?thesis . 
    qed
    
    also have "\<dots> = 
           nn_integral (Samples m D)
           (\<lambda>S. nn_integral (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>. nn_integral (Samples m D)
         (\<lambda>S'. 
               \<Squnion>h\<in>H. ennreal (\<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m ) )))"  
      term "nn_integral (measure_pmf (Samples m D))"
      find_theorems nn_integral name:Fubini
      term "indicator {h x} y"
      thm indicator_def
      apply -  
      apply(subst  nn_integral_linear')
        (* some missing side conditions here ! *)
      by simp
    also have "\<dots> = 
           nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. nn_integral (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. ennreal ( \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m ) )))"  
      apply(subst (2) nn_integral_linear') .. 
    also have "\<dots> \<le> 
           nn_integral (Samples m D)
           (\<lambda>S.  nn_integral (Samples m D)
         (\<lambda>S'. ?bnd * \<delta>))"
      apply(rule nn_integral_mono)  
      apply(rule nn_integral_mono)  
      by(rule fff') 
    also have "\<dots> =   ?bnd * \<delta>"
      apply(subst nn_integral_const)
      apply(subst nn_integral_const) by simp  
  finally   

  have bd_exp_nn: "nn_integral (measure_pmf (Samples m D)) (\<lambda>S. ennreal (Sup (?err S ` H))) \<le> ennreal (?bnd * \<delta>)"
    by simp
  have bd_exp: "measure_pmf.expectation (Samples m D) (\<lambda>S. Sup (?err S ` H)) \<le> ?bnd * \<delta>"
    apply(rule integral_real_bounded)
    subgoal apply(rule mult_nonneg_nonneg) using bnd_gt0 delta_nn by auto
    apply(rule bd_exp_nn)
    done

  note f = measure_pmf.prob_neg[where M="(Samples m D)", simplified]

  have *: "{S. Sup (?err S ` H) > ?bnd } = {S. \<not> Sup (?err S ` H) \<le> ?bnd }" by auto

  thm integral_real_bounded

  have "measure_pmf.prob (Samples m D) {S. Sup (?err S ` H) > ?bnd }       
         \<le> measure_pmf.expectation (Samples m D) (\<lambda>S. Sup (?err S ` H)) / ?bnd"
    apply (rule markov_inequality)  
    sorry

  also have "\<dots> \<le> (?bnd * \<delta>) / ?bnd "
    apply (rule divide_right_mono)
    using bd_exp bnd_gt0 by auto 
  also have "\<dots> = \<delta>" using bnd_gt0 by auto
  finally have fa: "measure_pmf.prob (Samples m D) {S. Sup (?err S ` H) > ?bnd } \<le> \<delta>"
    .
  have "1 - \<delta> \<le> 
         measure_pmf.prob (Samples m D) {S. Sup (?err S ` H) \<le> ?bnd }"     
    apply(rule A) using fa[unfolded * f] .
  also have "\<dots> \<le>  measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. ?err S h \<le> ?bnd }"
    apply(rule subsetlesspmf)
    apply safe 
    apply(subst (asm) cSup_le_iff)
    subgoal by auto
    subgoal using Error_bounded[OF m_gt0] by fast
    subgoal by simp 
    done   
  finally show ?thesis .

qed

   
  

  
   

end