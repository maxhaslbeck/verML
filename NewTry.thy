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
  shows expectation_Pi_pmf:
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
    apply simp
    unfolding expectation_pair_pmf
    apply(subst prod.insert) apply fact apply fact
    apply simp unfolding p by simp
  also have "\<dots> = (\<Prod>x\<in>insert a A. measure_pmf.expectation (p x) (f x))"
    apply(subst insert(3))
    apply(subst prod.insert) apply fact apply fact by simp
  finally  show ?case .
qed


 
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

term measure_pmf.expectation 

lemma markov_inequality:
  "measure_pmf.prob D {x. f x > a} \<le> (measure_pmf.expectation D f / a)"
  using integral_Markov_inequality[where c=a]

  sorry

lemma markov_inequality':
  "
  integrable (measure_pmf D) f \<Longrightarrow>
  AE x in measure_pmf D. 0 \<le> f x \<Longrightarrow> a>0 \<Longrightarrow> measure_pmf.prob D {x. f x \<ge> a} \<le> (measure_pmf.expectation D f / a)"
  using integral_Markov_inequality[where c=a and u=f and M=D, unfolded measure_pmf.emeasure_eq_measure]  
    sorry


thm integral_Markov_inequality
thm integral_Markov_inequality
thm nn_integral_Markov_inequality

   

lemma A :
  fixes a b :: real
  shows "a\<ge>1-b \<Longrightarrow> 1-a\<le>b" by auto

lemma "abs(PredErr D h - TrainErr S {0..<m} h) \<ge> 0"
  by auto

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


lemma expectation_Sup_le: "(\<Squnion>h\<in>H. measure_pmf.expectation D (f h))
         \<le> measure_pmf.expectation D (\<lambda>S'. \<Squnion>h\<in>H. f h S')"
  sorry

lemma expectation_linear:
    "measure_pmf.expectation M (\<lambda>S. measure_pmf.expectation M2 (f S))
        = measure_pmf.expectation M2 (\<lambda>S2. measure_pmf.expectation M (\<lambda>S. f S S2))"
  sorry
  

(* by auto3 aka Manuel Eberl: *)
lemma convex_on_exp: 
  fixes l :: real
  assumes "l > 0"
  shows   "convex_on UNIV (\<lambda>x. exp(l*x))"
  using assms
  by (intro convex_on_realI[where f' = "\<lambda>x. l * exp (l * x)"]) (auto
intro!: derivative_eq_intros)

lemma hoeffdings_lemma:
  fixes a b :: real
  assumes range: "\<And>i. measure_pmf.prob D {x. a \<le> x \<and> x \<le> b} = 1" 
  and E0: "measure_pmf.expectation D id = 0" and "l>0" and aleb: "a\<le>b"
shows  "measure_pmf.expectation D (\<lambda>x. exp (l*x)) \<le> exp ( l^2 *(b-a)^2 / 8)"
proof -
  let ?f = "(\<lambda>x. exp (l * x))"

  from range have xbetweenab: "\<And>x. x\<in>set_pmf D \<Longrightarrow> x \<in> {x. a \<le> x \<and> x \<le> b}"
    sorry
  have ab: "a<b" and al0: "a<0" and bg0: "0<b" sorry

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
  

  have "measure_pmf.expectation D ?f \<le> measure_pmf.expectation D (\<lambda>x. (b - x) / (b - a) * exp (l * a) + (x-a)/(b-a) * exp (l * b))"
    apply(rule expectation_mono) 
    subgoal sorry
    subgoal sorry
    apply(rule *)
    using xbetweenab by auto
  also 
  have "\<dots> = (b - measure_pmf.expectation D id) / (b - a) * exp (l * a) + (measure_pmf.expectation D id-a)/(b-a) * exp (l * b)"
    (is "?L = ?R")  
  proof -
    have "?L = measure_pmf.expectation D (\<lambda>x. (b + (x * -1)) / (b - a) * exp (l * a) + (x + (- a)) / (b - a) * exp (l * b))" by simp
    also have "\<dots> = measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a) * exp (l * a)) + measure_pmf.expectation D (\<lambda>x. (x + - a) / (b - a) * exp (l * b))"
      apply(rule Bochner_Integration.integral_add)
      subgoal sorry
      subgoal sorry
      done
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a) * exp (l * a)) = measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a))  * exp (l * a)"
      by (rule integral_mult_left_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) / (b - a)) =  measure_pmf.expectation D (\<lambda>x. (b + x * -1) ) / (b - a)  " 
      by(rule integral_divide_zero)
    also have "measure_pmf.expectation D (\<lambda>x. (b + x * -1) ) = measure_pmf.expectation D (\<lambda>_. b) +  measure_pmf.expectation D (\<lambda>x. x * -1 )" 
      apply(rule Bochner_Integration.integral_add)
      subgoal sorry
      subgoal sorry
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
      subgoal sorry
      subgoal sorry
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
    subgoal   sorry
    subgoal   sorry
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
  have 3: "?L ?h \<le> ?h^2 / 8" sorry

  have 4: "?h^2 = l^2 *(b-a)^2" by algebra

  note 1
  also have "(b / (b - a)) * ?f a - (a/(b-a)) * ?f b = exp (?L ?h)" using 2 by simp
  also have "\<dots> \<le> exp (?h^2 / 8)" using 3 ..
  also have "\<dots> \<le> exp ( l^2 *(b-a)^2 / 8)" unfolding 4 ..
  finally show ?thesis .
qed


lemma braaaaaaa:
  assumes [simp]: "finite A"
  shows   "measure_pmf.expectation (Pi_pmf A dflt p) (\<lambda>y. \<Sum>x\<in>A. (Q x) (y x)) =
             (\<Sum>x\<in>A. measure_pmf.expectation (p x) (Q x))"
  (* induction over A? *)
  sorry

term "Pi_pmf {0..<n} undefined (\<lambda>i. D i)"
term sum              
term measure_pmf.prob 
lemma hoeffding_ineq:
  assumes
      "\<And>i::nat. measure_pmf.expectation (D i) (f i) = \<mu> i"
    and "\<And>i. measure_pmf.prob (D i) {x. a \<le> x \<and> x \<le> b} = 1"  and "(\<epsilon>::real)>0"
  shows "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. abs(sum  (\<lambda>i. f i (\<sigma> i) - \<mu> i) {0..<m} / m) > \<epsilon> }
             \<le> 2 * exp (- 2 * m * \<epsilon>^2 / (b-a)^2 )"
  sorry





lemma hoeffding_ineq_forreal:
  assumes
      "\<And>i::nat. i < m \<Longrightarrow> measure_pmf.expectation (D i) id = \<mu> i"
    and "\<And>i. i<m \<Longrightarrow> measure_pmf.prob (D i) {x. a \<le> x \<and> x \<le> b} = 1"  and "(\<epsilon>::real)>0"
  shows "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. abs(sum  (\<lambda>i. (\<sigma> i) - \<mu> i) {0..<m} / m) > \<epsilon> }
             \<le> 2 * exp (- 2 * m * \<epsilon>^2 / (b-a)^2 )"
proof -
  have ab2: "a<b" sorry
  have mgt0: "m>0"   sorry
  {
    fix D :: "nat \<Rightarrow> real pmf" and a b :: "nat \<Rightarrow> real" and d :: real
    assume ONE: "\<And>i. i<m \<Longrightarrow> measure_pmf.prob (D i) {x. a i \<le> x \<and> x \<le> b i} = 1"  
    assume TWO: "\<And>x. x<m \<Longrightarrow> measure_pmf.expectation (D x) (\<lambda>x. id (x / real m)) = 0"
    assume defd: "\<And>i. i<m \<Longrightarrow> b i - a i = d"
    assume dgt0: "d>0" 
    assume ab: "\<And>i. i<m \<Longrightarrow> a i \<le> b i"  
    assume ab2: "\<And>i. i<m \<Longrightarrow> a i < b i"  
  thm markov_inequality
  { fix M and \<epsilon>::real and l :: real
    assume "l>0"
    then 
    have "measure_pmf.prob M {x. x > \<epsilon>} = measure_pmf.prob M {x. exp (l * x) > exp (l * \<epsilon>)}"
      by simp
    also have "\<dots> \<le>  measure_pmf.expectation M (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)"
      apply(rule markov_inequality) 
      done
    finally have "measure_pmf.prob M {x. x > \<epsilon>} \<le> measure_pmf.expectation M (\<lambda>x. exp (l * x)) / exp (l * \<epsilon>)" .
  } note first = this
  { 
    fix   p and Q and l :: real 
    have "measure_pmf.expectation (Pi_pmf  {0..<m} dflt p) (\<lambda>y. exp (l * (\<Sum>x\<in> {0..<m}. (Q x) (y x) / m) ))
          = measure_pmf.expectation (Pi_pmf  {0..<m} dflt p) (\<lambda>y. ( \<Prod>x\<in> {0..<m}. exp (l * (Q x) (y x) / m)))"
      by (auto simp:  sum_distrib_left exp_sum)     
    also have "\<dots> = (\<Prod>x\<in> {0..<m}. measure_pmf.expectation (p x) (\<lambda>y. ( exp (l * (Q x) y / m))))"
      by (auto intro: expectation_Pi_pmf)
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

    from first[OF lgt0, of "map_pmf ?avg (Pi_pmf {0..<m} dflt D)" \<epsilon>]
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

    have ppa: "\<And>x. ?mavg x = (\<Sum>xa = 0..<m. - x xa / real m)"
      using mgt0 unfolding sum_negf[symmetric] by simp
    from first[OF lgt0, of "map_pmf ?mavg (Pi_pmf {0..<m} dflt D)" \<epsilon>]
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
        apply(rule Bochner_Integration.integral_add) apply auto sorry
      also have "measure_pmf.expectation (D i) (\<lambda>x. x) = \<mu> i"  using assms(1)[OF *] unfolding id_def  by simp
      also have "measure_pmf.expectation (D i) (\<lambda>x. (- \<mu> i))  = - \<mu> i"
        by simp
      finally show "measure_pmf.expectation (D i) (\<lambda>x. x - \<mu> i) = 0 " by simp
    qed
    subgoal by simp
    subgoal using ab2 by simp
    subgoal using ab2 by simp
    subgoal using ab2 by simp
    done
  finally show "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. \<epsilon> < \<bar>(\<Sum>i = 0..<m.   (\<sigma> i) - \<mu> i) / real m\<bar>}
           \<le> 2 * exp (- 2 * real m * \<epsilon>\<^sup>2 / (b - a)\<^sup>2)" .
qed
 





lemma Lemma_A4:
  assumes "a>0" "b\<ge>exp 1" "\<And>t. t>0 \<Longrightarrow> measure_pmf.prob R {x. abs(f x-x')>t}\<le> 2*b*exp(-(t^2)/a^2)"
  shows "measure_pmf.expectation R (\<lambda>x. abs(f x-x')) \<le> a * (2+ sqrt (ln b))"
  sorry


lemma PP': " measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation p (\<lambda>y. f x y))
    = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation p (\<lambda>y. f y x))"
  using expectation_linear by auto

lemma PP: "(\<And>x y. f y x = g y x) \<Longrightarrow> measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation p (\<lambda>y. f x y))
    = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation p (\<lambda>y. g y x))"
  apply(subst PP') by simp


lemma hardstep'': 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  shows "finite A \<Longrightarrow> A \<subseteq> {0..<m} \<Longrightarrow> 
        measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f (  (\<lambda>i. g (S' i) h - g (S i) h) )))
      = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. if i\<in>A then (g (S i) h - g (S' i) h) else (g (S' i) h - g (S i) h)) )))"
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
  have "measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D)) (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. g (S' i) h - g (S i) h))) =
    measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D))
           (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. if i \<in> F then g (S i) h - g (S' i) h else g (S' i) h - g (S i) h)))"
    using insert(3)[OF F] .
  also have "\<dots> = 
    measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D))
     (\<lambda>S. measure_pmf.expectation (Pi_pmf {0..<m} undefined (\<lambda>_. D))
           (\<lambda>S'. \<Squnion>h\<in>H. f (\<lambda>i. if i \<in> insert x F then g (S i) h - g (S' i) h else g (S' i) h - g (S i) h)))"
  
    apply(subst B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst integral_map_pmf)
    apply(subst expectation_pair_pmf)
    apply(subst expectation_linear)

    apply(subst (2)B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst integral_map_pmf)
    apply(subst expectation_pair_pmf)
    apply(subst (3) expectation_linear)
    apply(subst (2) expectation_linear)

    apply simp


    apply(subst (3) B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst integral_map_pmf)
    apply(subst expectation_pair_pmf)
    apply(subst (4) expectation_linear)
    apply(subst (5) expectation_linear)


    apply(subst (4) B(1)) 
    apply(subst Pi_pmf_insert[OF B(2,3)])
    apply(subst integral_map_pmf)
    apply(subst expectation_pair_pmf)
    apply(subst (5) expectation_linear)
    apply(subst (6) expectation_linear) 

    apply(rule arg_cong[where f="measure_pmf.expectation (Pi_pmf ({0..<m} - {x}) undefined (\<lambda>_. D))"])
    apply(rule ext)
    
    apply(rule arg_cong[where f="measure_pmf.expectation (Pi_pmf ({0..<m} - {x}) undefined (\<lambda>_. D))"])
    apply(rule ext)

    subgoal for S S'  
      apply(rule PP)
    apply(rule SUP_cong) apply simp
    apply(rule arg_cong[where f=f]) apply(rule ext)
    subgoal for  v v' h i using insert(2) by auto
    done
  done
  finally show ?case .
qed 


lemma hardstep': 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  assumes "finite A" "A={i. \<sigma> i = -1}" "(\<And>i. \<sigma> i \<in>{-1,1})" "A\<subseteq>{0..<m}"
  shows "measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f (  (\<lambda>i. g (S' i) h - g (S i) h) )))
      = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) )))"
proof -
  from assms have inA: "\<And>i. i\<in>A \<Longrightarrow> \<sigma> i = -1" by auto
  from assms have notinA: "\<And>i. i\<notin>A  \<Longrightarrow> \<sigma> i = 1" by auto

  have "measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f (  (\<lambda>i. g (S' i) h - g (S i) h) )))
      = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. if i\<in>A then (g (S i) h - g (S' i) h) else (g (S' i) h - g (S i) h)) )))"
    apply(rule hardstep'') by fact+ 
  also have "\<dots> 
      = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) )))"
    apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"]) apply(rule ext)
    apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"]) apply(rule ext)
    apply(rule SUP_cong) apply simp
    apply(rule arg_cong[where f=f]) apply (rule ext)

    using inA notinA apply auto done
  finally show ?thesis .
qed 

lemma hardstep: 
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  shows "finite {i. \<sigma> i = -1} \<Longrightarrow> (\<And>i. \<sigma> i \<in>{-1,1}) \<Longrightarrow> {i. \<sigma> i = -1}\<subseteq>{0..<m}
      \<Longrightarrow> measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. g (S' i) h - g (S i) h) )))
      = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. f ( (\<lambda>i. \<sigma> i * (g (S' i) h - g (S i) h)) )))"
  using hardstep' by blast


definition Samples1 :: "nat \<Rightarrow> (real) pmf \<Rightarrow> ((nat \<Rightarrow> real)) pmf" where
  "Samples1 n D = Pi_pmf {0..<n} (1::real) (\<lambda>_. D)"

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
 

lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and delta_nn: "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(m/2))} \<ge> 1 - \<delta>"
      (is "measure_pmf.prob _ {S. \<forall>h\<in>H. ?err S h \<le> ?bnd } \<ge> _")
proof -
  have bnd_gt0: "?bnd > 0"   sorry
  have m_gt0: "m>0" sorry
  have finiteY: "finite Y" sorry (* hmm, not so sure here! *)

  
  have samples_domain: "\<And>S i. S \<in> set_pmf (Samples m D) \<Longrightarrow> i < m \<Longrightarrow> S i \<in> (X\<times>Y)"
    using assms(1)  set_pmf_Samples by blast


  thm measure_pmf.jensens_inequality[where q=abs]
  thm measure_pmf.jensens_inequality[where q=A]
  thm measure_pmf.jensens_inequality[where q="(\<lambda>x. abs (x - C))"]



  have tt: "\<And>S' S h. sum (\<lambda>i. case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}  
                       - sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}
        = sum (\<lambda>i. (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       - (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)) {0..<m}"
  apply(subst sum_subtractf) by auto

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
         apply(rule hoeffding_ineq_forreal[where \<mu>="\<lambda>i.0" and a="-1" and b="1", simplified])
        subgoal by (simp add: integral_pmf_of_set)  
        subgoal for i apply (simp add: measure_pmf_of_set)
          apply(cases "S i"; cases "S' i") by auto
        subgoal apply fact done
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


  have "measure_pmf.expectation (Samples m D) (\<lambda>S. Sup (?err S ` H))
      =measure_pmf.expectation (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'.  TrainErr S' {0..<m} h )
               - TrainErr S {0..<m} h\<bar>)" apply(subst PredErr_as_expectation[where m=m]) ..
  also have "... \<le> measure_pmf.expectation (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. \<bar>measure_pmf.expectation (Samples m D) (\<lambda>S'. TrainErr S' {0..<m} h - TrainErr S {0..<m} h )
               \<bar>)"
    apply(rule expectation_mono)
    subgoal sorry
    subgoal sorry
    apply(rule cSUP_mono[OF nnH])
    subgoal sorry
    subgoal for x n apply(rule bexI[where x=n]) sorry (* not sure here! *)
    done  
  also have "\<dots> \<le> measure_pmf.expectation (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> ) )"
    apply(rule expectation_mono)
    subgoal sorry
    subgoal sorry
    apply(rule cSUP_mono[OF nnH])
    subgoal sorry
    subgoal for x n apply(rule bexI[where x=n])
       apply(rule  measure_pmf.jensens_inequality[where q=abs, where I=UNIV])
      subgoal   sorry
      subgoal apply auto done
      subgoal by simp
      subgoal  sorry
      subgoal   sorry
      subgoal by simp
      done
    done
  thm measure_pmf.jensens_inequality[where q="(\<lambda>x. Sup ((f x)`H))", where I=UNIV]
  also
  let ?g = "(\<lambda>S' S h. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar>)" 
    have "\<dots> \<le> measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> ) )"
      apply(rule expectation_mono) 
    subgoal sorry
    subgoal sorry
      apply(rule expectation_Sup_le) done 
    also have "\<dots> = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. \<bar>sum (\<lambda>i. case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m} / card {0..<m}
                       - sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m} / card {0..<m}\<bar> ) )"
      unfolding TrainErr_def apply simp done
    also have "\<dots> = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}  
                       - sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) {0..<m}) / m  \<bar> ) )"
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply(rule ext) 
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply (rule ext)
      apply(rule arg_cong[where f="SUPREMUM H"]) apply(rule ext)
      apply(rule arg_cong[where f="abs"]) 
      using m_gt0  
      by (simp add: diff_divide_distrib) 
    also have "\<dots> = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)) {0..<m}) / m  \<bar> ) )"
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply(rule ext) 
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply (rule ext)
      apply(rule arg_cong[where f="SUPREMUM H"]) apply(rule ext)
      apply(rule arg_cong[where f="abs"]) 
      unfolding tt .. 
    also have "\<dots> = measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. (\<bar>(sum (\<lambda>i. (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)) {0..<m})  \<bar>  / m) ) )"
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply(rule ext) 
      apply(rule arg_cong[where f="measure_pmf.expectation (Samples m D)"])
      apply (rule ext)
      apply(rule arg_cong[where f="SUPREMUM H"]) apply(rule ext)
      by simp
    term "pmf_of_set {-1,1::real}"
    term " Pi_pmf {0..<m} undefined (\<lambda>_. pmf_of_set {-1,1::real})"
    term "Samples m (pmf_of_set {-1,1::real})"
    term "measure_pmf.expectation (Samples m (pmf_of_set {-1,1::real}))"
    also have "\<dots> = measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real})) (\<lambda>\<sigma>.
           measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<Squnion>h\<in>H. (\<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m )) ))"
      (is "?L = measure_pmf.expectation ?U (\<lambda>\<sigma>. measure_pmf.expectation ?M1 (\<lambda>S. measure_pmf.expectation ?M2 (\<lambda>S'. 
             \<Squnion>h\<in>H. (?f::(nat \<Rightarrow> real) \<Rightarrow> real) ((\<lambda>i. \<sigma> i * ( ?g (S' i) h -  ?g (S i) h ))))))")

    proof - 
      term ?f
      have "?L = measure_pmf.expectation ?U (\<lambda>\<sigma>. ?L)"
        apply(subst expectation_const) ..
      also have "\<dots> = measure_pmf.expectation ?U (\<lambda>\<sigma>. measure_pmf.expectation ?M1 (\<lambda>S. measure_pmf.expectation ?M2 (\<lambda>S'. 
             \<Squnion>h\<in>H. ?f ((\<lambda>i. \<sigma> i * ( ?g (S' i) h -  ?g (S i) h ))))))"
        apply(rule expectation_cong)
        apply(rule hardstep)
        subgoal using Samples1_finite .    
        subgoal using Samples1_set .    
        subgoal using Samples1_subm .
        done
      finally show ?thesis . 
    qed
    
    also have "\<dots> = 
           measure_pmf.expectation (Samples m D)
           (\<lambda>S. measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>. measure_pmf.expectation (Samples m D)
         (\<lambda>S'. 
               \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m ) ))"  
      apply(subst expectation_linear) ..
    also have "\<dots> = 
           measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. measure_pmf.expectation (Samples1 m (pmf_of_set {-1,1::real}))
         (\<lambda>\<sigma>.
               \<Squnion>h\<in>H. \<bar>(sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0)  
                       -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0))) {0..<m})  \<bar>  / m ) ))"  
      apply(subst (2) expectation_linear) .. 
    also have "\<dots> \<le> 
           measure_pmf.expectation (Samples m D)
           (\<lambda>S.  measure_pmf.expectation (Samples m D)
         (\<lambda>S'. ?bnd * \<delta>))"
      apply(rule expectation_mono)
      subgoal sorry
      subgoal sorry
      apply(rule expectation_mono)
      subgoal sorry
      subgoal sorry
      apply(rule fff) by auto 
    also have "\<dots> =   ?bnd * \<delta>"
      apply(subst expectation_const)
      apply(subst expectation_const) ..
  finally have bd_exp: "measure_pmf.expectation (Samples m D) (\<lambda>S. Sup (?err S ` H)) \<le> ?bnd * \<delta>"
    by simp

  note f = measure_pmf.prob_neg[where M="(Samples m D)", simplified]

  have *: "{S. Sup (?err S ` H) > ?bnd } = {S. \<not> Sup (?err S ` H) \<le> ?bnd }" by auto

  have "measure_pmf.prob (Samples m D) {S. Sup (?err S ` H) > ?bnd }       
         \<le> measure_pmf.expectation (Samples m D) (\<lambda>S. Sup (?err S ` H)) / ?bnd"
    by(rule markov_inequality)    
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