theory NewTry
imports LearningTheory
begin

definition "mapify f = (\<lambda>x. Some (f x))"
definition "allmaps C D = {m. dom m = C \<and> ran m \<subseteq> D}"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"



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
  sorry


lemma fixes f :: "'a \<Rightarrow> real" and C :: real
  shows brag1: "(\<forall>h\<in>S. f h \<le> C) \<Longrightarrow> Greatest (\<lambda>r. \<exists>x. f x = r) \<le> C"
  sorry
 
lemma fixes f :: "'c \<Rightarrow> real" and C :: real
  assumes "S \<noteq> {}"   
  shows brag2: "Greatest (\<lambda>r. \<exists>x\<in>S. f x = r) \<le> C \<Longrightarrow> h\<in>S \<Longrightarrow>  f h \<le> C"
  sorry
 
thm brag2[OF nnH]
 


thm Max_le_iff
   
    thm subsetlesspmf

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


print_classes

thm cSup_le_iff

lemma fixes f :: "'c \<Rightarrow> real" and C :: real
  assumes "S \<noteq> {}"   
      and "\<And>x. f x \<le> 2"
  shows brag3: "Sup (f ` S) \<le> C \<Longrightarrow> h\<in>S \<Longrightarrow>  f h \<le> C"
  sorry


lemma PredErr_as_expectation:
  "PredErr D h = measure_pmf.expectation (Samples m D) (\<lambda>S. TrainErr S {0..<m} h )"
  unfolding PredErr_def unfolding TrainErr_def sorry


lemma expectation_mono:
    "(\<And>x. f x \<le> g x) \<Longrightarrow> measure_pmf.expectation M f \<le> measure_pmf.expectation M g"
  sorry

lemma expectation_const: "measure_pmf.expectation M (\<lambda>_. c) = c"
    sorry

lemma expectation_cong: "(\<And>m. m\<in>set_pmf M \<Longrightarrow> f m = g m) \<Longrightarrow> measure_pmf.expectation M f = measure_pmf.expectation M g"
  sorry


lemma expectation_Sup_le: "(\<Squnion>h\<in>H. measure_pmf.expectation D (f h))
         \<le> measure_pmf.expectation D (\<lambda>S'. \<Squnion>h\<in>H. f h S')"
  sorry

lemma expectation_linear:
    "measure_pmf.expectation M (\<lambda>S. measure_pmf.expectation M2 (f S))
        = measure_pmf.expectation M2 (\<lambda>S2. measure_pmf.expectation M (\<lambda>S. f S S2))"
  sorry

term "Pi_pmf {0..<n} undefined (\<lambda>i. D i)"
term sum              
term measure_pmf.prob 
lemma hoeffding_ineq:
  assumes
      "\<And>i::nat. measure_pmf.expectation (D i) (f i) = \<mu>"
    and "\<And>i. measure_pmf.prob (D i) {x. a \<le> x \<and> x \<le> b} = 1" 
  shows "measure_pmf.prob (Pi_pmf {0..<m} dflt D) {\<sigma>. abs(sum  (\<lambda>i. f i (\<sigma> i) - \<mu>) {0..<m} / m) > \<epsilon> }
             \<le> 2 * exp (- 2 * m * \<epsilon>^2 / (b-a)^2 )"
  sorry


lemma Lemma_A4:
  assumes "a>0" "b\<ge>exp 1" "\<And>t. t\<ge>0 \<Longrightarrow> measure_pmf.prob R {x. abs(f x-x')>t}\<le> 2*b*exp(-(t^2)/a^2)"
  shows "measure_pmf.expectation R (\<lambda>x. abs(f x-x')) \<le> a * (2+ sqrt (ln b))"
  sorry

lemma expectation_pair_pmf:
    "measure_pmf.expectation (pair_pmf p q) f
      = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation q (\<lambda>y. f (x, y)))"
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



lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and delta_nn: "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(m/2))} \<ge> 1 - \<delta>"
      (is "measure_pmf.prob _ {S. \<forall>h\<in>H. ?err S h \<le> ?bnd } \<ge> _")
proof -
  have bnd_gt0: "?bnd > 0"   sorry
  have m_gt0: "m>0" sorry


  have finiteY: "finite Y" sorry (* hmm, not so sure here! *)

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
      apply auto sorry
    have "card ?C \<le> card {fst (S i)|i. i\<in>{0..<m}} + card {fst (S' i)|i. i\<in>{0..<m}}"
      by (rule card_Un_le)
    also have "\<dots> \<le> 2*m"
      using pp[of S] pp[of S'] by simp
    finally have cardC: "card ?C \<le> 2 * m" .

    
    have finite_restrC: "finite (restrictH H_map ?C Y)"
      apply(rule finiteres) apply simp using finiteY by simp
  
    have CX: "?C \<subseteq> X" sorry
    have *: "card (restrictH H_map ?C Y) \<le> growth (card ?C)"
      unfolding growth_def
      apply(rule Max_ge)
      subgoal apply auto sorry
      subgoal using CX by blast
      done
    have C_bd_growth: "card (restrictH H_map ?C Y) \<le> growth (2*m)"
      apply(rule order.trans)
      apply(rule *) apply(rule growth_mono)  apply(rule cardC) done
    have C_gt0: "card ?C > 0" apply simp sorry
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
      let ?bla = "\<lambda>\<sigma> h. (sum (\<lambda>i. \<sigma> i * ( (case (S' i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0)  
                         -  (case (S i) of (x,y) \<Rightarrow> if h x \<noteq> Some y then 1::real else 0))) {0..<m})    / m "
    { 
      term measure_pmf.prob
      fix h :: "'a \<Rightarrow> 'b option"   
      { fix \<rho> D and f :: "nat \<Rightarrow> real \<Rightarrow> real"
          have "(\<And>i::nat. measure_pmf.expectation (D i) (f i) = 0) \<Longrightarrow>
  (\<And>i. measure_pmf.prob (D i) {x. -1 \<le> x \<and> x \<le> 1} = 1) \<Longrightarrow>
  measure_pmf.prob (Pi_pmf {0..<m} 1 D) {\<sigma>. \<rho> < \<bar>(\<Sum>i = 0..<m. f i (\<sigma> i) ) / real m\<bar>}
  \<le> 2 * exp (-  real m * \<rho>\<^sup>2 / 2 )"
        using hoeffding_ineq[where \<epsilon>=\<rho> and m=m and a="-1" and b=1 and \<mu>=0 and f=f, simplified] by simp  
    } note bla = this
      have "\<And>\<rho>::real. measure_pmf.prob (Samples1 m (pmf_of_set {-1,1::real})) {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho> }
                    \<le> 2 * exp (-  real m  * \<rho>^2 / 2)"
        subgoal for \<rho> unfolding Samples1_def
          apply(rule bla) 
          subgoal by(simp add: integral_pmf_of_set)
          subgoal by(simp add: measure_pmf_of_set)
          done
        done
    } note gaga = this

    have argh: "\<And>\<rho>. {\<sigma>. MAXIMUM (restrictH H_map ?C Y) (\<lambda>h. \<bar>?bla \<sigma> h\<bar>) > \<rho> }
                  \<subseteq> (\<Union>h\<in>(restrictH H_map ?C Y).  {\<sigma>. \<bar>?bla \<sigma> h\<bar> > \<rho>} )"
      subgoal for \<rho>
        using braa[OF finite_restrC restrictH_nonempty, of \<rho> "\<lambda>\<sigma> h. \<bar>?bla \<sigma> h\<bar>"] by blast
      done

      thm measure_pmf.finite_measure_subadditive_finite

      {fix \<rho> :: real

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
           apply(rule sum_mono) by (rule gaga)
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
(\<And>t. 0 \<le> t \<Longrightarrow>
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
         apply(rule ppp[of t]) apply simp
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
    apply(rule cSUP_mono[OF nnH])
    subgoal sorry
    subgoal for x n apply(rule bexI[where x=n]) sorry (* not sure here! *)
    done  
  also have "\<dots> \<le> measure_pmf.expectation (Samples m D)
           (\<lambda>S. \<Squnion>h\<in>H. measure_pmf.expectation (Samples m D)
         (\<lambda>S'. \<bar>TrainErr S' {0..<m} h - TrainErr S {0..<m} h\<bar> ) )"
    apply(rule expectation_mono)
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
      apply(rule expectation_mono)
      apply(rule fff)
      done
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