\<^marker>\<open>creator Manuel Eberl\<close>

theory Pi_pmf
  imports "HOL-Probability.Probability"
begin

definition Pi_pmf :: "'a set \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b pmf) \<Rightarrow> ('a \<Rightarrow> 'b) pmf" where
  "Pi_pmf A dflt p =
     embed_pmf (\<lambda>f. if (\<forall>x. x \<notin> A \<longrightarrow> f x = dflt) then \<Prod>x\<in>A. pmf (p x) (f x) else 0)"

lemma pmf_Pi:
  assumes A: "finite A"
  shows   "pmf (Pi_pmf A dflt p) f = 
             (if (\<forall>x. x \<notin> A \<longrightarrow> f x = dflt) then \<Prod>x\<in>A. pmf (p x) (f x) else 0)"
  unfolding Pi_pmf_def
proof (rule pmf_embed_pmf, goal_cases)
  case 2
  define S where "S = {f. \<forall>x. x \<notin> A \<longrightarrow> f x = dflt}"
  define B where "B = (\<lambda>x. set_pmf (p x))"

  have neutral_left: "(\<Prod>xa\<in>A. pmf (p xa) (f xa)) = 0" 
    if "f \<in> PiE A B - (\<lambda>f. restrict f A) ` S" for f
  proof -
    have "restrict (\<lambda>x. if x \<in> A then f x else dflt) A \<in> (\<lambda>f. restrict f A) ` S"
      by (intro imageI) (auto simp: S_def)
    also have "restrict (\<lambda>x. if x \<in> A then f x else dflt) A = f"
      using that by (auto simp: PiE_def Pi_def extensional_def fun_eq_iff)
    finally show ?thesis using that by blast
  qed
  have neutral_right: "(\<Prod>xa\<in>A. pmf (p xa) (f xa)) = 0" 
    if "f \<in> (\<lambda>f. restrict f A) ` S - PiE A B" for f
  proof -
    from that obtain f' where f': "f = restrict f' A" "f' \<in> S" by auto
    moreover from this and that have "restrict f' A \<notin> PiE A B" by simp
    then obtain x where "x \<in> A" "pmf (p x) (f' x) = 0" by (auto simp: B_def set_pmf_eq)
    with f' and A show ?thesis by auto
  qed

  have "(\<lambda>f. \<Prod>x\<in>A. pmf (p x) (f x)) abs_summable_on PiE A B"
    by (intro abs_summable_on_prod_PiE A) (auto simp: B_def)
  also have "?this \<longleftrightarrow> (\<lambda>f. \<Prod>x\<in>A. pmf (p x) (f x)) abs_summable_on (\<lambda>f. restrict f A) ` S"
    by (intro abs_summable_on_cong_neutral neutral_left neutral_right) auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>f. \<Prod>x\<in>A. pmf (p x) (restrict f A x)) abs_summable_on S"
    by (rule abs_summable_on_reindex_iff [symmetric]) (force simp: inj_on_def fun_eq_iff S_def)
  also have "\<dots> \<longleftrightarrow> (\<lambda>f. if \<forall>x. x \<notin> A \<longrightarrow> f x = dflt then \<Prod>x\<in>A. pmf (p x) (f x) else 0) 
                          abs_summable_on UNIV"
    by (intro abs_summable_on_cong_neutral) (auto simp: S_def)
  finally have summable: \<dots> .

  have "1 = (\<Prod>x\<in>A. 1::real)" by simp
  also have "(\<Prod>x\<in>A. 1) = (\<Prod>x\<in>A. \<Sum>\<^sub>ay\<in>B x. pmf (p x) y)"
    unfolding B_def by (subst infsetsum_pmf_eq_1) auto
  also have "(\<Prod>x\<in>A. \<Sum>\<^sub>ay\<in>B x. pmf (p x) y) = (\<Sum>\<^sub>af\<in>Pi\<^sub>E A B. \<Prod>x\<in>A. pmf (p x) (f x))"
    by (intro infsetsum_prod_PiE [symmetric] A) (auto simp: B_def)
  also have "\<dots> = (\<Sum>\<^sub>af\<in>(\<lambda>f. restrict f A) ` S. \<Prod>x\<in>A. pmf (p x) (f x))" using A
    by (intro infsetsum_cong_neutral neutral_left neutral_right refl)
  also have "\<dots> = (\<Sum>\<^sub>af\<in>S. \<Prod>x\<in>A. pmf (p x) (restrict f A x))"
    by (rule infsetsum_reindex) (force simp: inj_on_def fun_eq_iff S_def)
  also have "\<dots> = (\<Sum>\<^sub>af\<in>S. \<Prod>x\<in>A. pmf (p x) (f x))"
    by (intro infsetsum_cong) (auto simp: S_def)
  also have "\<dots> = (\<Sum>\<^sub>af. if \<forall>x. x \<notin> A \<longrightarrow> f x = dflt then \<Prod>x\<in>A. pmf (p x) (f x) else 0)"
    by (intro infsetsum_cong_neutral) (auto simp: S_def)
  also have "ennreal \<dots> = (\<integral>\<^sup>+f. ennreal (if \<forall>x. x \<notin> A \<longrightarrow> f x = dflt
                             then \<Prod>x\<in>A. pmf (p x) (f x) else 0) \<partial>count_space UNIV)"
    by (intro nn_integral_conv_infsetsum [symmetric] summable) (auto simp: prod_nonneg)
  finally show ?case by simp
qed (auto simp: prod_nonneg)

lemma pmf_Pi':
  assumes "finite A" "\<And>x. x \<notin> A \<Longrightarrow> f x = dflt"
  shows   "pmf (Pi_pmf A dflt p) f = (\<Prod>x\<in>A. pmf (p x) (f x))"
  using assms by (subst pmf_Pi) auto

lemma pmf_Pi_outside:
  assumes "finite A" "\<exists>x. x \<notin> A \<and> f x \<noteq> dflt"
  shows   "pmf (Pi_pmf A dflt p) f = 0"
  using assms by (subst pmf_Pi) auto

lemma pmf_Pi_empty [simp]: "Pi_pmf {} dflt p = return_pmf (\<lambda>_. dflt)"
  by (intro pmf_eqI, subst pmf_Pi) (auto simp: indicator_def)

lemma set_Pi_pmf_subset: "finite A \<Longrightarrow> set_pmf (Pi_pmf A dflt p) \<subseteq> {f. \<forall>x. x \<notin> A \<longrightarrow> f x = dflt}"
  by (auto simp: set_pmf_eq pmf_Pi)

lemma pmf_prob_cong:
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> pmf p x = 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> pmf p x = 0"
  shows   "measure_pmf.prob p A = measure_pmf.prob p B"
proof -
  have "measure_pmf.prob p A = measure_pmf.prob p (A \<inter> set_pmf p)"
    by (simp add: measure_Int_set_pmf)
  also have "A \<inter> set_pmf p = B \<inter> set_pmf p"
    using assms by (auto simp: set_pmf_eq)
  also have "measure_pmf.prob p \<dots> = measure_pmf.prob p B"
    by (simp add: measure_Int_set_pmf)
  finally show ?thesis .
qed

lemma Pi_pmf_insert: 
  assumes "finite A" "x \<notin> A"
  shows   "Pi_pmf (insert x A) dflt p = map_pmf (\<lambda>(y,f). f(x:=y)) (pair_pmf (p x) (Pi_pmf A dflt p))"
proof (intro pmf_eqI)
  fix f
  let ?M = "pair_pmf (p x) (Pi_pmf A dflt p)"
  have "pmf (map_pmf (\<lambda>(y, f). f(x := y)) ?M) f = 
          measure_pmf.prob ?M ((\<lambda>(y, f). f(x := y)) -` {f})"
    by (subst pmf_map) auto
  also have "((\<lambda>(y, f). f(x := y)) -` {f}) = (\<Union>y'. {(f x, f(x := y'))})"
    by (auto simp: fun_upd_def fun_eq_iff)
  also have "measure_pmf.prob ?M \<dots> = measure_pmf.prob ?M {(f x, f(x := dflt))}"
    using assms by (intro pmf_prob_cong) (auto simp: pmf_pair pmf_Pi split: if_splits)
  also have "\<dots> = pmf (p x) (f x) * pmf (Pi_pmf A dflt p) (f(x := dflt))"
    by (simp add: measure_pmf_single pmf_pair pmf_Pi)
  also have "\<dots> = pmf (Pi_pmf (insert x A) dflt p) f"
  proof (cases "\<forall>y. y \<notin> insert x A \<longrightarrow> f y = dflt")
    case True
    with assms have "pmf (p x) (f x) * pmf (Pi_pmf A dflt p) (f(x := dflt)) = 
                       pmf (p x) (f x) * (\<Prod>xa\<in>A. pmf (p xa) ((f(x := dflt)) xa))"
      by (subst pmf_Pi') auto
    also have "(\<Prod>xa\<in>A. pmf (p xa) ((f(x := dflt)) xa)) = (\<Prod>xa\<in>A. pmf (p xa) (f xa))"
      using assms by (intro prod.cong) auto
    also have "pmf (p x) (f x) * \<dots> = pmf (Pi_pmf (insert x A) dflt p) f" 
      using assms True by (subst pmf_Pi') auto
    finally show ?thesis .
  qed (insert assms, auto simp: pmf_Pi)
  finally show "\<dots> = pmf (map_pmf (\<lambda>(y, f). f(x := y)) ?M) f" ..
qed

lemma Pi_pmf_singleton: 
  "Pi_pmf {x} dflt p = map_pmf (\<lambda>a b. if b = x then a else dflt) (p x)"
proof -
  have "Pi_pmf {x} dflt p = map_pmf (fun_upd (\<lambda>_. dflt) x) (p x)"
    by (subst Pi_pmf_insert) (simp_all add: pair_return_pmf2 pmf.map_comp o_def)
  also have "fun_upd (\<lambda>_. dflt) x = (\<lambda>z y. if y = x then z else dflt)"
    by (simp add: fun_upd_def fun_eq_iff)
  finally show ?thesis .
qed

lemma Pi_pmf_component:
  assumes "finite A"
  shows   "map_pmf (\<lambda>f. f x) (Pi_pmf A dflt p) = (if x \<in> A then p x else return_pmf dflt)"
proof (cases "x \<in> A")
  case True
  define A' where "A' = A - {x}"
  from assms and True have A': "A = insert x A'"
    by (auto simp: A'_def)
  from assms have "map_pmf (\<lambda>f. f x) (Pi_pmf A dflt p) = p x" unfolding A'
    by (subst Pi_pmf_insert) 
       (auto simp: A'_def pmf.map_comp o_def case_prod_unfold map_fst_pair_pmf)
  with True show ?thesis by simp
next
  case False
  have "map_pmf (\<lambda>f. f x) (Pi_pmf A dflt p) = map_pmf (\<lambda>_. dflt) (Pi_pmf A dflt p)"
    using assms False set_Pi_pmf_subset[of A dflt p]
    by (intro pmf.map_cong refl) (auto simp: set_pmf_eq pmf_Pi_outside)
  with False show ?thesis by simp
qed

definition PiE_dflt 
  where "PiE_dflt A dflt B = {f. \<forall>x. (x \<in> A \<longrightarrow> f x \<in> B x) \<and> (x \<notin> A \<longrightarrow> f x = dflt)}"

lemma restrict_PiE_dflt: "(\<lambda>h. restrict h A) ` PiE_dflt A dflt B = PiE A B"
proof (intro equalityI subsetI)
  fix h assume "h \<in> (\<lambda>h. restrict h A) ` PiE_dflt A dflt B"
  thus "h \<in> PiE A B"
    by (auto simp: PiE_dflt_def)
next
  fix h assume h: "h \<in> PiE A B"
  hence "restrict (\<lambda>x. if x \<in> A then h x else dflt) A \<in> (\<lambda>h. restrict h A) ` PiE_dflt A dflt B"
    by (intro imageI) (auto simp: PiE_def extensional_def PiE_dflt_def)
  also have "restrict (\<lambda>x. if x \<in> A then h x else dflt) A = h"
    using h by (auto simp: fun_eq_iff)
  finally show "h \<in> (\<lambda>h. restrict h A) ` PiE_dflt A dflt B" .
qed

lemma measure_Pi_pmf_PiE_dflt:
  assumes [simp]: "finite A"
  shows   "measure_pmf.prob (Pi_pmf A dflt p) (PiE_dflt A dflt B) =
             (\<Prod>x\<in>A. measure_pmf.prob (p x) (B x))"
proof -
  define B' where "B' = (\<lambda>x. B x \<inter> set_pmf (p x))"
  have "measure_pmf.prob (Pi_pmf A dflt p) (PiE_dflt A dflt B) = 
          (\<Sum>\<^sub>ah\<in>PiE_dflt A dflt B. pmf (Pi_pmf A dflt p) h)"
    by (rule measure_pmf_conv_infsetsum)
  also have "\<dots> = (\<Sum>\<^sub>ah\<in>PiE_dflt A dflt B. \<Prod>x\<in>A. pmf (p x) (h x))"
    by (intro infsetsum_cong, subst pmf_Pi') (auto simp: PiE_dflt_def)
  also have "\<dots> = (\<Sum>\<^sub>ah\<in>(\<lambda>h. restrict h A) ` PiE_dflt A dflt B. \<Prod>x\<in>A. pmf (p x) (h x))"
    by (subst infsetsum_reindex) (force simp: inj_on_def PiE_dflt_def fun_eq_iff)+
  also have "(\<lambda>h. restrict h A) ` PiE_dflt A dflt B = PiE A B"
    by (rule restrict_PiE_dflt)
  also have "(\<Sum>\<^sub>ah\<in>PiE A B. \<Prod>x\<in>A. pmf (p x) (h x)) = (\<Sum>\<^sub>ah\<in>PiE A B'. \<Prod>x\<in>A. pmf (p x) (h x))"
    by (intro infsetsum_cong_neutral) (auto simp: B'_def set_pmf_eq)
  also have "(\<Sum>\<^sub>ah\<in>PiE A B'. \<Prod>x\<in>A. pmf (p x) (h x)) = (\<Prod>x\<in>A. infsetsum (pmf (p x)) (B' x))"
    by (intro infsetsum_prod_PiE) (auto simp: B'_def)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (pmf (p x)) (B x))"
    by (intro prod.cong infsetsum_cong_neutral) (auto simp: B'_def set_pmf_eq)
  also have "\<dots> = (\<Prod>x\<in>A. measure_pmf.prob (p x) (B x))"
    by (subst measure_pmf_conv_infsetsum) (rule refl)
  finally show ?thesis .
qed

lemma Pi_pmf_map:
  assumes [simp]: "finite A" and "f dflt = dflt'"
  shows   "Pi_pmf A dflt' (\<lambda>x. map_pmf f (g x)) = map_pmf (\<lambda>h. f \<circ> h) (Pi_pmf A dflt g)"
    (is "?lhs = ?rhs")
proof (rule pmf_eqI)
  fix h
  show "pmf ?lhs h = pmf ?rhs h"
  proof (cases "\<forall>x. x \<notin> A \<longrightarrow> h x = dflt'")
    case True
    hence "pmf ?lhs h = (\<Prod>x\<in>A. measure_pmf.prob (g x) (f -` {h x}))"
      by (subst pmf_Pi) (auto simp: pmf_map)
    also have "\<dots> = measure_pmf.prob (Pi_pmf A dflt g) (PiE_dflt A dflt (\<lambda>x. f -` {h x}))"
      by (rule measure_Pi_pmf_PiE_dflt [symmetric]) auto
    also have "PiE_dflt A dflt (\<lambda>x. f -` {h x}) = ((\<circ>) f -` {h}) \<inter> PiE_dflt A dflt (\<lambda>_. UNIV)"
      using True by (fastforce simp: assms(2) [symmetric] fun_eq_iff PiE_dflt_def o_def)
    also have "measure_pmf.prob (Pi_pmf A dflt g) \<dots> = 
                 measure_pmf.prob (Pi_pmf A dflt g) ((\<circ>) f -` {h})"
      by (intro pmf_prob_cong) (auto simp: PiE_dflt_def pmf_Pi_outside)
    also have "\<dots> = pmf ?rhs h" by (simp add: pmf_map)
    finally show ?thesis .
  next
    case False
    have "pmf ?rhs h = infsetsum (pmf (Pi_pmf A dflt g)) ((\<circ>) f -` {h})"
      by (simp add: pmf_map measure_pmf_conv_infsetsum)
    also from False have "\<dots> = infsetsum (\<lambda>_. 0) ((\<circ>) f -` {h})"
      by (intro infsetsum_cong pmf_Pi_outside) (auto simp: fun_eq_iff o_def assms(2) [symmetric])
    also have "\<dots> = 0" by simp
    also from False have "\<dots> = pmf ?lhs h"
      by (subst pmf_Pi_outside) auto
    finally show ?thesis ..
  qed
qed

lemma pmf_expectation_eq_infsetsum: "measure_pmf.expectation p f = infsetsum (\<lambda>x. pmf p x * f x) UNIV" 
  unfolding infsetsum_def measure_pmf_eq_density by (subst integral_density) simp_all

lemma Pi_pmf_bind:
  assumes "finite A"
  shows   "Pi_pmf A d (\<lambda>x. bind_pmf (p x) (q x)) =
             do {f \<leftarrow> Pi_pmf A d' p; Pi_pmf A d (\<lambda>x. q x (f x))}" (is "?lhs = ?rhs")
proof (rule pmf_eqI, goal_cases)
  case (1 f)
  show ?case
  proof (cases "\<exists>x\<in>-A. f x \<noteq> d")
    case False
    define B where "B = (\<lambda>x. set_pmf (p x))"
    have [simp]: "countable (B x)" for x by (auto simp: B_def)

    {
      fix x :: 'a
      have "(\<lambda>a. pmf (p x) a * 1) abs_summable_on B x" 
        by (simp add: pmf_abs_summable)
      moreover have "norm (pmf (p x) a * 1) \<ge> norm (pmf (p x) a * pmf (q x a) (f x))" for a
        unfolding norm_mult by (intro mult_left_mono) (auto simp: pmf_le_1)
      ultimately have "(\<lambda>a. pmf (p x) a * pmf (q x a) (f x)) abs_summable_on B x"
        by (rule abs_summable_on_comparison_test)
    } note summable = this

    have "pmf ?rhs f = (\<Sum>\<^sub>ag. pmf (Pi_pmf A d' p) g * (\<Prod>x\<in>A. pmf (q x (g x)) (f x)))"
      by (subst pmf_bind, subst pmf_Pi') 
         (insert assms False, simp_all add: pmf_expectation_eq_infsetsum)
    also have "\<dots> = (\<Sum>\<^sub>ag\<in>PiE_dflt A d' B. 
                      pmf (Pi_pmf A d' p) g * (\<Prod>x\<in>A. pmf (q x (g x)) (f x)))" unfolding B_def
      using assms by (intro infsetsum_cong_neutral) (auto simp: pmf_Pi PiE_dflt_def set_pmf_eq)
    also have "\<dots> = (\<Sum>\<^sub>ag\<in>PiE_dflt A d' B. 
                      (\<Prod>x\<in>A. pmf (p x) (g x) * pmf (q x (g x)) (f x)))"
      using assms by (intro infsetsum_cong) (auto simp: pmf_Pi PiE_dflt_def prod.distrib)
    also have "\<dots> = (\<Sum>\<^sub>ag\<in>(\<lambda>g. restrict g A) ` PiE_dflt A d' B. 
                      (\<Prod>x\<in>A. pmf (p x) (g x) * pmf (q x (g x)) (f x)))"
      by (subst infsetsum_reindex) (force simp: PiE_dflt_def inj_on_def fun_eq_iff)+
    also have "(\<lambda>g. restrict g A) ` PiE_dflt A d' B = PiE A B"
      by (rule restrict_PiE_dflt)
    also have "(\<Sum>\<^sub>ag\<in>\<dots>. (\<Prod>x\<in>A. pmf (p x) (g x) * pmf (q x (g x)) (f x))) = 
                 (\<Prod>x\<in>A. \<Sum>\<^sub>aa\<in>B x. pmf (p x) a * pmf (q x a) (f x))"
      using assms summable by (subst infsetsum_prod_PiE) simp_all
    also have "\<dots> = (\<Prod>x\<in>A. \<Sum>\<^sub>aa. pmf (p x) a * pmf (q x a) (f x))"
      by (intro prod.cong infsetsum_cong_neutral) (auto simp: B_def set_pmf_eq)
    also have "\<dots> = pmf ?lhs f"
      using False assms by (subst pmf_Pi') (simp_all add: pmf_bind pmf_expectation_eq_infsetsum)
    finally show ?thesis ..
  next
    case True
    have "pmf ?rhs f = 
            measure_pmf.expectation (Pi_pmf A d' p) (\<lambda>x. pmf (Pi_pmf A d (\<lambda>xa. q xa (x xa))) f)"
      using assms by (simp add: pmf_bind)
    also have "\<dots> = measure_pmf.expectation (Pi_pmf A d' p) (\<lambda>x. 0)"
      using assms True by (intro Bochner_Integration.integral_cong pmf_Pi_outside) auto
    also have "\<dots> = pmf ?lhs f"
      using assms True by (subst pmf_Pi_outside) auto
    finally show ?thesis ..
  qed
qed

(* Weeeellll, guess who wrote all that? That's right. Manuel *)

lemma dflt_image_PiE: "(\<lambda>h x. if x \<in> A then h x else dflt) ` PiE A B = PiE_dflt A dflt B"
  (is "?f ` ?X = ?Y")
proof (intro equalityI subsetI)
  fix h assume "h \<in> ?f ` ?X"
  thus "h \<in> ?Y"
    by (auto simp: PiE_dflt_def PiE_def)
next
  fix h assume h: "h \<in> ?Y"
  hence "?f (restrict h A) \<in> ?f ` ?X"
    by (intro imageI) (auto simp: PiE_def extensional_def PiE_dflt_def)
  also have "?f (restrict h A) = h"
    using h by (auto simp: fun_eq_iff PiE_dflt_def)
  finally show "h \<in> ?f ` ?X" .
qed

lemma finite_PiE_dflt [intro]: 
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)"
  shows   "finite (PiE_dflt A d B)"
proof -
  have "PiE_dflt A d B = (\<lambda>f x. if x \<in> A then f x else d) ` PiE A B"
    by (rule dflt_image_PiE [symmetric])
  also have "finite \<dots>"
    by (intro finite_imageI finite_PiE assms)
  finally show ?thesis .
qed

lemma card_PiE_dflt: 
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)"
  shows   "card (PiE_dflt A d B) = (\<Prod>x\<in>A. card (B x))"
proof -
  from assms have "(\<Prod>x\<in>A. card (B x)) = card (PiE A B)"
    by (intro card_PiE [symmetric]) auto
  also have "PiE A B = (\<lambda>f. restrict f A) ` PiE_dflt A d B"
    by (rule restrict_PiE_dflt [symmetric])
  also have "card \<dots> = card (PiE_dflt A d B)"
    by (intro card_image) (force simp: inj_on_def restrict_def fun_eq_iff PiE_dflt_def)
  finally show ?thesis ..
qed

lemma PiE_dflt_empty_iff [simp]: "PiE_dflt A dflt B = {} \<longleftrightarrow> (\<exists>x\<in>A. B x = {})"
  by (simp add: dflt_image_PiE [symmetric] PiE_eq_empty_iff)

lemma Pi_pmf_default_swap:
  assumes "finite A"
  shows   "map_pmf (\<lambda>f x. if x \<in> A then f x else dflt') (Pi_pmf A dflt p) =
             Pi_pmf A dflt' p" (is "?lhs = ?rhs")
proof (rule pmf_eqI, goal_cases)
  case (1 f)
  let ?B = "(\<lambda>f x. if x \<in> A then f x else dflt') -` {f} \<inter> PiE_dflt A dflt (\<lambda>_. UNIV)"
  show ?case
  proof (cases "\<exists>x\<in>-A. f x \<noteq> dflt'")
    case False
    let ?f' = "\<lambda>x. if x \<in> A then f x else dflt"
    from False have "pmf ?lhs f = measure_pmf.prob (Pi_pmf A dflt p) ?B"
      using assms unfolding pmf_map 
      by (intro pmf_prob_cong) (auto simp: PiE_dflt_def pmf_Pi_outside)
    also from False have "?B = {?f'}"
      by (auto simp: fun_eq_iff PiE_dflt_def)
    also have "measure_pmf.prob (Pi_pmf A dflt p) {?f'} = pmf (Pi_pmf A dflt p) ?f'"
      by (simp add: measure_pmf_single)
    also have "\<dots> = pmf ?rhs f"
      using False assms by (subst (1 2) pmf_Pi) auto
    finally show ?thesis .
  next
    case True
    have "pmf ?lhs f = measure_pmf.prob (Pi_pmf A dflt p) ?B"
      using assms unfolding pmf_map 
      by (intro pmf_prob_cong) (auto simp: PiE_dflt_def pmf_Pi_outside)
    also from True have "?B = {}" by auto
    also have "measure_pmf.prob (Pi_pmf A dflt p) \<dots> = 0" 
      by simp
    also have "0 = pmf ?rhs f"
      using True assms by (intro pmf_Pi_outside [symmetric]) auto
    finally show ?thesis .
  qed
qed

lemma Pi_pmf_union:
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows   "Pi_pmf (A \<union> B) dflt p =
             map_pmf (\<lambda>(f,g) x. if x \<in> A then f x else g x) 
             (pair_pmf (Pi_pmf A dflt p) (Pi_pmf B dflt p))" (is "_ = map_pmf (?h A) (?q A)")
  using assms(1,3)
proof (induction rule: finite_induct)
  case (insert x A)
  have "map_pmf (?h (insert x A)) (?q (insert x A)) = 
          do {v \<leftarrow> p x; (f, g) \<leftarrow> pair_pmf (Pi_pmf A dflt p) (Pi_pmf B dflt p);
              return_pmf (\<lambda>y. if y \<in> insert x A then (f(x := v)) y else g y)}"
    by (subst Pi_pmf_insert)
       (insert insert.hyps insert.prems, 
        simp_all add: pair_pmf_def map_bind_pmf bind_map_pmf bind_assoc_pmf bind_return_pmf)
  also have "\<dots> = do {v \<leftarrow> p x; (f, g) \<leftarrow> ?q A; return_pmf ((?h A (f,g))(x := v))}"
    by (intro bind_pmf_cong refl) (auto simp: fun_eq_iff)
  also have "\<dots> = do {v \<leftarrow> p x; f \<leftarrow> map_pmf (?h A) (?q A); return_pmf (f(x := v))}"
    by (simp add: bind_map_pmf map_bind_pmf case_prod_unfold cong: if_cong)
  also have "\<dots> = do {v \<leftarrow> p x; f \<leftarrow> Pi_pmf (A \<union> B) dflt p; return_pmf (f(x := v))}"
    using insert.hyps and insert.prems by (intro bind_pmf_cong insert.IH [symmetric] refl) auto
  also have "\<dots> = Pi_pmf (insert x (A \<union> B)) dflt p"
    by (subst Pi_pmf_insert) 
       (insert assms insert.hyps insert.prems, auto simp: pair_pmf_def map_bind_pmf)
  also have "insert x (A \<union> B) = insert x A \<union> B"
    by simp
  finally show ?case ..
qed (simp_all add: case_prod_unfold map_snd_pair_pmf)

lemma Pi_pmf_subset:
  assumes "finite A" "A' \<subseteq> A"
  shows   "Pi_pmf A' dflt p = map_pmf (\<lambda>f x. if x \<in> A' then f x else dflt) (Pi_pmf A dflt p)"
proof -
  let ?P = "pair_pmf (Pi_pmf A' dflt p) (Pi_pmf (A - A') dflt p)"
  from assms have [simp]: "finite A'"
    by (blast dest: finite_subset)
  from assms have "A = A' \<union> (A - A')"
    by blast
  also have "Pi_pmf \<dots> dflt p = map_pmf (\<lambda>(f,g) x. if x \<in> A' then f x else g x) ?P"
    using assms by (intro Pi_pmf_union) auto
  also have "map_pmf (\<lambda>f x. if x \<in> A' then f x else dflt) \<dots> = map_pmf fst ?P"
    unfolding map_pmf_comp o_def case_prod_unfold
    using set_Pi_pmf_subset[of A' dflt p] by (intro map_pmf_cong refl) (auto simp: fun_eq_iff)
  also have "\<dots> = Pi_pmf A' dflt p"
    by (simp add: map_fst_pair_pmf)
  finally show ?thesis ..
qed

lemma Pi_pmf_remove:
  assumes "finite A"
  shows   "Pi_pmf (A - {x}) dflt p = map_pmf (\<lambda>f. f(x := dflt)) (Pi_pmf A dflt p)"
proof -
  have "Pi_pmf (A - {x}) dflt p =
          map_pmf (\<lambda>f xa. if xa \<in> A - {x} then f xa else dflt) (Pi_pmf A dflt p)"
    using assms by (intro Pi_pmf_subset) auto
  also have "\<dots> = map_pmf (\<lambda>f. f(x := dflt)) (Pi_pmf A dflt p)"
    using set_Pi_pmf_subset[of A dflt p] assms
    by (intro map_pmf_cong refl) (auto simp: fun_eq_iff)
  finally show ?thesis .
qed

lemma binomial_pmf_altdef':
  fixes A :: "'a set"
  assumes "finite A" and "card A = n" and p: "p \<in> {0..1}"
  shows   "binomial_pmf n p = 
             map_pmf (\<lambda>f. card {x\<in>A. f x}) (Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p))" (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = binomial_pmf (card A) p"
    by simp
  also have "\<dots> = ?rhs"
  using assms(1)
  proof (induction rule: finite_induct)
    case empty
    with p show ?case by (simp add: binomial_pmf_0)
  next
    case (insert x A)
    from insert.hyps have "card (insert x A) = Suc (card A)"
      by simp
    also have "binomial_pmf \<dots> p = do {
                                     b \<leftarrow> bernoulli_pmf p;
                                     f \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
                                     return_pmf ((if b then 1 else 0) + card {y \<in> A. f y})
                                   }"
      using p by (simp add: binomial_pmf_Suc insert.IH bind_map_pmf)
    also have "\<dots> = do {
                      b \<leftarrow> bernoulli_pmf p;
                      f \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
                      return_pmf (card {y \<in> insert x A. (f(x := b)) y})
                    }"
    proof (intro bind_pmf_cong refl, goal_cases)
      case (1 b f)
      have "(if b then 1 else 0) + card {y\<in>A. f y} = card ((if b then {x} else {}) \<union> {y\<in>A. f y})"
        using insert.hyps by auto
      also have "(if b then {x} else {}) \<union> {y\<in>A. f y} = {y\<in>insert x A. (f(x := b)) y}"
        using insert.hyps by auto
      finally show ?case by simp
    qed
    also have "\<dots> = map_pmf (\<lambda>f. card {y\<in>insert x A. f y}) 
                      (Pi_pmf (insert x A) dflt (\<lambda>_. bernoulli_pmf p))"
      using insert.hyps by (subst Pi_pmf_insert) (simp_all add: pair_pmf_def map_bind_pmf)
    finally show ?case .
  qed
  finally show ?thesis .
qed

lemma Pi_pmf_of_set:
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)" "\<And>x. x \<in> A \<Longrightarrow> B x \<noteq> {}" 
  shows   "Pi_pmf A d (\<lambda>x. pmf_of_set (B x)) = pmf_of_set (PiE_dflt A d B)" (is "?lhs = ?rhs")
proof (rule pmf_eqI, goal_cases)
  case (1 f)
  show ?case
  proof (cases "\<exists>x. x \<notin> A \<and> f x \<noteq> d")
    case True
    hence "pmf ?lhs f = 0"
      using assms by (intro pmf_Pi_outside) (auto simp: PiE_dflt_def)
    also from True have "f \<notin> PiE_dflt A d B"
      by (auto simp: PiE_dflt_def)
    hence "0 = pmf ?rhs f" 
      using assms by (subst pmf_of_set) auto
    finally show ?thesis .
  next
    case False
    hence "pmf ?lhs f = (\<Prod>x\<in>A. pmf (pmf_of_set (B x)) (f x))"
      using assms by (subst pmf_Pi') auto
    also have "\<dots> = (\<Prod>x\<in>A. indicator (B x) (f x) / real (card (B x)))"
      by (intro prod.cong refl, subst pmf_of_set) (use assms False in auto)
    also have "\<dots> = (\<Prod>x\<in>A. indicator (B x) (f x)) / real (\<Prod>x\<in>A. card (B x))"
      by (subst prod_dividef) simp_all
    also have "(\<Prod>x\<in>A. indicator (B x) (f x) :: real) = indicator (PiE_dflt A d B) f"
      using assms False by (auto simp: indicator_def PiE_dflt_def)
    also have "(\<Prod>x\<in>A. card (B x)) = card (PiE_dflt A d B)"
      using assms by (intro card_PiE_dflt [symmetric]) auto
    also have "indicator (PiE_dflt A d B) f / \<dots> = pmf ?rhs f"
      using assms by (intro pmf_of_set [symmetric]) auto
    finally show ?thesis .
  qed
qed

lemma Pi_pmf_bij_betw:
  assumes "finite A" "bij_betw h A B" "\<And>x. x \<notin> A \<Longrightarrow> h x \<notin> B"
  shows "Pi_pmf A dflt (\<lambda>_. f) = map_pmf (\<lambda>g. g \<circ> h) (Pi_pmf B dflt (\<lambda>_. f))"
    (is "?lhs = ?rhs")
proof -
  have B: "finite B"
    using assms bij_betw_finite by auto
  have "pmf ?lhs g = pmf ?rhs g" for g 
  proof (cases "\<forall>a. a \<notin> A \<longrightarrow> g a = dflt")
    case True
    define h' where "h' = the_inv_into A h"
    have h': "h' (h x) = x" if "x \<in> A" for x
      unfolding h'_def using that assms by (auto simp add: bij_betw_def the_inv_into_f_f)
    have h: "h (h' x) = x" if "x \<in> B" for x
      unfolding h'_def using that assms f_the_inv_into_f_bij_betw by fastforce
    have "pmf ?rhs g = measure_pmf.prob (Pi_pmf B dflt (\<lambda>_. f)) ((\<lambda>g. g \<circ> h) -` {g})"
      unfolding pmf_map by simp
    also have "\<dots> = measure_pmf.prob (Pi_pmf B dflt (\<lambda>_. f))
                                (((\<lambda>g. g \<circ> h) -` {g}) \<inter> PiE_dflt B dflt (\<lambda>_. UNIV))"
      using B by (intro pmf_prob_cong) (auto simp: PiE_dflt_def pmf_Pi_outside)
    also have "\<dots> = pmf (Pi_pmf B dflt (\<lambda>_. f)) (\<lambda>x. if x \<in> B then g (h' x) else dflt)"
    proof -
      have "(if h x \<in> B then g (h' (h x)) else dflt) = g x" for x
        using h' assms True by (cases "x \<in> A") (auto simp add: bij_betwE)
      then have "(\<lambda>g. g \<circ> h) -` {g} \<inter> PiE_dflt B dflt (\<lambda>_. UNIV) =
            {(\<lambda>x. if x \<in> B then g (h' x) else dflt)}"
        using assms h' h True unfolding PiE_dflt_def by auto
      then show ?thesis
        by (simp add: measure_pmf_single)
    qed
    also have "\<dots> = pmf (Pi_pmf A dflt (\<lambda>_. f)) g"
      using B assms True  h'_def
      by (auto simp add: pmf_Pi intro!: prod.reindex_bij_betw bij_betw_the_inv_into)
    finally show ?thesis
      by simp
  next
    case False
    have "pmf ?rhs g = infsetsum (pmf (Pi_pmf B dflt (\<lambda>_. f))) ((\<lambda>g. g \<circ> h) -` {g})"
      using assms by (auto simp add: measure_pmf_conv_infsetsum pmf_map)
    also have "\<dots> = infsetsum (\<lambda>_. 0) ((\<lambda>g x. g (h x)) -` {g})"
      using B False assms apply (intro infsetsum_cong pmf_Pi_outside) by fastforce+
    also have "\<dots> = 0"
      by simp
    finally show ?thesis
      using assms False by (auto simp add: pmf_Pi pmf_map)
  qed
  then show ?thesis
    by (rule pmf_eqI)
qed

lemma Pi_pmf_if_set:
  fixes f::"'a \<Rightarrow> nat pmf"
  assumes "finite A"
  shows "Pi_pmf A 0 (\<lambda>x. if b x then f x else return_pmf 0) =
         Pi_pmf {x \<in> A. b x} 0 f"
proof (cases "A = {}")
  assume "A = {}"
  then show ?thesis by (simp)
next
  assume not_empty: "A \<noteq> {}"
  have "(if \<forall>x. x \<notin> A \<longrightarrow> i x = 0 then \<Prod>x\<in>A. pmf (if b x then f x else return_pmf 0) (i x) else 0) =
        (if \<forall>x. x \<notin> {x \<in> A. b x} \<longrightarrow> i x = 0 then \<Prod>x\<in>{x \<in> A. b x}. pmf (f x) (i x) else 0)" for i
  proof -
    have *: "(\<Prod>x\<in>A. pmf (if b x then f x else return_pmf 0) (i x)) =
             (\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then f x else return_pmf 0) (i x)) *
             (\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then f x else return_pmf 0) (i x))"
    proof -
      have "(\<Prod>x\<in>A. pmf (if b x then f x else return_pmf 0) (i x)) =
        (\<Prod>x\<in>({x \<in> A. b x} \<union> {x \<in> A. \<not> b x}). pmf (if b x then f x else return_pmf 0) (i x))"
      proof -
        have "({x \<in> A. b x} \<union> {x \<in> A. \<not> b x}) = A"
          by blast
        then show ?thesis
          by simp
      qed
      also have "\<dots> = (\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then f x else return_pmf 0) (i x)) *
                      (\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then f x else return_pmf 0) (i x))"
        using assms by (intro prod.union_disjoint) (auto)
      finally show ?thesis
        by simp
    qed
    {
      assume a: "\<not> (\<forall>x. x \<notin> {x \<in> A. b x} \<longrightarrow> i x = 0)" "(\<forall>x. x \<notin> A \<longrightarrow> i x = 0)"
      have "(\<Prod>x\<in>A. pmf (if b x then f x else return_pmf 0) (i x)) = 0"
      proof (cases "{x \<in> A. \<not> b x} = {}")
        case True
        then have "{x \<in> A. b x} = A"
          by blast
        with a have False
          by blast
        then show ?thesis ..
      next
        case False
        then have "\<exists>x \<in> A. \<not> b x \<and> i x > 0"
          using a by auto
        (* There exists an element x in {x \<in> A. b x} with i x > 0 and therefore
           pmf (return_pmf 0) (i x) = 0 *)
        then have "(\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then f x else return_pmf 0) (i x)) = 0"
          using assms by (subst prod_zero_iff) (auto simp add: indicator_def)
        then show ?thesis
          by (simp add: *)
      qed
    }
    moreover {
      assume a: " \<forall>x. x \<notin> {x \<in> A. b x} \<longrightarrow> i x = 0"
      have "(\<Prod>x\<in>A. pmf (if b x then f x else return_pmf 0) (i x)) =
            (\<Prod>x\<in>{x \<in> A. b x}. pmf (f x) (i x))"
      proof -
        have "(\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then f x else return_pmf 0) (i x)) = 1"
        proof -
          have "\<not> b x \<Longrightarrow> pmf (if b x then f x else return_pmf 0) (i x) = 1" for x
            using a by (auto simp add: indicator_def)
          have "(\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then f x else return_pmf 0) (i x)) = (\<Prod>x\<in>{x \<in> A. \<not> b x}. 1)"
            using a by (intro prod.cong) (auto simp add: indicator_def)
          also have "\<dots> = 1"
            by fastforce
          finally show ?thesis
            by simp
        qed
        then show ?thesis
          by (simp add: *)
      qed
    }
    ultimately show ?thesis
      by (auto)
  qed
  then show ?thesis
    using assms by (auto intro!: pmf_eqI simp add: pmf_Pi)
qed

lemma Pi_pmf_if_set':
  fixes f::"'a \<Rightarrow> nat pmf"
  assumes "finite A"
  shows "Pi_pmf A 0 (\<lambda>x. if b x then return_pmf 0 else f x) =
         Pi_pmf {x \<in> A. \<not> b x} 0 f"
proof (cases "A = {}")
  assume "A = {}"
  then show ?thesis by (simp)
next
  assume not_empty: "A \<noteq> {}"
  have "(if \<forall>x. x \<notin> A \<longrightarrow> i x = 0 then \<Prod>x\<in>A. pmf (if b x then return_pmf 0 else f x) (i x) else 0) =
        (if \<forall>x. x \<notin> {x \<in> A. \<not> b x} \<longrightarrow> i x = 0 then \<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (f x) (i x) else 0)" for i
  proof -
    have *: "(\<Prod>x\<in>A. pmf (if b x then return_pmf 0 else f x) (i x)) =
             (\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then return_pmf 0 else f x) (i x)) *
             (\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then return_pmf 0 else f x) (i x))"
    proof -
      have "(\<Prod>x\<in>A. pmf (if b x then return_pmf 0 else f x) (i x)) =
        (\<Prod>x\<in>({x \<in> A. b x} \<union> {x \<in> A. \<not> b x}). pmf (if b x then return_pmf 0 else f x) (i x))"
      proof -
        have "({x \<in> A. b x} \<union> {x \<in> A. \<not> b x}) = A"
          by blast
        then show ?thesis
          by simp
      qed
      also have "\<dots> = (\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then return_pmf 0 else f x) (i x)) *
                      (\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (if b x then return_pmf 0 else f x) (i x))"
        using assms by (intro prod.union_disjoint) (auto)
      finally show ?thesis
        by simp
    qed
    {
      assume a: "\<not> (\<forall>x. x \<notin> {x \<in> A. \<not> b x} \<longrightarrow> i x = 0)" "(\<forall>x. x \<notin> A \<longrightarrow> i x = 0)"
      have "(\<Prod>x\<in>A. pmf (if b x then return_pmf 0 else f x) (i x)) = 0"
      proof (cases "{x \<in> A. b x} = {}")
        case True
        then have "{x \<in> A. \<not> b x} = A"
          by blast
        with a have False
          by blast
        then show ?thesis ..
      next
        case False
        then have "\<exists>x \<in> A. b x \<and> i x > 0"
          using a by auto
        (* There exists an element x in {x \<in> A. b x} with i x > 0 and therefore
           pmf (return_pmf 0) (i x) = 0 *)
        then have "(\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then return_pmf 0 else f x) (i x)) = 0"
          using assms by (subst prod_zero_iff) (auto simp add: indicator_def)
        then show ?thesis
          by (simp add: *)
      qed
    }
    moreover {
      assume a: " \<forall>x. x \<notin> {x \<in> A. \<not> b x} \<longrightarrow> i x = 0"
      have "(\<Prod>x\<in>A. pmf (if b x then return_pmf 0 else f x) (i x)) =
            (\<Prod>x\<in>{x \<in> A. \<not> b x}. pmf (f x) (i x))"
      proof -
        have "(\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then return_pmf 0 else f x) (i x)) = 1"
        proof -
          have "b x \<Longrightarrow> pmf (if b x then return_pmf 0 else f x) (i x) = 1" for x
            using a by (auto simp add: indicator_def)
          have "(\<Prod>x\<in>{x \<in> A. b x}. pmf (if b x then return_pmf 0 else f x) (i x)) = (\<Prod>x\<in>{x \<in> A. b x}. 1)"
            using a by (intro prod.cong) (auto simp add: indicator_def)
          also have "\<dots> = 1"
            by fastforce
          finally show ?thesis
            by simp
        qed
        then show ?thesis
          by (simp add: *)
      qed
    }
    ultimately show ?thesis
      by (auto)
  qed
  then show ?thesis
    using assms by (auto intro!: pmf_eqI simp add: pmf_Pi)
qed

lemma Pi_pmf_pmf_of_set: 
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)" "\<And>x. x \<in> A \<Longrightarrow> B x \<noteq> {}"
  shows   "Pi_pmf A d (\<lambda>x. pmf_of_set (B x)) = pmf_of_set (PiE_dflt A d B)"
proof -
  have "pmf (Pi_pmf A d (\<lambda>x. pmf_of_set (B x))) i = pmf (pmf_of_set (PiE_dflt A d B)) i" for i
  proof (cases " \<forall>x. x \<notin> A \<longrightarrow> i x = d")
    case True
    then have "pmf (Pi_pmf A d (\<lambda>x. pmf_of_set (B x))) i = (\<Prod>x\<in>A. pmf (pmf_of_set (B x)) (i x))"
      using assms by (auto simp add: pmf_Pi)
    also have "\<dots> = (\<Prod>x\<in>A. indicator (B x) (i x) / real (card (B x)))"
      using assms by (auto)
    also have "\<dots> = pmf (pmf_of_set (PiE_dflt A d B)) i"
    proof -
      have "((\<Prod>x\<in>A. indicator (B x) (i x))::real) = indicator (PiE_dflt A d B) i"
        using True assms by (auto simp add: indicator_def PiE_dflt_def)
      then show ?thesis
        using assms by (subst pmf_of_set) (auto simp add: card_PiE_dflt prod_dividef)
    qed
    finally show ?thesis
      by simp
  next
    case False
    then have "pmf (Pi_pmf A d (\<lambda>x. pmf_of_set (B x))) i = 0"
      using assms by (subst pmf_Pi) (auto)
    also have "0 = pmf (pmf_of_set (PiE_dflt A d B)) i"
    proof -
      have "indicator (PiE_dflt A d B) i = (0::real)"
        using False by (auto simp add: PiE_dflt_def indicator_def)
      then show ?thesis
        using assms by (subst pmf_of_set) (auto) 
    qed
    finally show ?thesis
      by simp
  qed
  then show ?thesis
    by (intro pmf_eqI) auto
qed

lemma
  assumes "finite A"
  shows "map_pmf (\<lambda>b. {x \<in> A. b x}) (Pi_pmf A P (\<lambda>_. bernoulli_pmf (1/2))) = pmf_of_set (Pow A)"
proof -
  have *: "Pi_pmf A P (\<lambda>_. pmf_of_set (UNIV :: bool set)) = pmf_of_set (PiE_dflt A P (\<lambda>_. UNIV :: bool set))"
    using assms by (intro Pi_pmf_pmf_of_set) auto
  have "map_pmf (\<lambda>b. {x \<in> A. b x}) (Pi_pmf A P (\<lambda>_. bernoulli_pmf (1 / 2))) = 
        map_pmf (\<lambda>b. {x \<in> A. b x}) (Pi_pmf A P (\<lambda>_. pmf_of_set UNIV))"
    using bernoulli_pmf_half_conv_pmf_of_set by auto
  also have "\<dots> = map_pmf (\<lambda>b. {x \<in> A. b x}) (pmf_of_set (PiE_dflt A P (\<lambda>_. UNIV)))"
    using assms by (subst Pi_pmf_pmf_of_set) (auto)
  also have "\<dots> = pmf_of_set (Pow A)"
  proof -
    have "bij_betw (\<lambda>b. {x \<in> A. b x}) (PiE_dflt A P (\<lambda>_. UNIV)) (Pow A)"
      by (rule bij_betwI[of _ _ _ "\<lambda>B b. if b \<in> A then b \<in> B else P"]) (auto simp add: PiE_dflt_def)
    then show ?thesis
      using assms by (intro map_pmf_of_set_bij_betw) auto
  qed
  finally show ?thesis
    by simp
qed

lemma Pi_pmf_insert':
  assumes  "finite A"  "x \<notin> A"
  shows "Pi_pmf (insert x A) dflt p =
         (p x \<bind>
         (\<lambda>g. Pi_pmf A dflt p \<bind>
         (\<lambda>f. return_pmf (f(x := g)))))"
  using assms 
  by (subst Pi_pmf_insert)
    (auto simp add: map_pmf_def pair_pmf_def case_prod_beta' bind_return_pmf bind_assoc_pmf)

end

