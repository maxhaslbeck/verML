theory VCDim2
  imports Main
begin
  
term Max
  
definition "mapify f = (\<lambda>x. Some (f x))" (*This should exist somewhere*)
  
definition "allmaps C D = (if C = {} then {} else {m. dom m = C \<and> ran m \<subseteq> D})"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"

lemma finitemaps: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (allmaps C D)"
  by (simp add: allmaps_def finite_set_of_finite_maps)

lemma finiteres: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (restrictH H C D)"
  by (simp add: finitemaps restrictH_def)

lemma "shatters H C D \<longleftrightarrow> (\<forall>m\<in>(allmaps C D).\<exists>h\<in>H. m \<subseteq>\<^sub>m h)" 
  by (smt Collect_cong dom_def dom_empty mem_Collect_eq restrictH_def allmaps_def shatters_def)
  
lemma empty_shatted: "shatters H {} D"
  by (simp add: allmaps_def restrictH_def shatters_def)

locale vcd =
  fixes X :: "'a set"
    and Y :: "'b set"  
  assumes 
      "X \<noteq> {}" 
    and infx: "infinite X"
    and "card Y = 2" (* is never used! *)
begin

definition "VCDim H = (if finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H C Y} then Some (Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H C Y}) else None)"
(* definition "VCDim H D = (if \<exists>m. (\<forall>C\<subseteq>X. card C > m \<longrightarrow> \<not>shatters H C D) \<and> (\<exists>C2\<subseteq>X. shatters H C2 D) then Some m else None)" *)

definition "growth H m = Max {k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m}"

lemma "{k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
  
lemma assumes "VCDim H = Some m" 
  shows "(\<exists>C\<subseteq>X. card C = m \<and> shatters H C Y)"
   and noshatter: "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H C Y)"
proof -
  have s1: "m = Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.discI option.inject)
  moreover have s2: "finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.simps(3))
   moreover have "{m. \<exists>C\<subseteq>X. card C = m \<and> shatters H C Y} \<noteq> {}"
    using empty_shatted by fastforce
  ultimately show "\<exists>C\<subseteq>X. card C = m \<and> shatters H C Y" using Max_in by auto
  show "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H C Y)"
    by (metis (mono_tags, lifting) Max_ge leD mem_Collect_eq s1 s2)
qed
  

(*Equation 6.3*)
lemma eq63: "finite C \<Longrightarrow> card (restrictH H C Y) \<le> card ({B. B\<subseteq>C \<and> shatters H B Y})"
proof (induct rule: finite.induct)
  case emptyI
  then show ?case by (simp add: allmaps_def restrictH_def)
next
  case (insertI A a)
  then show ?case sorry
qed

(*lemma "m>0 \<Longrightarrow> card C = m \<Longrightarrow> card ({B. B\<subseteq>C}) \<le> 2^m"  
proof -
  have "" *)

lemma "finite {k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m}" using finiteres oops

lemma assumes "VCDim H = Some d"
      and "m>0"
      and "C\<subseteq>X"
      and "card C = m"
    shows superaux: "card (restrictH H C Y) \<le> sum (\<lambda>x. m choose x) {0..d}"
proof -
  have f3: "finite C" using assms(2,4) card_ge_0_finite by auto
 have "\<forall>B\<subseteq>C. shatters H B Y \<longrightarrow> card B \<le> d" using assms noshatter
    by (meson \<open>C \<subseteq> X\<close> not_le_imp_less order_trans)
  then have f2: "{B. B\<subseteq>C \<and> shatters H B Y} \<subseteq> {B. B\<subseteq>C \<and> card B \<le> d}" by auto
  have f1: "finite {B. B\<subseteq>C \<and> card B \<le> d}" using f3 by auto
  have "card {B. B\<subseteq>C \<and> card B \<le> d} \<le> sum (\<lambda>x. m choose x) {0..d}"
  proof (induction d)
    case 0
    have "{B. B \<subseteq> C \<and> card B \<le> 0} = {{}}"
      using f3 infinite_super by fastforce
    then show ?case by simp
  next
    case (Suc d)
    have "{B. B \<subseteq> C \<and> card B \<le> Suc d} = {B. B \<subseteq> C \<and> card B \<le> d} \<union> {B. B \<subseteq> C \<and> card B = Suc d}" by auto
    moreover have "{B. B \<subseteq> C \<and> card B \<le> d} \<inter> {B. B \<subseteq> C \<and> card B = Suc d} = {}" by auto
    ultimately have "card {B. B \<subseteq> C \<and> card B \<le> Suc d} = card {B. B \<subseteq> C \<and> card B \<le> d} + card {B. B \<subseteq> C \<and> card B = Suc d}" using f1
        by (simp add: f3 card_Un_disjoint)
    then show ?case using f3 by (simp add: n_subsets assms(4) Suc.IH)
  qed
  from this f2 have "card {B. B\<subseteq>C \<and> shatters H B Y} \<le> sum (\<lambda>x. m choose x) {0..d}"
    by (metis (no_types, lifting) card_mono f1 order_trans)
  then show "card (restrictH H C Y) \<le> sum (\<lambda>x. m choose x) {0..d}" using eq63 f3
    by (metis (mono_tags, lifting) Collect_cong dual_order.strict_trans1 neq_iff not_le_imp_less)
qed

(*Sauers Lemma 6.10*)
lemma assumes "VCDim H = Some d"
      and "m>0"
  shows "growth H m \<le> sum (\<lambda>x. m choose x) {0..d}"
 (* using n_subsets growth_def eq63 noshatter *)
proof -
  have "\<forall>n \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m}. n \<le> sum (\<lambda>x. m choose x) {0..d}" using superaux assms(1,2)
    by fastforce
  then have "finite {k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m}"
    using finite_nat_set_iff_bounded_le by auto
  moreover have "{k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
  ultimately have "growth H m \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H C Y) \<and> card C = m}"
    using Max_in growth_def by auto
  then show ?thesis
    using assms(1) assms(2) vcd.superaux vcd_axioms by fastforce
qed
  


text \<open>Definition of the Prediction Error (2.1). 
    This is the Isabelle way to write: 
      @{text "L\<^sub>D\<^sub>,\<^sub>f(h) =  D({S. f S \<noteq> h S})"} \<close>
definition PredErr :: "'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "PredErr D f h = measure_pmf.prob D {S. f S \<noteq> h S}" 


text \<open>Definition of the Training Error (2.2). \<close>
definition TrainErr :: " ('c \<Rightarrow> ('a * 'b)) \<Rightarrow> 'c set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "TrainErr S I h = sum (\<lambda>i. case (S i) of (x,y) \<Rightarrow> if h x \<noteq> y then 1::real else 0) I / card I"


(* Sample D f, takes a sample x of the distribution D and pairs it with its
    label f x; the result is a distribution on pairs of (x, f x). *)
definition Sample ::"'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) pmf" where
  "Sample D f = do {  a \<leftarrow> D;
                      return_pmf (a,f a) }"


(* Samples n D f, generates a distribution of training sets of length n, which are
     independently and identically distribution wrt. to D.  *)
definition Samples :: "nat \<Rightarrow> 'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ((nat \<Rightarrow> 'a \<times> 'b)) pmf" where
  "Samples n D f = Pi_pmf {0..<n} undefined (\<lambda>_. Sample D f)"

(*Theorem 6.11*)
lemma assumes "set_pmf D \<subseteq> X"
      and "f ` X = Y"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
      and "h\<in>H"
    shows "measure_pmf.prob (Samples m D f) {S. abs(PredErr D f h - TrainErr S {0..<m} h) \<le> (4+sqrt(ln(real(growth (image mapify H) (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
  sorry



