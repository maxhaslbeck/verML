\<^marker>\<open>creator Eric Koepke\<close>

theory LinearPredictor
  imports VCDim
begin

paragraph \<open>Summary\<close>
text \<open>This theory proves "The Fundamental Theorem of Statistical Learning"
        and coresponds to chapter 6 of @{cite UnderstandingML}.\<close>

paragraph \<open>Main Definitions\<close>
text \<open>
\<^item> \<open>linear_predictor\<close>: Linear Predictor
\<close>

paragraph \<open>Main Theorems\<close>
text \<open>
\<^item> \<open>linvcd\<close>: The VC dimension of the class of homogenous halfspaces in \<open>R^d\<close> is \<open>d\<close> 
              (Lemma 9.2. of @{cite UnderstandingML}).
\<close>


definition "linear_predictor w = (\<lambda>x. minner w x > 0)"

definition "all_linear V = image linear_predictor V"


lemma dimsub: "0 < dim T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> dim S \<le> dim T" 
proof -
  assume a1: "S \<subseteq> T"
  assume a2: "0 < dim T"
  obtain B where o1: "B \<subseteq> T" "independent B" "T \<subseteq> span B" "card B = dim T"
    using basis_exists by auto
  have "finite B" using a2
    by (simp add: o1(4) card_ge_0_finite)
  then have "dim S \<le> card B" using dim_le_card a1 o1(3) by auto
  then show "dim S \<le> dim T" using o1(4) by auto
qed
  

lemma fixes V::"(movec) set" (* euclidean_space*)
  assumes "dim V < card B" 
          and "B\<subseteq>V"
          and "0 < dim V"
        shows upper_dim: "\<not> shatters (image mapify (all_linear V)) B {True, False}"
proof(rule ccontr)
  have fB: "finite B" using assms card_infinite by fastforce
  moreover have "dim B < card B" using assms dimsub
    by (metis dim_le_card' fB leD le_neq_implies_less)
  ultimately obtain f x1 where o3: "sum (\<lambda>x. scaleR (f x)  x) B = 0" "(f x1 \<noteq> 0)" "x1\<in>B"
    by (metis assms dependent_finite dim_eq_card_independent nat_neq_iff)
  moreover have "{b\<in>B. f b \<ge> 0} \<union> {b\<in>B. f b < 0} = B" by auto
  moreover have "{b\<in>B. f b \<ge> 0} \<inter> {b\<in>B. f b < 0} = {}" by auto
  moreover have "finite {b\<in>B. f b \<ge> 0}" using fB by auto
  moreover have "finite {b\<in>B. f b < 0}" using fB by auto
  ultimately have "sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b \<ge> 0} = - sum (\<lambda>x. scaleR ((f x))  x) {b\<in>B. f b < 0}"
    using sum.union_disjoint
    by (metis (mono_tags, lifting) add.inverse_inverse add_eq_0_iff)
  also have "... = sum (\<lambda>x. scaleR (abs(f x))  x) {b\<in>B. f b < 0}"
      proof -
        have f1: "\<forall>a. (a \<in> {a \<in> B. f a < 0}) = (a \<in> B \<and> \<not> 0 \<le> f a)"
          by fastforce
      have f2: "\<forall>a. if 0 \<le> f a then (if f a < 0 then - f a else f a) *\<^sub>R a = f a *\<^sub>R a else (if f a < 0 then - f a else f a) *\<^sub>R a = (- 1 * f a) *\<^sub>R a"
      by force
        { assume "- (f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) \<noteq> (if f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) < 0 then - f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) else f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0})) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}"
          then have "(if f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) < 0 then - f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) else f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0})) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0} \<noteq> (- 1 * f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0})) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}"
            by simp
          then have "v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0} \<notin> {a \<in> B. f a < 0} \<or> - (f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) = (if f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) < 0 then - f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}) else f (v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0})) *\<^sub>R v4_0 (\<lambda>a. (if f a < 0 then - f a else f a) *\<^sub>R a) (\<lambda>a. - (f a *\<^sub>R a)) {a \<in> B. f a < 0}"
            using f2 f1 by meson }
        then show ?thesis
          by (simp add: sum_negf)
      qed        
  finally have f1: "sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b \<ge> 0} = sum (\<lambda>x. scaleR (abs(f x))  x) {b\<in>B. f b < 0}"
    by auto
  have "{b\<in>B. f b \<ge> 0} = {b\<in>B. f b > 0} \<union> {b\<in>B. f b = 0}" by auto
  moreover have "{} = {b\<in>B. f b > 0} \<inter> {b\<in>B. f b = 0}" by auto
  moreover have "finite {b\<in>B. f b > 0}" using fB by auto
  moreover have "finite {b\<in>B. f b = 0}"using fB by auto
  ultimately have "sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b \<ge> 0} = sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b > 0} +
            sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b = 0}" using sum.union_disjoint by (metis (no_types, lifting))
  from f1 this have f4: "sum (\<lambda>x. scaleR (f x)  x) {b\<in>B. f b > 0} = sum (\<lambda>x. scaleR (abs(f x))  x) {b\<in>B. f b < 0}"
    by auto

  let ?T = "f x1 > 0"
  let ?F = "\<not>?T"
  let ?TS = "(if ?T then {b\<in>B. f b > 0} else {b\<in>B. f b < 0})"
  let ?FS = "(if ?F then {b\<in>B. f b > 0} else {b\<in>B. f b < 0})"

  have f5: "x1\<in>?TS" using o3 by auto
  obtain m where o1: "\<forall>x. m x = (if x\<in>B then (if f x > 0 then Some ?T else Some ?F) else None)" by fastforce
  then have f2: "\<forall>x\<in>{b\<in>B. f b > 0}. m x = Some ?T" "\<forall>x\<in>{b\<in>B. f b < 0}. m x = Some ?F"
    by auto
  from o1 have "ran m \<subseteq> {True, False}" by blast
  moreover from o1 have f3: "dom m = B"
    by (meson domI domIff subsetI subset_antisym)
  moreover have "B\<noteq>{}" using \<open>dim B < card B\<close> by auto 
  ultimately have "m \<in> (allmaps B {True, False})"
    by (simp add: allmaps_def)
  moreover assume "\<not> \<not> shatters (mapify ` all_linear V) B {True, False}"
  ultimately obtain h where o2: "h\<in>(mapify ` all_linear V)" "m \<subseteq>\<^sub>m h" using alt_shatters by blast
  then obtain w where o3: "mapify (linear_predictor w) = h" using all_linear_def
    by (metis (mono_tags, hide_lams) image_iff)
  have "\<forall>x\<in>?TS. minner w x > 0"
    using f2 o2(2) o3 f3 linear_predictor_def map_le_def mapify_def 
    by (metis (no_types, lifting) mem_Collect_eq option.inject)
  moreover from this f5 have "(abs(f x1)) * (minner w x1) > 0"
    using zero_less_mult_iff by fastforce
  ultimately have "sum (\<lambda>x. (abs(f x)) * (minner w x)) ?TS  > 0" using f5
    by (smt \<open>finite {b \<in> B. 0 < f b}\<close> \<open>finite {b \<in> B. f b < 0}\<close> mult_nonneg_nonneg sum_nonneg sum_nonneg_0) 
  then have "sum (\<lambda>x. minner w (scaleR (abs(f x)) x)) ?TS  > 0" using minner_scale minner_comm by auto
  moreover have "finite ?TS"  by (simp add: \<open>finite {b \<in> B. 0 < f b}\<close> \<open>finite {b \<in> B. f b < 0}\<close>)
  ultimately have "minner w (sum (\<lambda>x. scaleR (abs(f x)) x) ?TS) > 0"
    by (simp add: minner_sum) 
  moreover from f4 have "sum (\<lambda>x. scaleR (abs(f x)) x) ?TS = sum (\<lambda>x. scaleR (abs(f x))  x) ?FS"
    by auto
  ultimately have "minner w (sum (\<lambda>x. scaleR (abs(f x)) x) ?FS) > 0" by auto
  moreover have "finite ?FS"  by (simp add: \<open>finite {b \<in> B. 0 < f b}\<close> \<open>finite {b \<in> B. f b < 0}\<close>)
  ultimately have "sum (\<lambda>x. minner w (scaleR (abs(f x)) x)) ?FS  > 0" 
    by (simp add: minner_sum)
  then have "sum (\<lambda>x. (abs(f x)) * (minner w x)) ?FS  > 0" using minner_scale minner_comm by auto
  moreover have "\<forall>x\<in>?FS. minner w x \<le> 0" 
    using f2 o2(2) o3 f3 linear_predictor_def map_le_def mapify_def
    by (smt domI option.inject)
  ultimately show False
    by (smt sum_nonpos zero_less_mult_iff)
qed

lemma aux41: "ran m \<subseteq> R \<Longrightarrow> x \<in> dom m \<Longrightarrow> m x \<in> image Some R"
  by (metis domD imageI ranI subsetCE)


(*remove unnecessary parts*)
lemma lower_dim: "shatters (image mapify (all_linear (myroom d))) (mybasis d) {True, False}"
proof -
  let ?B = "(image (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0)) {..<d})"
  have f1: "\<forall>(k::nat). (\<lambda>i. if i = k then 1 else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
     by auto
  then have "\<forall>k j. k = j \<longleftrightarrow> vec_lambda (\<lambda>i. if i = k then 1 else 0) = vec_lambda (\<lambda>i. if i = j then 1 else 0)"
    using fun_eq_iff movec.vec_lambda_inject by smt
  then have "inj (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0))" by (meson injI) 
  then have "card ?B = d"
    by (metis (no_types, lifting) card_image card_lessThan injD inj_on_def)
  moreover have "?B \<subseteq> (myroom d)"
    by(rule mybasis_subset_myroom[unfolded unit_vec_def mybasis_def])
  moreover have "(\<forall>m\<in>(allmaps ?B {True, False}).\<exists>h\<in>(image mapify (all_linear (myroom d))). m \<subseteq>\<^sub>m h)"
  proof
    fix m
    assume a1: "m\<in>(allmaps ?B {True, False})"
    then have f15: "\<forall>k\<in>{..<d}. m ((\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0)) k) \<in> image Some {True, False}"
    proof(cases "d = 0")
      case True
      then show ?thesis by auto
    next
      case False
      then have "?B \<noteq> {}" by auto
      then show ?thesis using allmaps_def aux41 a1
        by (smt image_eqI mem_Collect_eq) 
    qed
    let ?v = "(\<lambda>x. (if x = Some True then 1 else -1))"
    obtain w where o0: "\<forall>k<d. vec_nth w k = (?v \<circ> m \<circ> (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0))) k" "w\<in>(myroom d)"
      using exmovec myroom_def by blast
    have "\<forall>x\<in>?B. mapify (linear_predictor w) x = m x"
    proof
      fix x
      assume a1: "x \<in> (\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) ` {..<d}"
      then obtain k where o1: "x = (\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) k" "k < d"
        by auto
      then have f2: "\<forall>j\<noteq>k. vec_nth x j = 0" using movec.vec_lambda_cases f1 movec.vec_lambda_inverse
              proof -
                { fix nn :: nat
                  obtain rr :: "movec \<Rightarrow> nat \<Rightarrow> real" where
                    ff1: "\<forall>m. movec.vec_nth m = rr m"
                    by blast
                  then have "\<forall>f. rr (movec.vec_lambda f) = f \<or> f \<notin> {f. \<exists>n. \<forall>na>n. f na = 0}"
                    by (metis (no_types) movec.vec_lambda_inverse)
                  then have "\<forall>n. rr (movec.vec_lambda (\<lambda>na. if na = n then 1 else 0)) = (\<lambda>na. if na = n then 1 else 0)"
                    using f1 by blast
                  then have "nn = k \<or> movec.vec_nth x nn = 0"
                    using ff1 o1(1) by presburger }
                then show ?thesis
                  by meson
              qed
      have f3: "vec_nth x k = 1" using movec.vec_lambda_cases f1 movec.vec_lambda_inverse
        by (smt \<open>\<And>thesis. (\<And>k. \<lbrakk>x = movec.vec_lambda (\<lambda>i. if i = k then 1 else 0); k < d\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> f2)
        
      then have f4: "minner w x = vec_nth w k"
          proof (cases "vec_nth w k = 0")
            case True
            then have "{q. movec.vec_nth w q \<noteq> 0 \<and> movec.vec_nth x q \<noteq> 0} = {}"
              using f2 by fastforce
            then show ?thesis using minner_def sum.neutral
              by (metis (no_types, lifting) Collect_cong True empty_iff)
          next
            case False
            then have "{q. movec.vec_nth w q \<noteq> 0 \<and> movec.vec_nth x q \<noteq> 0} = {k}"
              using f2 f3 by fastforce 
            then show ?thesis using minner_def f2 f3 by auto
          qed
      show "mapify (linear_predictor w) x = m x"
      proof(cases "m x = Some True")
        case True
        then have "vec_nth w k = 1" using o0 o1 by simp
        (*then have "minner w x = 1"*)
      then show ?thesis using f4 linear_predictor_def True
        by (simp add: mapify_def) 
      next
        case False
        then have "m x = Some False" using f15 a1 by auto
        moreover from this have "vec_nth w k = -1" using o0 o1 by simp
        ultimately show ?thesis using f4 linear_predictor_def
          by (simp add: mapify_def) 
      qed
    qed
      then have "m \<subseteq>\<^sub>m (mapify (linear_predictor w))" using a1 map_le_def allmaps_def
            proof -
            have f1: "\<forall>f fa. (fa \<in> Collect ((\<subseteq>\<^sub>m) f)) = (\<forall>m. (m::movec) \<notin> dom f \<or> (f m::bool option) = fa m)"
            by (simp add: Ball_def_raw map_le_def)
            have f2: "m \<in> ( {f. dom f = (\<lambda>n. movec.vec_lambda (\<lambda>na. if na = n then 1 else 0)) ` {..<d} \<and> ran f \<subseteq> {True, False}})"
              using a1 allmaps_def by (simp add: allmaps_def)(* by blast *)
              have f3: "\<forall>F f. F \<noteq> {} \<or> (f::movec \<Rightarrow> bool option) \<notin> F"
                by blast
              have "\<forall>M B f. (f \<in> {f. dom f = (M::movec set) \<and> ran f \<subseteq> (B::bool set)}) = (dom f = M \<and> ran f \<subseteq> B)"
                by simp
              then have "mapify (linear_predictor w) \<in> Collect ((\<subseteq>\<^sub>m) m)"
                using f3 f2 f1 \<open>\<forall>x\<in>(\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) ` {..<d}. mapify (linear_predictor w) x = m x\<close> by presburger
              then show ?thesis
                by blast
            qed 
            moreover have "mapify (linear_predictor w) \<in> (image mapify (all_linear (myroom d)))"
              using o0(2) all_linear_def by blast
            ultimately show "\<exists>h\<in>(image mapify (all_linear (myroom d))). m \<subseteq>\<^sub>m h" by auto
          qed
          ultimately show ?thesis
            using alt_shatters mybasis_def unit_vec_def
            by (metis (no_types, lifting) image_cong)

 qed



locale linpred =
  fixes d::nat
  assumes dgone: "d>1"
begin

lemma dgz: "d>0" using dgone by auto

interpretation vcd "myroom d" "{True, False}" "all_linear (myroom d)"
proof
  show "infinite (myroom d)" using dgz infiniteroom by auto
  show "card {True, False} = 2" by auto
  show "\<forall>h x. h \<in> all_linear (myroom d) \<longrightarrow> h x \<in> {True, False}" by auto
  show "all_linear (myroom d) \<noteq> {}"
    using \<open>infinite (myroom d)\<close> all_linear_def by force
qed

\<comment> \<open>Theorem 9.2\<close>
lemma linvcd: "VCDim = Some d" unfolding VCDim_alt
proof
  have "mybasis d \<subseteq> myroom d" using roomSpan
    by (simp add: span_superset) 
  then show "\<exists>C\<subseteq>myroom d. card C = d \<and> shatters H_map C {True, False}"
    using lower_dim cardbasis by metis
  show "\<not> (\<exists>C\<subseteq>myroom d. d < card C \<and> shatters H_map C {True, False})"
    using upper_dim dim_room
    by (simp add: dgz)
qed

lemma vaux: "(\<lambda>h. h |` C) ` H_map = (\<lambda>h. restrict_map (mapify h) C) ` (all_linear (myroom d))" by auto

lemma vmain: "card C \<le> m \<Longrightarrow> finite C \<Longrightarrow> d \<le> m \<Longrightarrow> C \<subseteq> (myroom d) \<Longrightarrow> card ((\<lambda>h. restrict_map (mapify h) C) ` (all_linear (myroom d))) \<le> m^d"
  using resforboost[of C d m] vaux linvcd dgone by auto

lemma vfinite: "finite C \<Longrightarrow> finite ((\<lambda>h. restrict_map (mapify h) C) ` (all_linear (myroom d)))"
  using finiteres[of C "{True, False}" "H_map"] restrictH_map_conv[of C] vaux[of C] by simp

lemma "0<(m::nat) \<Longrightarrow> growth m \<le> sum (\<lambda>x. m choose x) {0..d}"
  using lem610 linvcd by auto

end


end

