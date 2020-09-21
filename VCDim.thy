theory VCDim
  imports Complex_Main LearningTheory RpowD
begin


section "Combinatorics over maps"

definition "mapify f = (\<lambda>x. Some (f x))"
definition "allmaps C D = {m. dom m = C \<and> ran m \<subseteq> D}"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"

lemma mapify_alt: "mapify f = Some \<circ> f" unfolding mapify_def by auto

lemma "C \<subseteq> dom h \<Longrightarrow> dom (restrict_map h C) = C" by auto

lemma restrict_map_to_dom: "x \<subseteq>\<^sub>m h \<Longrightarrow> restrict_map h (dom x) = x" 
  by (auto simp: domIff restrict_map_def map_le_def) 

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

lemma dom_mapify_restrict: "m \<in> (\<lambda>h. mapify h |` C) ` H \<Longrightarrow> dom m = C"
proof -
  assume "m \<in> (\<lambda>h. mapify h |` C) ` H"
  then obtain h where o1: "h\<in>H" "(\<lambda>h. mapify h |` C) h = m" by auto
  then have "dom (mapify h) = UNIV" 
    by (simp add: mapify_def)
  then show "dom m = C"
    using dom_restrict o1 by fastforce
qed

lemma finitemaps: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (allmaps C D)"
  by (simp add: allmaps_def finite_set_of_finite_maps)

lemma finiteres: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (restrictH H C D)"
  by (simp add: finitemaps restrictH_def)

lemma alt_shatters: "shatters H C D \<longleftrightarrow> (\<forall>m\<in>(allmaps C D).\<exists>h\<in>H. m \<subseteq>\<^sub>m h)" 
  by (smt Collect_cong dom_def dom_empty mem_Collect_eq restrictH_def allmaps_def shatters_def)
  
(*lemma empty_shatted: "shatters H {} D"
  by (simp add: allmaps_def restrictH_def shatters_def)*)

lemma hx_none: "h\<in>restrictH H C D \<Longrightarrow> x \<in> C \<Longrightarrow> h x \<noteq> None"
  by (metis (mono_tags, lifting) allmaps_def domIff mem_Collect_eq restrictH_def)


lemma assumes "dom (f::('a \<Rightarrow> 'b option)) = {}"
  shows allmaps_e: "allmaps {} D = {f}"
proof -
    have "f\<in>(allmaps {} D)" using assms by (simp add: allmaps_def)
    moreover have "\<forall>g\<in>(allmaps {} D). g = f" using assms
      by (simp add: allmaps_def)
    ultimately show ?thesis by blast
  qed


lemma fixes m d
  assumes "m\<in>(allmaps F D)" "d\<in>D" 
  shows upd_in_all: "m(x:=Some d)\<in>(allmaps (insert x F) D)"
  using assms by(auto simp: allmaps_def ran_def map_upd_Some_unfold) 

lemma "(\<forall>x\<in>A. \<forall>y\<in>A. x\<noteq>y \<longrightarrow> f x \<noteq> f y) \<Longrightarrow> inj_on f A"
  using inj_on_def by blast

lemma "bij_betw f A B \<Longrightarrow> bij_betw f A' B' \<Longrightarrow> A = A' \<Longrightarrow> B = B'" 
   by (simp add: bij_betw_def) 

lemma assumes  "x\<notin>F" "m_1\<in>allmaps F D" "m_2\<in>allmaps F D" "m_1(x \<mapsto> d_1) = m_2(x \<mapsto> d_2)"
  shows aux392: "m_1 = m_2"
    by (metis (mono_tags, lifting) allmaps_def assms domIff fun_upd_triv fun_upd_upd mem_Collect_eq) 
 

lemma  allmaps_insert_image_update: 
  assumes "x\<notin>F"
  shows"h \<in> allmaps (insert x F) D \<Longrightarrow> \<exists>e\<in>D. h \<in> (\<lambda>m. m(x \<mapsto> e)) ` (allmaps F D)"
proof -
  fix m
  assume a1: "m \<in> allmaps (insert x F) D"
  let ?n = "m(x:=None)"
  have "dom ?n = F"
    by (metis (mono_tags, lifting) Diff_insert_absorb a1 allmaps_def assms dom_fun_upd mem_Collect_eq)
  have "ran m \<subseteq> D" using allmaps_def a1 by fastforce
  then have "ran ?n \<subseteq> D"
    by (metis ranI ran_restrictD restrict_complement_singleton_eq subsetCE subsetI) 
  then have "?n \<in> allmaps F D"
    using \<open>dom (m(x := None)) = F\<close> allmaps_def by blast
  obtain d where o1: "m x = Some d"
    by (metis (mono_tags, lifting) a1 allmaps_def domD insertI1 mem_Collect_eq)
  then have "d\<in>D"
    by (meson \<open>ran m \<subseteq> D\<close> ranI subsetCE)
  have *: "(\<lambda>(m, d). m(x \<mapsto> d)) (?n,d) = m" using o1 by auto
  show "\<exists>e\<in>D. m \<in> (\<lambda>m. m(x \<mapsto> e)) ` (allmaps F D)"
    apply(rule bexI[where x=d])
    subgoal unfolding image_iff
      apply(rule bexI[where x="?n"]) using o1 
      using \<open>m(x := None) \<in> allmaps F D\<close> by auto
    by fact
qed


lemma upd_inj_on: "\<And>y. x\<notin>F \<Longrightarrow> inj_on (\<lambda>m. m(x \<mapsto> y)) (allmaps F D)" by (meson aux392  inj_onI)

lemma assumes "x\<notin>F"
  shows bij_allmaps: "bij_betw (\<lambda>(m,d). m(x:=Some d)) ((allmaps F D) \<times> D) (allmaps (insert x F) D)"
  apply(rule bij_betw_imageI)
  subgoal
    apply(simp add: inj_on_def)
    by (meson assms aux392 map_upd_eqD1)
  apply rule
  subgoal using upd_in_all by fastforce
  subgoal using allmaps_insert_image_update[OF assms] by fast 
  done


lemma assumes "finite D"
    shows mappow: "finite C \<Longrightarrow> card (allmaps C D) = (card D) ^ (card C)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by (simp add: allmaps_e) 
next
  case c1: (insert x F)
  then have "card (insert x F) = card F + 1"
    by auto
  from this c1 have "card D ^ card (insert x F) = card (allmaps F D) * card D"
    by simp
  also have "... = card (allmaps F D \<times> D)"
    by (simp add: card_cartesian_product)
  also have "... = card (allmaps (insert x F) D)" 
    using bij_allmaps[of x F D] bij_betw_same_card c1(2) by auto
  finally show ?case by auto
qed


lemma allmaps_insert: 
  fixes D
  assumes "x\<notin>F"
  shows "allmaps (insert x F) D = (\<Union>y\<in>D. (\<lambda>m. m(x:=Some y)) ` allmaps F D)"
  apply (auto simp:  )
  subgoal for h
    apply(rule allmaps_insert_image_update)
    using assms by auto
  subgoal using upd_in_all by metis
  done

section "Definition VC-Dimension"

locale vcd =learning_basics where X=X and Y=Y and H=H
  for X::"'a set" and Y::"'b set" and H :: "('a \<Rightarrow> 'b) set" +
assumes infx: "infinite X"
begin

abbreviation "H_map \<equiv> image mapify H"

definition "VCDim = (if finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} then Some (Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}) else None)"

definition "growth m = Max {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"

lemma "X \<noteq> {}" using infx by auto

lemma ranh: "\<forall>h\<in>H_map. ran h \<subseteq> Y" using Hdef mapify_def
  by (smt imageE mem_Collect_eq option.simps(1) ran_def subset_iff)

lemma domh: "\<forall>h\<in>H_map. dom h = UNIV"
  by (simp add: mapify_def) 

lemma nnHmap: "H_map \<noteq> {}" using nnH by auto

lemma restrictH_map_conv: "restrictH H_map C Y = (\<lambda>h. restrict_map h C) ` H_map" 
  using auxtemp domh ranh by blast

lemma finite_restrict: "finite C \<Longrightarrow> finite ((\<lambda>h. restrict_map h C) ` H_map)"
proof -
  assume "finite C"
  moreover have "finite Y" using cardY card_infinite by force
  ultimately show ?thesis using restrictH_map_conv[of C] finiteres[of C Y H_map] by auto
qed


lemma assumes "H'\<noteq>{}" "H'\<subseteq>H_map"
    shows empty_shatted: "shatters H' {} D"
  unfolding shatters_def restrictH_def
proof -
  obtain h where "h\<in>H'" using assms by auto
  moreover obtain f::"('a \<Rightarrow> 'b option)" where s1: "dom f = {}" by auto
  moreover from this have "f \<subseteq>\<^sub>m h" by auto
  moreover have "allmaps {} D = {f}" using allmaps_e s1(1) by blast 
  ultimately show "allmaps {} D = {m \<in> allmaps {} D. Bex H' ((\<subseteq>\<^sub>m) m)}"
    by auto
qed


  (*
lemma "{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
*)

lemma assumes "(\<forall>C\<subseteq>X. shatters H_map C Y \<longrightarrow> (card C) \<le> q)"
  shows vcd_upper: "\<exists>d. VCDim = Some d \<and>  d \<le> q"
proof -
  have s1: "\<forall>k\<in>{m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}. k \<le> q"
    using assms by auto
  then have f1: "finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}"
    using finite_nat_set_iff_bounded_le by blast 
  then obtain d where "VCDim = Some d" using VCDim_def by auto
  moreover from this have "d\<le>q" using s1 VCDim_def
    by (metis (mono_tags, lifting) Max_in empty_iff f1 mem_Collect_eq nnHmap option.simps(1) subsetI vcd.empty_shatted vcd_axioms) 
  ultimately show ?thesis by auto
qed

lemma assumes "VCDim = Some m" 
  shows doshatter: "(\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y)"
   and noshatter: "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"
proof -
  have s1: "m = Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.discI option.inject)
  moreover have s2: "finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.simps(3))
   moreover have "{m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} \<noteq> {}"
    using empty_shatted nnHmap
    by (metis (mono_tags, lifting) empty_iff empty_subsetI mem_Collect_eq subset_refl)
  ultimately show "\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y" using Max_in by auto
  show "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"
    by (metis (mono_tags, lifting) Max_ge leD mem_Collect_eq s1 s2)
qed


lemma VCDim_alt: "VCDim = Some m \<longleftrightarrow>
  (\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y) \<and>
   \<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"
  apply rule
  apply (simp add: doshatter noshatter)
  apply (rule conjE[of "(\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y)" "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"])
  apply simp
proof -
  assume a1: "(\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y)"
  assume a2: "\<not> (\<exists>C\<subseteq>X. m < card C \<and> shatters H_map C Y)"
  then have "\<forall>k\<in>{m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}. k \<le> m"
    using leI by blast
  moreover from this have f1: "finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}"
    using finite_nat_set_iff_bounded_le by auto
  moreover from a1 have "m \<in> {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}" by auto
  ultimately have "Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} = m"
    by (meson Max_eqI)
  then show "VCDim = Some m"
    using VCDim_def f1 by auto
qed

section "Sauers Lemma"

lemma "\<exists>f. bij_betw f Y {True, False}"
proof -
  obtain y1 where "y1 \<in> Y" using cardY by fastforce
  obtain y2 where "y2 \<in> Y" "y2 \<noteq> y1" using cardY
    by (metis card_2_iff')
  then obtain f where "f y1 = True" "f y2 = False" by auto
  have "bij_betw f Y {True, False}"
    apply (rule bij_betwI')
    apply (metis \<open>f y1 = True\<close> \<open>f y2 = False\<close> \<open>y1 \<in> Y\<close> \<open>y2 \<in> Y\<close> cardY card_2_iff')
    apply simp
    using \<open>f y1 = True\<close> \<open>f y2 = False\<close> \<open>y1 \<in> Y\<close> \<open>y2 \<in> Y\<close> by blast
  then show ?thesis by auto
qed
    
lemma aux394: "m\<in> restrictH H' C Y \<Longrightarrow> \<exists>h. h\<in>H' \<and> m \<subseteq>\<^sub>m h"
  by (simp add: Bex_def_raw restrictH_def) 


lemma card_some_y: "card (Some ` Y) = 2"
proof -
  have "bij_betw Some Y (Some ` Y)"
    by (simp add: bij_betw_imageI)
  then show ?thesis
    using bij_betw_same_card cardY by fastforce
qed

lemma card_2_explicit: "a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> a\<noteq>b \<Longrightarrow> card A = 2 \<Longrightarrow> A = {a,b}"
  by (smt One_nat_def Suc_inject card.remove card_1_singletonE card_infinite doubleton_eq_iff
      insert_Diff_single insert_absorb2 mk_disjoint_insert numeral_2_eq_2 zero_neq_numeral)


lemma sum_union_inter:
  fixes g :: "'v\<Rightarrow>nat"  and A B
  assumes "finite A "" finite B "" A\<inter>B={} "
  shows " sum g (A\<union>B) = sum g A + sum g B" 
proof - 
  have "sum g (A\<inter>B) = 0" using assms(3) by auto
  then have "sum g (A\<union>B) = sum g(A\<union>B) + sum g (A\<inter>B)" by auto
  also have "\<dots> = sum g A + sum g B" 
    apply(rule sum.union_inter) by fact+
  finally show ?thesis .
qed 


lemma over_shatter: "H1\<subseteq>H2 \<Longrightarrow> shatters H1 C D \<Longrightarrow> shatters H2 C D"
  by (meson alt_shatters subsetCE)

lemma allmaps_empty[simp]: "\<And>Z. allmaps {} Z = {Map.empty}"
  by(auto simp: allmaps_def)

lemma restrictH_Cempty[simp]: "\<And>D H. H \<noteq> {} \<Longrightarrow> restrictH H {} D = {Map.empty}"
  by(auto simp: restrictH_def)

lemma restrictH_Hempty[simp]: "\<And>D C. restrictH {} C D = {}"
  by(auto simp: restrictH_def)
 

(*Equation 6.3*)
lemma eq63: "finite C \<Longrightarrow> H'\<subseteq>H_map \<Longrightarrow> card (restrictH H' C Y) \<le> card ({B. B\<subseteq>C \<and> shatters H' B Y})"
proof (induct arbitrary: H' rule: finite_induct )
  case empty
  show ?case
  proof(cases "H' = {}")
    case False
    with empty have "restrictH H' {} Y = {Map.empty}" 
      "{B. B \<subseteq> {} \<and> shatters H' B Y} = { {} }"
      by (auto intro: empty_shatted) 
    then show ?thesis by simp
  qed auto 
next
  case c1: (insert c1 C' H)
  note a100 = c1(4) 

  have fF[simp]: "finite C'" using c1 by auto 
  have FY[simp]: "finite Y" using cardY
    using card_infinite by fastforce

\<comment> \<open>Define H'\<subseteq>H_map to be,\<close>
  let ?H' = "{h\<in>H. \<exists>h'\<in>H. h' c1 \<noteq> h c1 \<and> (\<forall>a\<in>C'. h' a = h a)}"

  have "?H' \<subseteq> H_map" using a100 by blast

\<comment> \<open>namely, H' contains pairs of hypotheses that agree on C' and differ on x.
    Using this definition it is clear that if H' shatters a set B \<subseteq> F then it also
    shatters the set B\<union>{x} (and vice versa, but we don't show that)\<close>

  have s40: "\<forall>B\<subseteq>C'. shatters ?H' B Y \<longrightarrow> shatters ?H' (insert c1 B) Y"
  proof(safe)
    fix B
    assume "B\<subseteq>C'"
    assume "shatters ?H' B Y"
    then have s1: "(\<forall>m\<in>(allmaps B Y).\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h)"  by (simp add: alt_shatters)
    have "(\<forall>m\<in>(allmaps (insert c1 B) Y).\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h)"
    proof
      fix m
      assume "m\<in>(allmaps (insert c1 B) Y)" 
      then obtain n d where o1: "m = (\<lambda>(m,d). m(c1:=Some d)) (n, d)" "n\<in> allmaps B Y" "d\<in>Y"
        using c1(2) bij_allmaps[of c1 B Y] \<open>B \<subseteq> C'\<close> bij_betw_imp_surj_on by blast
      then obtain h where o2: "h\<in>?H'" "n \<subseteq>\<^sub>m h" using s1 by blast
      then obtain h2 where o3: "h2 c1 \<noteq> h c1 \<and> (\<forall>a\<in>C'. h2 a = h a)" "h2\<in>H" by blast
      then have s2: "h2 \<in> ?H'"
        using o2(1) by force
      have "h \<in> H" using o2(1) by auto
      then have "h\<in>H_map" using \<open>H \<subseteq> H_map\<close> by blast
      have "h2\<in>H_map" using \<open>H \<subseteq> H_map\<close> o3(2) by blast
      have "Some ` Y = {h c1, h2 c1}"
      proof -
        have "ran h \<subseteq> Y"
          by (simp add: \<open>h \<in> H_map\<close> ranh)
        then have "h c1 \<in> Some ` Y"
          by (metis UNIV_I \<open>h \<in> H_map\<close> contra_subsetD domD domh imageI ranI)
        moreover have "h2 c1 \<in> Some ` Y"
          by (metis (mono_tags, hide_lams) Hdef \<open>h2 \<in> H_map\<close> image_iff mapify_def)
        ultimately show ?thesis using card_2_explicit o3(1)
          by (metis card_some_y)
      qed
      show "\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h"
      proof (cases "Some d = h c1")
        case True
        then show ?thesis
          by (metis (mono_tags, lifting) case_prod_conv fun_upd_triv map_le_upd o1(1) o2(1) o2(2)) 
      next
        case False
        then have "Some d = h2 c1"
          using \<open>Some ` Y = {h c1, h2 c1}\<close> o1(3) by blast 
        then show ?thesis
          by (metis (mono_tags, lifting) \<open>B \<subseteq> C'\<close> allmaps_def case_prod_conv fun_upd_triv map_le_def
              map_le_upd mem_Collect_eq o1(1) o1(2) o2(2) o3(1) s2 subset_iff) 
      qed
    qed
    then show "shatters ?H' (insert c1 B) Y" using alt_shatters by blast
  qed


\<comment> \<open>It is "easy to verify" that  = @{text \<open>|H\<^sub>C| = |H'\<^sub>C\<^sub>'\<^bold>| + |H\<^sub>C\<^sub>'\<^bold>| \<close>}\<close>

  have *: "card (restrictH H (insert c1 C') Y) = card (restrictH H C' Y) + card (restrictH ?H' C' Y)"
  proof -
  
    from cardY obtain a0 a1 where Y: "Y = {a0, a1}" "a0\<noteq>a1"  
      by (meson card_2_iff' card_2_explicit)  
    then have allmaps_insertY: "(allmaps (insert c1 C') Y)
       = ((\<lambda>m. m(c1 \<mapsto> a0)) ` allmaps C' Y) \<union> ((\<lambda>m. m(c1 \<mapsto> a1)) ` allmaps C' Y)"
      unfolding allmaps_insert[OF c1(2)] by fast  
  
    have disj: "((\<lambda>m. m(c1 \<mapsto> a0)) ` allmaps C' Y) \<inter> ((\<lambda>m. m(c1 \<mapsto> a1)) ` allmaps C' Y) = {}" 
      using Y(2) by (auto dest: map_upd_eqD1)  
  
  
    have k: "\<And>Hc C D. (allmaps C D \<inter> {m. Bex Hc ((\<subseteq>\<^sub>m) m)}) = (restrictH Hc C D)"
      unfolding restrictH_def by auto
  
    have fff: "\<forall>h\<in>H. h c1 \<in> {Some a0,Some a1}"
      using c1(4) Hdef Y unfolding mapify_def by auto 
  
    have y0: "\<And>h. dom h = C' \<Longrightarrow> Bex H ((\<subseteq>\<^sub>m) h)
                 \<longleftrightarrow> ( Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a0))) \<or> Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a1))))" 
      apply auto
      subgoal for h'
        by (metis fff fun_upd_triv insert_iff map_le_upd singletonD)
      subgoal for h h' apply(rule bexI[where x=h']) 
         apply (metis (full_types)   c1.hyps(2) domIff fun_upd_triv fun_upd_upd map_le_trans upd_None_map_le) by auto
      subgoal for h h' apply(rule bexI[where x=h']) 
         apply (metis (full_types)   c1.hyps(2) domIff fun_upd_triv fun_upd_upd map_le_trans upd_None_map_le) by auto
      done  
  
    have y1: "\<And>h. dom h = C' \<Longrightarrow> Bex ?H' ((\<subseteq>\<^sub>m) h)
                   \<longleftrightarrow> ( Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a0))) \<and> Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a1))))"
      apply auto
      subgoal for h h1 h2 unfolding map_le_def apply auto
        apply(cases "h1 c1 = Some a0") 
        subgoal apply(rule bexI[where x="h1"]) by simp
        subgoal apply(rule bexI[where x="h2"]) using fff apply auto by metis   
        done     
      subgoal for h h1 h2 unfolding map_le_def apply auto
        apply(cases "h1 c1 = Some a1") 
        subgoal apply(rule bexI[where x="h1"]) by simp
        subgoal apply(rule bexI[where x="h2"]) using fff apply auto by metis   
        done         
      subgoal for h h1 h2 apply(rule exI[where x="h1"])
        apply safe
         apply(rule bexI[where x=h2])
          apply safe
        subgoal by (metis \<open>a0 \<noteq> a1\<close> domI fun_upd_same map_le_def option.inject)  
        subgoal by (metis c1.hyps(2) domI domIff fun_upd_triv fun_upd_upd map_le_def map_le_trans upd_None_map_le)   
        subgoal by (metis (full_types) c1.hyps(2) domIff fun_upd_triv fun_upd_upd map_le_trans upd_None_map_le) 
        done
      done
  
  
    \<comment> \<open>We need to rewrite the cardinality of Hc some what...\<close>
    have "card (restrictH H (insert c1 C') Y) = sum (\<lambda>_.1) (restrictH H (insert c1 C') Y)"
      by(rule card_eq_sum)
    also
    have "\<dots> = sum (\<lambda>_.1) (allmaps (insert c1 C') Y \<inter> {m. Bex H ((\<subseteq>\<^sub>m) m)})"
      unfolding k by simp
    also
    have "\<dots> = sum (\<lambda>m. if m\<in>{m. Bex H ((\<subseteq>\<^sub>m) m)} then  1 else 0) (allmaps (insert c1 C') Y)" 
      apply(rule  sum.inter_restrict) apply (rule finitemaps) using c1  apply blast
      using cardY card_ge_0_finite by force
    also
    have "\<dots> = sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) m) then  1 else 0) (allmaps (insert c1 C') Y)" by simp
    also
    have "\<dots> = sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) m) then  1 else 0)
                        ((\<lambda>m. m(c1 \<mapsto> a0)) ` allmaps C' Y \<union> (\<lambda>m. m(c1 \<mapsto> a1)) ` allmaps C' Y)"
      unfolding allmaps_insertY by simp
    also
    have "\<dots> = sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) m) then  1::nat else 0) ((\<lambda>m. m(c1 \<mapsto> a0)) ` allmaps C' Y) 
                    + sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) m) then  1 else 0) ((\<lambda>m. m(c1 \<mapsto> a1)) ` allmaps C' Y)"
      apply(rule sum_union_inter) using disj by (auto intro!: finite_imageI intro: finitemaps)
    also
    have "\<dots> = sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) (m(c1 \<mapsto> a0))) then  1::nat else 0) (allmaps C' Y) 
                    + sum (\<lambda>m. if Bex H ((\<subseteq>\<^sub>m) ( m(c1 \<mapsto> a1))) then  1 else 0) (allmaps C' Y)" 
      by(subst sum.reindex, auto simp: c1.hyps(2) intro: upd_inj_on)+ 
    also
    have "\<dots> = sum (\<lambda>m. (if Bex H ((\<subseteq>\<^sub>m) (m(c1 \<mapsto> a0))) then  1::nat else 0)
                            + (if Bex H ((\<subseteq>\<^sub>m) (m(c1 \<mapsto> a1))) then  1::nat else 0)) (allmaps C' Y)"
      apply(subst sum.distrib) by simp
    also
    have "\<dots> = sum (\<lambda>h. (if Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a0))) \<or> Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a1))) then 1 else 0)
                       + (if Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a0))) \<and> Bex H ((\<subseteq>\<^sub>m) (h(c1 \<mapsto> a1))) then 1 else 0))
                             (allmaps C' Y)"
      by (auto intro: sum.cong)
    also
    \<comment> \<open>... until we now reach the heart of the argument ...\<close>
    have "\<dots> = sum (\<lambda>h. (if  Bex H ((\<subseteq>\<^sub>m) h) then 1 else 0)
                            + (if Bex ?H' ((\<subseteq>\<^sub>m) h) then 1 else 0)) (allmaps C' Y)"
    proof (rule sum.cong, goal_cases) 
      case (2 h)
      then have a: "dom h = C'" unfolding allmaps_def by auto 
      show ?case unfolding y0[OF a] y1[OF a] by simp
    qed simp
    \<comment> \<open>... now we package things together again...\<close>
    also have "\<dots> = sum (\<lambda>h. if Bex H ((\<subseteq>\<^sub>m) h) then 1 else 0) (allmaps C' Y) +
      sum (\<lambda>h. if Bex ?H' ((\<subseteq>\<^sub>m) h) then 1 else 0) (allmaps C' Y)"
      apply(subst sum.distrib) by simp
    also have "\<dots> = sum (\<lambda>x. if x \<in> {m. Bex H ((\<subseteq>\<^sub>m) m)} then 1 else 0) (allmaps C' Y) +
      sum (\<lambda>xa. if xa \<in> {m. Bex ?H' ((\<subseteq>\<^sub>m) m)} then 1 else 0) (allmaps C' Y)"
      by simp
    also have "\<dots> = sum (\<lambda>_.1) (restrictH H C' Y) + sum (\<lambda>_.1) (restrictH ?H' C' Y)"
      unfolding k[symmetric]
      apply(subst sum.inter_restrict) apply(simp add: finitemaps)
      apply(subst sum.inter_restrict) apply(simp add: finitemaps)
      by simp
    also have "\<dots> = card (restrictH H C' Y) + card (restrictH ?H' C' Y)"
      by auto 
    \<comment> \<open>... to obtain the desired equality.\<close>
    finally show  "card (restrictH H (insert c1 C') Y)
                  = card (restrictH H C' Y) + card (restrictH ?H' C' Y)" .
  qed
 

\<comment> \<open>Using the induction assumption (applied on Hc and F) we have that:\<close>


  have Y0: "card (restrictH H C' Y) \<le> card ({B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<notin> B})" 
  proof -
    have "card (restrictH H C' Y) \<le> card ({B. B\<subseteq>C' \<and> shatters H B Y})"
      using c1.hyps(3) a100 by auto
    also
    have "\<dots> = card {B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<notin> B}"
      apply(rule arg_cong[where f=card]) using c1.hyps(2) by blast
    finally show ?thesis .
  qed

\<comment> \<open>Combining @{thm s40} with the inductive assumption (now applied on H' and F) we obtain that\<close>

  have Y1: "card (restrictH ?H' C' Y) \<le> card {B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<in> B}"
  proof -   

    have bij3: "bij_betw (\<lambda>B. insert c1 B) {B. B\<subseteq>C' \<and> shatters ?H' (insert c1 B) Y} {B. B\<subseteq>(insert c1 C') \<and> shatters ?H' B Y \<and> c1 \<in> B}"
      apply(rule bij_betwI')
      using c1.hyps(2) apply fastforce
       apply blast 
    proof -
      fix b
      assume a1: "b\<in>{B. B\<subseteq>(insert c1 C') \<and> shatters ?H' B Y \<and> c1 \<in> B}"
      then have s1: "b\<subseteq>(insert c1 C')" "shatters ?H' b Y" "c1 \<in> b" by auto
      then obtain b' where "insert c1 b' = b" "c1\<notin>b'" by auto
      then have "b' \<subseteq> C'"
        using \<open>b \<subseteq> insert c1 C'\<close> by blast
      then have "b' \<in> {B. B\<subseteq>C' \<and> shatters ?H' (insert c1 B) Y}"
        using \<open>insert c1 b' = b\<close> s1(2) by blast
      then show "\<exists>xa\<in>{B. B \<subseteq> C' \<and> shatters ?H' (insert c1 B) Y}.  b = insert c1 xa"
        using \<open>insert c1 b' = b\<close> by blast
    qed 

    have sh': "\<forall>B. shatters ?H' B Y \<longrightarrow> shatters H B Y"
      using over_shatter by (metis (mono_tags, lifting) mem_Collect_eq subsetI)

    from `?H' \<subseteq> H_map`
    have "card (restrictH ?H' C' Y) \<le> card ({B. B\<subseteq>C' \<and> shatters ?H' B Y})" using c1.hyps(3) by auto
    also
    have "\<dots> \<le> card {B. B\<subseteq>C' \<and> shatters ?H' (insert c1 B) Y}"
      apply (rule card_mono) using s40 by (auto simp: c1.hyps(1))  
    also
    from bij3 have "\<dots> = card {B. B\<subseteq>(insert c1 C') \<and> shatters ?H' B Y \<and> c1 \<in> B}"
      by (simp add: bij_betw_same_card)
    also 
    have "\<dots> \<le> card {B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<in> B}"
      apply (rule card_mono) using sh'  by (auto simp: c1.hyps(1)) 
    finally show ?thesis .
  qed


\<comment> \<open>Overall, we have shown that\<close>
  from * Y0 Y1
  have "card (restrictH H (insert c1 C') Y) \<le> card ({B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<notin> B})
                                            + card ({B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<in> B})"
    by auto
  also
  have "\<dots> = card ({B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<notin> B} \<union> {B. B\<subseteq>(insert c1 C') \<and> shatters H B Y \<and> c1 \<in> B})"
    apply(subst card_Un_disjoint) by (auto simp: c1.hyps(1))
  also 
  have "\<dots> = card {B. B \<subseteq> insert c1 C' \<and> shatters H B Y}"
    apply(rule arg_cong[where f=card]) by auto
  finally
  show "card (restrictH H (insert c1 C') Y) \<le> card {B. B \<subseteq> insert c1 C' \<and> shatters H B Y}" .
\<comment> \<open>which concludes our proof.\<close>
qed 




lemma binomial_mono: "n\<le>m \<Longrightarrow> n choose k \<le> m choose k" 
proof(induction m)
  case 0
  then show ?case by auto
next
  case (Suc m)
  {
    fix n k
    have *: "Suc n choose k = (n choose k) + (if k = 0 then 0 else (n choose (k - 1)))"
    by (cases k) simp_all
  } note * = this
  from Suc show ?case using *
    by (metis add_leD1 diff_diff_cancel diff_is_0_eq le_SucE nat_le_linear) 
qed


lemma assumes "VCDim = Some d"
      and "C\<subseteq>X"
      and f3: "finite C"
      and "card C \<le> m"
    shows superaux: "card (restrictH H_map C Y) \<le> sum (\<lambda>x. m choose x) {0..d}"
proof -
 have "\<forall>B\<subseteq>C. shatters H_map B Y \<longrightarrow> card B \<le> d" using assms noshatter
    by (meson \<open>C \<subseteq> X\<close> not_le_imp_less order_trans)
  then have f2: "{B. B\<subseteq>C \<and> shatters H_map B Y} \<subseteq> {B. B\<subseteq>C \<and> card B \<le> d}" by auto
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
    moreover have "card {B. B \<subseteq> C \<and> card B = Suc d} \<le> m choose Suc d" using assms(4) binomial_mono f3
      by (simp add: n_subsets)
    ultimately show ?case using Suc.IH by auto
  qed
  from this f2 have "card {B. B\<subseteq>C \<and> shatters H_map B Y} \<le> sum (\<lambda>x. m choose x) {0..d}"
    by (metis (no_types, lifting) card_mono f1 order_trans)
  then show "card (restrictH H_map C Y) \<le> sum (\<lambda>x. m choose x) {0..d}" using eq63 f3
    by (meson le_trans subsetI) 
qed

(*Sauers Lemma 6.10*)
lemma assumes "VCDim = Some d"
      and "m>0"
  shows lem610: "growth m \<le> sum (\<lambda>x. m choose x) {0..d}" 
 (* using n_subsets growth_def eq63 noshatter *)
proof -
  have "\<forall>n \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}. n \<le> sum (\<lambda>x. m choose x) {0..d}"
    using superaux assms(1,2) card_gt_0_iff by blast
  then have "finite {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"
    using finite_nat_set_iff_bounded_le by auto
  moreover have "{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
  ultimately have "growth m \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"
    using Max_in growth_def by auto
  then show ?thesis
    using \<open>\<forall>n\<in>{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}. n \<le> sum ((choose) m) {0..d}\<close> by blast
qed

section "Using the VCDim"

lemma growthgtone: "VCDim = Some d \<Longrightarrow> m \<ge> 1 \<Longrightarrow> growth m \<ge> 1"
proof -
  assume a1: "m \<ge> 1" "VCDim = Some d"
  then have "\<forall>n \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}. n \<le> sum (\<lambda>x. m choose x) {0..d}" using superaux card_gt_0_iff
    by (smt binomial_eq_0_iff card_infinite choose_one le_eq_less_or_eq mem_Collect_eq not_less) 
  then have f2: "finite {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"
    using finite_nat_set_iff_bounded_le by auto
  obtain C where f1: "card C = m" "C\<subseteq>X" "finite C" using infx infinite_arbitrarily_large by blast
  obtain h where f3: "h\<in>H_map" using nnH by auto
  have "ran (\<lambda>x. (if x\<in>C then h x else None)) \<subseteq> Y" using f3 ranh
    by (smt Collect_mono option.simps(3) ran_def subset_eq)
  moreover have "dom (\<lambda>x. (if x\<in>C then h x else None)) = C" using f3 domh
    by (smt Collect_cong Collect_mem_eq UNIV_I domIff)
  ultimately have "(\<lambda>x. (if x\<in>C then h x else None)) \<in> restrictH H_map C Y"
    using restrictH_def allmaps_def f1 f3 
    by (smt a1(1) card.empty map_le_def mem_Collect_eq of_nat_0 real_of_nat_ge_one_iff)
  then have "restrictH H_map C Y \<noteq> {}" by auto
  moreover have "finite (restrictH H_map C Y)" using cardY finiteres f1(3)
    by (metis card_infinite less_irrefl nat_zero_less_power_iff zero_power2)
  ultimately have "(card (restrictH H_map C Y)) \<ge> 1"
    by (meson card_0_eq less_one not_le)
  moreover have "(card (restrictH H_map C Y))\<in>{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}" using f1 by auto
  ultimately show "growth m \<ge> 1" using growth_def f2
    by (metis (no_types, lifting) Max_ge choose_one leD neq0_conv zero_less_binomial_iff) 
qed


(*Theorem 6.11*)
lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
  sorry



lemma ceil_gr: "y \<ge> ceiling x \<Longrightarrow> real y \<ge> x"
  by linarith


lemma ln_le_sqrt: "m\<ge>1 \<Longrightarrow> ln m \<le> 2 * sqrt(m)"
  by (metis divide_le_eq linorder_not_less ln_bound ln_sqrt mult.commute not_one_le_zero order.trans real_sqrt_gt_zero zero_less_numeral)


lemma sqrt_le_m: "m\<ge>1 \<Longrightarrow> sqrt(m) \<le> m"
proof -
  have "m\<ge>1 \<Longrightarrow> sqrt(m) \<le> sqrt m * sqrt m"
    by (smt real_mult_le_cancel_iff1 real_sqrt_ge_one semiring_normalization_rules(3)
        semiring_normalization_rules(8))
  also have "m\<ge>1 \<Longrightarrow> sqrt(m)* sqrt(m) \<le> m" by simp
  finally show "m\<ge>1 \<Longrightarrow> sqrt(m) \<le> m" by simp
qed



lemma aux124: "m\<ge>d \<Longrightarrow> 1 < d \<Longrightarrow> sum (\<lambda>x. m choose x) {0..d} \<le> m^d"
proof(induction d)
  case 0
  then show ?case by auto
next
  case c1: (Suc d)
  then show ?case
  proof(cases "1<d")
    case True
    then have s1: "sum ((choose) m) {0..d} \<le> m ^ d" using c1 by auto
    have s2: "sum ((choose) m) {0..Suc d} = sum ((choose) m) {0..d} + real (m choose Suc d)" by auto
    have "(m choose Suc d) = (m choose d)* real (m-d)/(Suc d)"
      by (metis Groups.mult_ac(2) binomial_absorb_comp binomial_absorption 
          nat.simps(3) nonzero_mult_div_cancel_left of_nat_eq_0_iff of_nat_mult)
    moreover have "(m-d)/(Suc d) \<le> (m-1)" using frac_le[of "m-d" "m-1" 1 "Suc d"]
      using True by auto
    moreover have "(m choose d) \<le>  m^d"
      using binomial_le_pow c1.prems(1) by auto
    ultimately have "real (m choose Suc d) \<le> (m-1) *  m^d" 
      using mult_mono[of "real (m - d) / real (Suc d)" "real (m - 1)" 
           "real (m choose d)" "real m ^ d"] by (simp add: mult.commute) 
    then have "sum ((choose) m) {0..Suc d} \<le> m^d + (m-1)*m^d" using s1 s2
      by linarith 
    then show ?thesis
      using Suc_le_eq c1.prems(1) mult_eq_if by auto 
  next
    case False
    from this c1(3) have d1: "d = 1" by auto
    have m2: "2 \<le> m" using c1(2) d1 by auto
    from d1 have "sum ((choose) m) {0..Suc d} = (m choose 0) + (m choose 1) + (m choose 2)"
      by (simp add: numeral_2_eq_2)
    also have "... = 1 + m + real (m choose 2)" using choose_one binomial_n_0 by auto
    also have "m choose 2 = m*(m-1)/ 2"
      by (metis (no_types, hide_lams) Suc_1 binomial_absorption choose_one
          nonzero_mult_div_cancel_left of_nat_mult of_nat_numeral zero_neq_numeral) 
    also have "real (1 + m) + real (m * (m - 1)) / 2 = 1 + 2*m/2 + (m-1)*m/2" by auto
    finally have s1: "sum ((choose) m) {0..Suc d} = 1 +  (m+1)*m/2"
      using mult_eq_if by auto
    have "1 + (m+1) \<le> 2*m" using m2
      apply (induction m rule: nat_induct_at_least)
      by auto
    then have "1/2 + (m+1)/2 \<le> m"
      by (simp add: add_divide_distrib)
    moreover have "1/m \<le> 1/2" using m2 by auto
    ultimately have "1/m + (m+1)/2 \<le> m" by auto
    then have "(1/m + (m+1)/2)*m \<le> real m * real m" using real_mult_le_cancel_iff1 m2 by auto
    then have "1/m * real m + (m+1)/2 * real m \<le> real m * real m"
      by (simp add: distrib_left mult.commute)
    then have "1 +  (m+1)*m/2 \<le> real m * real m"
      by (metis add_is_0 m2 nat_le_iff_add nonzero_mult_div_cancel_right of_nat_eq_0_iff
          of_nat_mult one_add_one one_neq_zero times_divide_eq_left) 
    then have "1 + (m+1)*m/2 \<le> m^2"
      by (simp add: power2_eq_square)
    then show ?thesis using s1 d1
      by (metis Suc_1 of_nat_le_iff) 
  qed
qed
  



lemma aux123: "m\<ge>d \<Longrightarrow> sum (\<lambda>x. m choose x) {0..d} \<le> (d+1)*m^d"
   using sum_bounded_above[of "{0..d}" "(\<lambda>x. m choose x)" "m^d"]
   by (smt One_nat_def add.right_neutral add_Suc_right atLeastAtMost_iff binomial_le_pow binomial_n_0 card_atLeastAtMost diff_zero
       le_antisym le_neq_implies_less le_trans less_one nat_le_linear nat_zero_less_power_iff neq0_conv of_nat_id power_increasing_iff)

lemma assumes "C\<subseteq>X" "1<d" "VCDim = Some d" "d \<le> m" "card C \<le> m" "finite C"
  shows resforboost: "card ((\<lambda>h. h |` C) ` H_map) \<le> m^d"
  using restrictH_map_conv[of C] aux124[of d] superaux[of d C m] assms by fastforce


  lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
      and "\<epsilon> > 0"
      and "m \<ge> M \<epsilon> \<delta>"
      and "M = (\<lambda>\<epsilon> \<delta>. nat( ceiling (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)))"
      and "VCDim = Some d"
    shows aux456: "h\<in>H \<Longrightarrow> abs(PredErr D h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(real(2*m)))
      \<Longrightarrow> abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>"
  proof -
    fix S h
    assume a10: "h\<in>H" "abs(PredErr D h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))"
    have f1: "m \<ge> (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)"
      using assms(4,5) ceil_gr by auto
    then have a2: "2*m \<ge> d"
      by (smt divide_nonneg_nonneg less_imp_le_nat mult_2 nat_less_real_le of_nat_0_le_iff of_nat_add zero_le_power2) 
    from f1 have a1: "2*m > 1"
      by (smt divide_nonneg_nonneg le_add2 le_neq_implies_less less_1_mult mult.right_neutral numeral_eq_one_iff
          of_nat_0_le_iff one_add_one real_of_nat_ge_one_iff semiring_norm(85) zero_le_power2) 

    from aux123 lem610 a2 a1 assms(6) have f2: "growth (2*m) \<le> (d+1)*(2*m)^d"
      by (smt le_trans less_imp_le_nat of_nat_0_less_iff real_of_nat_ge_one_iff) 

    have a12: "growth (2*m) \<ge> 1" using growthgtone assms(6) a1 by auto
    have ad: "\<delta>>0" using assms(2) by auto

    have "(4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))
            = 4/(\<delta> * sqrt(2*m)) +sqrt(ln(real(growth (2*m))))/(\<delta> * sqrt(2*m))"
      by (simp add: add_divide_distrib)
    moreover have "sqrt(ln(real(growth (2*m))))/(\<delta> * sqrt(2*m)) \<le> \<epsilon>/2"
    proof(cases "d > 0")
      case c1: True
      from a12 have "growth (2*m) > 0" by auto
      then have "ln(growth (2*m)) \<le> ln((d+1)*(2*m)^d)" using f2
        by (smt le_eq_less_or_eq ln_le_cancel_iff nat_less_real_le of_nat_0)
      also have "ln ((d+1)*(2*m)^d) = ln (d+1) + d * ln(2*m)" using a1 ln_mult
        by (smt add_pos_pos c1 less_imp_le_nat ln_realpow of_nat_0_less_iff of_nat_mult
            of_nat_power real_of_nat_ge_one_iff zero_less_one zero_less_power)
      also have "(ln(d+1)+d*ln(2*m)) \<le> (ln(d+1)+d*2* sqrt(2*m))"
        using ln_le_sqrt a1(1) c1 by auto 
      finally have f12: "(ln(growth (2*m)))/(2*m) \<le> (ln(d+1)+d*2* sqrt(2*m))/(2*m)"
        by (simp add: divide_right_mono)
      also have "... = (ln(d+1))/(2*m) + d*2* sqrt(2*m)/(2*m)"
        using add_divide_distrib by blast
      also have "... \<le> (ln(d+1))/sqrt(2*m) + d*2* sqrt(2*m)/(2*m)" using sqrt_le_m
        by (smt a1(1) frac_le le_add2 less_imp_le_nat ln_eq_zero_iff ln_gt_zero_iff
            real_of_nat_ge_one_iff real_sqrt_gt_0_iff) 
      also have "... = (ln(d+1))/sqrt(2*m) + d*2/sqrt(2*m)"
        by (metis divide_divide_eq_right of_nat_0_le_iff real_div_sqrt)
      also have "... = (ln(d+1)+d*2)/sqrt(2*m)"
        by (simp add: add_divide_distrib)
      finally have "sqrt((ln(growth (2*m)))/(2*m)) \<le> sqrt((ln(d+1)+d*2)/sqrt(2*m))"
        using real_sqrt_le_iff by blast
      moreover have "sqrt(ln(real(growth (2*m))))/(\<delta> * sqrt(2*m))
                  = (sqrt(ln(real(growth (2*m))))/sqrt(2*m))/\<delta>" by simp
      moreover have "(sqrt(ln(real(growth (2*m))))/sqrt(2*m))
                    = sqrt((ln(growth (2*m)))/(2*m))"
        by (simp add: real_sqrt_divide)
      ultimately have f20: "sqrt(ln(real(growth (2*m))))/(\<delta> * sqrt(2*m))
             \<le>sqrt((ln(d+1)+d*2)/sqrt(2*m))/\<delta>" using assms(4) ad
        by (smt divide_right_mono)
     from f1 have "m > ((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2"
      by (smt divide_nonneg_nonneg of_nat_0_le_iff zero_le_power2)
     then have "2*m > ((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2" by auto
     then have "sqrt(2*m) > ((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)"
       using real_less_rsqrt by blast
     moreover have "((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2) > 0" using assms(3) ad c1
       by (smt ln_gt_zero_iff nat_0_less_mult_iff nat_less_real_le nonzero_mult_div_cancel_right
           of_nat_0 of_nat_1 of_nat_add zero_less_divide_iff zero_less_numeral zero_less_power2)
     ultimately have "1/(sqrt(2*m)) \<le> 1/((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)"
       using frac_le[of 1 1 "((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)" "sqrt(2*m)"] by auto
     moreover have "... = ((\<epsilon>*\<delta>/2)^2)/(ln(d+1)+d*2)"
       by simp
     moreover have "(ln(d+1)+d*2) > 0" using c1
       by (simp add: add_pos_pos)
     ultimately have "(ln(d+1)+d*2)/(sqrt(2*m))\<le>(\<epsilon>*\<delta>/2)^2"
       using divide_le_cancel by fastforce
     then have "sqrt((ln(d+1)+d*2)/(sqrt(2*m)))\<le>(\<epsilon>*\<delta>/2)"
       by (smt ad assms(3) mult_sign_intros(5) real_le_lsqrt
           real_sqrt_ge_0_iff zero_less_divide_iff)
     then have "sqrt((ln(d+1)+d*2)/(sqrt(2*m)))\<le>(\<epsilon>/2)*\<delta>" by simp
     then have "sqrt((ln(d+1)+d*2)/(sqrt(2*m)))/\<delta> \<le> \<epsilon>/2" using ad pos_divide_le_eq by blast
     from this f20 show ?thesis
       by linarith
    next
      case False
      then have "d=0" by auto
      then have "growth(2*m) = 1" using a12 f2
        by (simp add: \<open>d = 0\<close>) 
      then show ?thesis using assms(3)
        by auto 
    qed
    moreover have "4/(\<delta>* sqrt(2*m)) \<le> \<epsilon>/2"
    proof -
     from f1 have "m \<ge> (4/(\<epsilon>*\<delta>/2))^2/2"
       by (smt divide_nonneg_nonneg of_nat_0_le_iff zero_le_power2)
     then have "2*m > (4/(\<epsilon>*\<delta>/2))^2"
       by (smt add_gr_0 f1 field_sum_of_halves less_imp_of_nat_less mult_2 of_nat_1
           of_nat_add zero_le_power2 zero_less_one) 
     then have "sqrt(2*m) > 4/(\<epsilon>*\<delta>/2)"
       using real_less_rsqrt by blast
     then have "1/sqrt(2*m) \<le> 1/(4/(\<epsilon>*\<delta>/2))" using assms(3) ad frac_le
       by (smt mult_pos_pos zero_less_divide_iff)
     then have "1/sqrt(2*m) \<le> (\<epsilon>*\<delta>/2)/4" by simp
     then have "4/sqrt(2*m) \<le> (\<epsilon>*\<delta>/2)" by linarith
     then have "4/sqrt(2*m) \<le> (\<epsilon>/2)*\<delta>" by simp
     then have "4/sqrt(2*m)/\<delta> \<le> \<epsilon>/2" using ad pos_divide_le_eq by blast
     then show ?thesis
       by (simp add: divide_divide_eq_left mult.commute)
    qed
    ultimately have "(4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m)) \<le> \<epsilon>" by auto
    from this a10 show "abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>" by auto
  qed



lemma assumes "set_pmf D \<subseteq> (X\<times>Y)"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
      and "\<epsilon> > 0"
      and "m \<ge> M \<epsilon> \<delta>"
      and "M = (\<lambda>\<epsilon> \<delta>. nat (ceiling (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)))"
      and "VCDim = Some d"
    shows aux200: "measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D} \<ge> 1 - \<delta>"
proof -
  have "\<forall>h S. h\<in>H \<longrightarrow> abs(PredErr D h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(real(2*m)))
      \<longrightarrow> abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>" using assms aux456 by auto
  then have "{S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))}
     \<subseteq>{S. (\<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h) \<le> \<epsilon>)}" by auto
  moreover have "measure_pmf.prob (Samples m D) {S. \<forall>h\<in>H. abs(PredErr D h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
    using assms theorem611 by auto
  ultimately show ?thesis using subsetlesspmf representative_def
    by (smt Collect_cong) 
qed


lemma assumes "VCDim = Some d"
  shows uni_conv: "uniform_convergence"
proof -
  obtain M where "M = (\<lambda>\<epsilon> \<delta>. nat \<lceil>((ln (real (d + 1)) + real (d * 2)) / (\<epsilon> * \<delta> / 2)\<^sup>2)\<^sup>2 / 2 + (4 / (\<epsilon> * \<delta> / 2))\<^sup>2 / 2
             + 1 + real d\<rceil>)" by auto
  from this have "(\<forall>D. set_pmf D \<subseteq> (X\<times>Y) \<longrightarrow>
               (\<forall>(m::nat) \<epsilon>. 0 < \<epsilon> \<longrightarrow>
                      (\<forall>(\<delta>::real)\<in>{x. 0 < x \<and> x < 1}.
                          M \<epsilon> \<delta> \<le> m \<longrightarrow>
                          1 - \<delta> \<le> measure_pmf.prob (Samples m D) {S. representative S m \<epsilon> D})))"
    using aux200 assms by auto
  then show ?thesis using uniform_convergence_def by auto
qed


end
end