theory VCDim
  imports Complex_Main LearningTheory RpowD
begin
  
lemma card_2_explicit: "a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> a\<noteq>b \<Longrightarrow> card A = 2 \<Longrightarrow> A = {a,b}"
  by (smt One_nat_def Suc_inject card.remove card_1_singletonE card_infinite doubleton_eq_iff
      insert_Diff_single insert_absorb2 mk_disjoint_insert numeral_2_eq_2 zero_neq_numeral)


definition "mapify f = (\<lambda>x. Some (f x))" (*This should exist somewhere*)
(*definition "allmaps C D = (if C = {} then {} else {m. dom m = C \<and> ran m \<subseteq> D})"  *)  
definition "allmaps C D = {m. dom m = C \<and> ran m \<subseteq> D}"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"




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
proof -
  have "dom (m(x \<mapsto> d)) = (insert x F)"
    by (metis (mono_tags, lifting) allmaps_def assms(1) dom_fun_upd mem_Collect_eq option.simps(3))
  moreover have "ran (m(x \<mapsto> d)) \<subseteq> D"
  proof(rule ccontr)
    assume "\<not> ran (m(x \<mapsto> d)) \<subseteq> D"
    then obtain z where o1: "z \<in> ran (m(x \<mapsto> d))" "z\<notin>D" by auto
    then obtain y where o2: "(m(x \<mapsto> d)) y = Some z" by (auto simp: ran_def)
    then have "x\<noteq>y" using assms(2) o1 by auto
    moreover have "ran m \<subseteq> D"
    using allmaps_def assms(1) by fastforce
    ultimately show False
      using o2 ranI o1(2) by fastforce
  qed
  ultimately show ?thesis
    by (simp add: allmaps_def)
qed

lemma "(\<forall>x\<in>A. \<forall>y\<in>A. x\<noteq>y \<longrightarrow> f x \<noteq> f y) \<Longrightarrow> inj_on f A"
  using inj_on_def by blast

lemma "bij_betw f A B \<Longrightarrow> bij_betw f A' B' \<Longrightarrow> A = A' \<Longrightarrow> B = B'" 
   by (simp add: bij_betw_def) 

lemma assumes  "x\<notin>F" "m_1\<in>allmaps F D" "m_2\<in>allmaps F D" "m_1(x \<mapsto> d_1) = m_2(x \<mapsto> d_2)"
  shows aux392: "m_1 = m_2"
    by (metis (mono_tags, lifting) allmaps_def assms domIff fun_upd_triv fun_upd_upd mem_Collect_eq) 
 

lemma assumes "x\<notin>F"
  shows bij_allmaps: "bij_betw (\<lambda>(m,d). m(x:=Some d)) ((allmaps F D) \<times> D) (allmaps (insert x F) D)"
  apply(rule bij_betw_imageI)
   apply(simp add: inj_on_def)
  apply (meson assms aux392 map_upd_eqD1)
  apply rule
  using upd_in_all apply fastforce
proof
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
  moreover have "(\<lambda>(m, d). m(x \<mapsto> d)) (?n,d) = m" using o1 by auto
  ultimately show "m \<in> (\<lambda>(m, d). m(x \<mapsto> d)) ` (allmaps F D \<times> D)"
    using \<open>m(x := None) \<in> allmaps F D\<close> image_iff by fastforce
qed


lemma assumes "finite D"
    shows "finite C \<Longrightarrow> card (allmaps C D) = (card D) ^ (card C)"
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



locale vcd =learning_basics where X=X and Y=Y and H=H
  for X::"'a set" and Y::"'b set" and H :: "('a \<Rightarrow> 'b) set" +
assumes infx: "infinite X"
begin

lemma "X \<noteq> {}" using infx by auto

abbreviation "H_map \<equiv> image mapify H"

lemma ranh: "\<forall>h\<in>H_map. ran h \<subseteq> Y" using Hdef mapify_def
  by (smt imageE mem_Collect_eq option.simps(1) ran_def subset_iff)

lemma domh: "\<forall>h\<in>H_map. dom h = UNIV"
  by (simp add: mapify_def) 

lemma nnHmap: "H_map \<noteq> {}" using nnH by auto

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


definition "VCDim = (if finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} then Some (Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}) else None)"

definition "growth m = Max {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"

lemma "{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)



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

lemma "\<exists>f. bij_betw f Y {True, False}"
proof -
  obtain y1 where "y1 \<in> Y" using cardY by fastforce
  obtain y2 where "y2 \<in> Y" "y2 \<noteq> y1" using cardY
    by (metis card_2_exists)
  then obtain f where "f y1 = True" "f y2 = False" by auto
  have "bij_betw f Y {True, False}"
    apply (rule bij_betwI')
    apply (metis \<open>f y1 = True\<close> \<open>f y2 = False\<close> \<open>y1 \<in> Y\<close> \<open>y2 \<in> Y\<close> cardY card_2_exists)
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


lemma over_shatter: "H1\<subseteq>H2 \<Longrightarrow> shatters H1 C D \<Longrightarrow> shatters H2 C D"
  by (meson alt_shatters subsetCE)

(*Equation 6.3*)
lemma eq63: "finite C \<Longrightarrow> \<forall>H'\<subseteq>H_map. card (restrictH H' C Y) \<le> card ({B. B\<subseteq>C \<and> shatters H' B Y})"
proof (induct rule: finite_induct)
  case empty
  show ?case
  proof(safe)
    fix H'
    assume a1: "H'\<subseteq>H_map"
  obtain f::"('a \<Rightarrow> 'b option)" where "dom f = {}" by simp
  then have "allmaps {} Y = {f}" using allmaps_e by auto
  then have "H'\<noteq>{} \<longrightarrow> card (restrictH H' {} Y) = 1" using empty_shatted shatters_def
      is_singletonI is_singleton_altdef a1 by metis    
  moreover have "H'\<noteq>{} \<longrightarrow> {B. B\<subseteq>{} \<and> shatters H' B Y} = {{}}" using empty_shatted a1 by blast 
  ultimately show "card (restrictH H' {} Y) \<le> card {B. B \<subseteq> {} \<and> shatters H' B Y}"
    apply (cases "H' = {}")
    by (auto simp: restrictH_def)
qed
next
  case c1: (insert x F)
  show ?case
    apply rule
  proof
  fix Hc
  assume a100: "Hc\<subseteq>H_map"
  let ?H' = "{h\<in>Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)}"


(*  have "\<forall>B\<subseteq>F. bij_betw (\<lambda>(m,d). m(x:=Some d)) ((restrictH ?H' B Y) \<times> Y) (restrictH ?H' (insert x B) Y)"
  let ?H'' = "{h\<in>Hc. \<exists>B\<subseteq>F. bij_betw (\<lambda>(m,d). m(x:=Some d)) ((restrictH Hc B Y) \<times> Y) (restrictH Hc (insert x B) Y)}"
  let ?H' = "{h\<in>Hc. ((\<lambda>d. h(x:=Some d)) ` Y) \<subseteq> Hc}" *)
  let ?Ha = "Hc - ?H'"
  have "?Ha = {h\<in>Hc. \<forall>h'\<in>Hc. (\<forall>a\<in>F. h' a = h a) \<longrightarrow> h' x =  h x}" by auto
  then have s1: "\<forall>h\<in>?Ha. \<forall>h'\<in>?Ha. (\<forall>a\<in>F. h' a = h a) \<longrightarrow> h' x =  h x" by auto
  have s10: "bij_betw (\<lambda>m. m(x:=None)) (restrictH ?Ha (insert x F) Y) (restrictH ?Ha F Y)"
    apply(rule bij_betwI')
  proof -
    fix m1 m2
    assume a1: "m1\<in>(restrictH ?Ha (insert x F) Y)" "m2\<in>(restrictH ?Ha (insert x F) Y)"
    then obtain h1 where o1: "h1\<in>?Ha" "m1 \<subseteq>\<^sub>m h1" using restrictH_def by blast
    obtain h2 where o2: "h2\<in>?Ha" "m2 \<subseteq>\<^sub>m h2" using restrictH_def a1 by blast
    show "(m1(x := None) = m2(x := None)) = (m1 = m2)"
    proof
    assume a2: "m1(x := None) = m2(x := None)"
    then have "(\<forall>a\<in>F. h1 a = h2 a)"
    proof -
      { fix aa :: 'a
        have "\<forall>a. m2 a \<noteq> None \<or> a \<notin> insert x F"
          by (meson a1(2) hx_none)
        then have "aa \<notin> F \<or> h1 aa = h2 aa"
          by (metis (no_types) \<open>m1 \<subseteq>\<^sub>m h1\<close> \<open>m1(x := None) = m2(x := None)\<close> \<open>m2 \<subseteq>\<^sub>m h2\<close> c1(2) contra_subsetD domIff fun_upd_apply map_le_def subset_insertI) }
      then show ?thesis
        by blast
    qed
    then have "h1 x = h2 x" using s1 o1(1) o2(1) by blast
    then have "m1 x = m2 x"
      by (metis (no_types, lifting) a1(1) a1(2) domIff hx_none insertI1 map_le_def o1(2) o2(2)) 
    then show "m1 = m2" using a2
      by (metis fun_upd_triv fun_upd_upd)
  next
    show "m1 = m2 \<Longrightarrow> m1(x := None) = m2(x := None)"
      by simp
  qed
next
  fix m1
  assume a1: "m1\<in>(restrictH ?Ha (insert x F) Y)"
  then have s1: "dom (m1(x := None)) = F"
    by (simp add: allmaps_def c1.hyps(2) restrictH_def)
  have "ran m1 \<subseteq> Y" using a1
    by (simp add: allmaps_def restrictH_def)
  then have "ran (m1(x := None)) \<subseteq> Y"
    by (metis ranI ran_restrictD restrict_complement_singleton_eq subset_eq) 
  then have s2: "(m1(x := None))\<in>allmaps F Y" using s1 by (simp add: allmaps_def)
  obtain h1 where o1: "h1\<in>?Ha" "m1 \<subseteq>\<^sub>m h1" using restrictH_def a1 by blast
  then have "(m1(x := None)) \<subseteq>\<^sub>m h1"
    by (meson map_le_trans upd_None_map_le)
  then show "(m1(x := None))\<in>(restrictH ?Ha F Y)"
    by (metis (mono_tags, lifting) mem_Collect_eq o1(1) restrictH_def s2)
next
  fix m2
  assume a1: "m2\<in>(restrictH ?Ha F Y)"
  obtain h2 where o1: "h2\<in>?Ha" "m2 \<subseteq>\<^sub>m h2" using restrictH_def a1 by blast
  let ?m1 = "m2(x := h2 x)"
  have "?m1 \<subseteq>\<^sub>m h2"
    by (metis fun_upd_triv map_le_upd o1(2))
  have "?m1 \<in> allmaps (insert x F) Y"
  proof -
    have "h2 x \<noteq> None"
      by (metis (no_types, lifting) DiffE UNIV_I \<open>Hc \<subseteq> H_map\<close> domIff domh o1(1) subsetCE)
    then have "dom ?m1 = insert x F" using a1 
      by (simp add: \<open>h2 x \<noteq> None\<close> allmaps_def restrictH_def)
    obtain y1 where "h2 x = Some y1" "y1\<in>Y"
      by (metis (no_types, lifting) DiffE \<open>Hc \<subseteq> H_map\<close> \<open>h2 x \<noteq> None\<close> domD domIff o1(1) ranI ranh subsetCE) 
    (*have "ran h2 \<subseteq> Y"
      by (meson DiffE \<open>Hc \<subseteq> H_map\<close> o1(1) ranh subsetCE)
    then have "h2 x \<in> Some ` Y"
      using \<open>h2 x \<noteq> None\<close> ranI by fastforce *)
    moreover have "ran m2 \<subseteq> Y" using o1
      by (metis (mono_tags, lifting) a1 allmaps_def mem_Collect_eq restrictH_def)
    ultimately have "ran ?m1 \<subseteq> Y"
      by (metis (full_types) contra_subsetD domIff fun_upd_triv insertE map_le_def o1(2) ran_map_upd subsetI) 
    then show ?thesis
      using \<open>dom (m2(x := h2 x)) = insert x F\<close> allmaps_def by blast 
  qed
  then have "?m1 \<in> (restrictH ?Ha (insert x F) Y)"
    by (metis (mono_tags, lifting) \<open>m2(x := h2 x) \<subseteq>\<^sub>m h2\<close> mem_Collect_eq o1(1) restrictH_def)
  then show "\<exists>xa\<in>(restrictH ?Ha (insert x F) Y). m2 = xa(x := None)"
    by (metis (mono_tags, lifting) a1 allmaps_def c1.hyps(2) domIff fun_upd_triv fun_upd_upd mem_Collect_eq restrictH_def) 
qed

  have "bij_betw (\<lambda>(m, y). m(x:=Some y)) (restrictH ?H' F Y \<times> Y) (restrictH ?H' (insert x F) Y)"
    apply(rule bij_betwI')
  proof -
      have "\<And>m1 m2 y1 y2. (m1, y1) \<in> restrictH ?H' F Y \<times> Y \<Longrightarrow> (m2, y2) \<in> restrictH ?H' F Y \<times> Y
            \<Longrightarrow> (m1(x \<mapsto> y1) = m2(x \<mapsto> y2)) = ((m1,y1) = (m2,y2))"
      proof -
        fix m1 m2 y1 y2
        assume a1: "(m1, y1) \<in> restrictH ?H' F Y \<times> Y" "(m2, y2) \<in> restrictH ?H' F Y \<times> Y"
        have "m1 \<in> allmaps F Y"
          using a1(1) restrictH_def by fastforce 
        then have "m1 x = None"
          using allmaps_def c1.hyps(2) by fastforce 
        have "m2 \<in> allmaps F Y"
          using a1(2) restrictH_def by fastforce 
        then have "m2 x = None"
          using allmaps_def c1.hyps(2) by fastforce
        show "(m1(x \<mapsto> y1) = m2(x \<mapsto> y2)) = ((m1,y1) = (m2,y2))"
        proof
          assume a2: "m1(x \<mapsto> y1) = m2(x \<mapsto> y2)"
          then have "m1 = m2"
            by (meson \<open>m1 \<in> allmaps F Y\<close> \<open>m2 \<in> allmaps F Y\<close> aux392 c1.hyps(2))
          then show "((m1,y1) = (m2,y2))"
            using a2 map_upd_eqD1 by fastforce
        next
          assume "(m1, y1) = (m2, y2)"
          then show "m1(x \<mapsto> y1) = m2(x \<mapsto> y2)"
            by blast
        qed
      qed
    then show "\<And>xa y.
       xa \<in> restrictH {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)} F Y \<times> Y \<Longrightarrow>
       y \<in> restrictH {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)} F Y \<times> Y \<Longrightarrow>
       ((case xa of (m, y) \<Rightarrow> m(x \<mapsto> y)) = (case y of (m, y) \<Rightarrow> m(x \<mapsto> y))) = (xa = y)"
      by auto
  next
    have "\<And>m1 y1. (m1, y1) \<in> restrictH ?H' F Y \<times> Y \<Longrightarrow> m1(x \<mapsto> y1) \<in> (restrictH ?H' (insert x F) Y)"
    proof -
     fix m1 y1
     assume a1: "(m1, y1) \<in> restrictH ?H' F Y \<times> Y"
     let ?m2 = "m1(x \<mapsto> y1)"
     have "m1 \<in> allmaps F Y"
       using a1 restrictH_def by fastforce
     then have "?m2 \<in> allmaps (insert x F) Y" using allmaps_def a1 upd_in_all by fastforce
     obtain h1 where o1:"h1\<in>?H'" "m1 \<subseteq>\<^sub>m h1" using restrictH_def a1 by blast
     then obtain h2 where o2: "h2 x \<noteq> h1 x \<and> (\<forall>a\<in>F. h2 a = h1 a)" "h2\<in>Hc" by blast
     then have "h2\<in>?H'" using o1 by force
     have "m1 \<subseteq>\<^sub>m h2"
       by (metis (mono_tags, lifting) \<open>m1 \<in> allmaps F Y\<close> allmaps_def map_le_def mem_Collect_eq o1(2) o2(1)) 
     have "h1\<in>Hc"
       using o1(1) by blast
     then have "h1\<in>H_map" using \<open>Hc \<subseteq> H_map\<close> by blast
     have "h2\<in>H_map" using \<open>Hc \<subseteq> H_map\<close> o2(2) by blast
     have "Some ` Y = {h1 x, h2 x}"
     proof -
       have "ran h1 \<subseteq> Y"
         using \<open>Hc \<subseteq> H_map\<close> \<open>h1 \<in> Hc\<close> ranh by blast 
       then have "h1 x \<in> Some ` Y"
         by (metis UNIV_I \<open>h1 \<in> H_map\<close> contra_subsetD domD domh imageI ranI)
       moreover have "h2 x \<in> Some ` Y"
         by (metis (mono_tags, hide_lams) Hdef \<open>h2 \<in> H_map\<close> image_iff mapify_def)
       ultimately show ?thesis using card_2_explicit o2(1)
         by (metis card_some_y)
     qed
     have "h1 x = Some y1 \<or> h2 x = Some y1"
       by (metis (no_types, lifting) Hdef SigmaD2 \<open>Some ` Y = {h1 x, h2 x}\<close> a1 cardY card_2_explicit
           imageE image_def image_iff insertE insertI1 mapify_def mem_Collect_eq o2(2) singletonD) 
     show "?m2 \<in> (restrictH ?H' (insert x F) Y)"
     proof (cases "h1 x = Some y1")
       case True
       then show ?thesis
         by (metis (mono_tags, lifting) \<open>m1(x \<mapsto> y1) \<in> allmaps (insert x F) Y\<close> fun_upd_triv
             map_le_upd mem_Collect_eq o1(1) o1(2) restrictH_def) 
     next
       case False
       then have "h2 x = Some y1"
         using \<open>h1 x = Some y1 \<or> h2 x = Some y1\<close> by blast 
       then show ?thesis
         by (metis (mono_tags, lifting) \<open>h2 \<in> {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)}\<close>
             \<open>m1 \<subseteq>\<^sub>m h2\<close> \<open>m1(x \<mapsto> y1) \<in> allmaps (insert x F) Y\<close> fun_upd_triv map_le_upd mem_Collect_eq restrictH_def) 
     qed
   qed
   then show "\<And>xa. xa \<in> restrictH {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)} F Y \<times> Y \<Longrightarrow>
          (case xa of (m, y) \<Rightarrow> m(x \<mapsto> y))
          \<in> restrictH {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)} (insert x F) Y" by auto
 next
   fix m2
   assume a1: "m2 \<in> (restrictH ?H' (insert x F) Y)"
   then have "m2 \<in> allmaps (insert x F) Y"
     by (simp add: restrictH_def) 
   then have "m2 x \<in> Some ` Y" 
   proof -
     have "m2 \<in> restrictH {f \<in> Hc. \<exists>fa. fa \<in> Hc \<and> fa x \<noteq> f x \<and> (\<forall>a. a \<in> F \<longrightarrow> fa a = f a)} (insert x F) Y"
       using \<open>m2 \<in> restrictH {h \<in> Hc. \<exists>h'\<in>Hc. h' x \<noteq> h x \<and> (\<forall>a\<in>F. h' a = h a)} (insert x F) Y\<close> by presburger
     then have "dom m2 = insert x F \<and> ran m2 \<subseteq> Y"
       by (simp add: allmaps_def restrictH_def)
     then show ?thesis
       by (metis (no_types) contra_subsetD domD image_iff insertI1 ranI)
   qed
   then obtain y1 where o2: "Some y1 = m2 x" "y1\<in>Y" by auto 
   let ?m1 = "m2(x:=None)"
   have s1: "dom ?m1 = F"
     by (metis (mono_tags, lifting) Diff_insert_absorb \<open>m2 \<in> allmaps (insert x F) Y\<close>
         allmaps_def c1.hyps(2) dom_fun_upd mem_Collect_eq) 
  have "ran m2 \<subseteq> Y" using a1
    by (simp add: allmaps_def restrictH_def)
  then have "ran ?m1 \<subseteq> Y"
    by (metis ranI ran_restrictD restrict_complement_singleton_eq subset_eq) 
  then have s2: "?m1\<in>allmaps F Y" using s1 by (simp add: allmaps_def)
  obtain h1 where o1: "h1\<in>?H'" "m2 \<subseteq>\<^sub>m h1" using restrictH_def a1 by blast
  then have "?m1 \<subseteq>\<^sub>m h1"
    by (meson map_le_trans upd_None_map_le)
   then have s3: "?m1 \<in> restrictH ?H' F Y"
     by (metis (mono_tags, lifting) mem_Collect_eq o1(1) restrictH_def s2)
   then have "m2 = ?m1(x \<mapsto> y1)"
     by (simp add: o2(1))
   moreover have "(?m1, y1) \<in> restrictH ?H' F Y \<times> Y"
     using s3 o2(2) by blast 
   ultimately show "\<exists>xa\<in>restrictH ?H' F Y \<times> Y. m2 = (case xa of (m, y) \<Rightarrow> m(x \<mapsto> y))"
     by (metis (mono_tags, lifting) case_prod_conv)
 qed
  then have "card (restrictH ?H' (insert x F) Y) = card (restrictH ?H' F Y \<times> Y)"
    by (simp add: bij_betw_same_card) 
  then have s30: "card (restrictH ?H' (insert x F) Y) = 2 * card (restrictH ?H' F Y)"   
    by (simp add: card_cartesian_product cardY)
  have s31: "card (restrictH ?Ha (insert x F) Y ) = card (restrictH ?Ha F Y)"
    using bij_betw_same_card s10 by blast
  have "?H' \<inter> ?Ha = {}" by auto

   have s20: "finite (insert x F)"
    by (simp add: c1.hyps(1))
   have s21: "finite Y" using cardY
    using card_infinite by fastforce

  have "(restrictH ?H' (insert x F) Y) \<inter> (restrictH ?Ha (insert x F) Y) = {}"
  proof (rule ccontr)
    assume "(restrictH ?H' (insert x F) Y) \<inter> (restrictH ?Ha (insert x F) Y) \<noteq> {}"
    then obtain m where o1: "m \<in> (restrictH ?H' (insert x F) Y)" "m \<in> (restrictH ?Ha (insert x F) Y)"
      by auto
    obtain h1 where "h1 \<in> ?H'" "m \<subseteq>\<^sub>m h1" using restrictH_def o1 by blast
    moreover obtain h2 where "h2 \<in> ?Ha" "m \<subseteq>\<^sub>m h2" using restrictH_def o1 by blast
    moreover have "\<forall>y\<in>(insert x F). h1 y = h2 y"
      by (metis (no_types, lifting) \<open>m \<subseteq>\<^sub>m h1\<close> \<open>m \<subseteq>\<^sub>m h2\<close> domIff hx_none map_le_def o1(1)) 
    moreover have "\<forall>h1\<in>?H'.\<forall>h2\<in>?Ha. \<exists>y\<in>(insert x F). h1 y \<noteq> h2 y"
      by auto
    ultimately show False
      by simp
  qed
  moreover have "(restrictH ?H' (insert x F) Y) \<union> (restrictH ?Ha (insert x F) Y) = restrictH Hc (insert x F) Y"
    apply safe
    apply (simp add: restrictH_def)
    apply blast
    apply (simp add: restrictH_def)
    apply blast
    apply (simp add: restrictH_def)
    apply blast
    done
  moreover have "finite (restrictH ?H' (insert x F) Y)" using finiteres
    using s20 s21 by blast
  moreover have "finite (restrictH ?Ha (insert x F) Y)" using finiteres
    using s20 s21 by blast
  ultimately have s32: "card (restrictH Hc (insert x F) Y) = 
        card (restrictH ?H' (insert x F) Y) + card (restrictH ?Ha (insert x F) Y)"
    using card_Un_disjoint by (metis (no_types, lifting))

  have "(restrictH ?H' F Y) \<inter> (restrictH ?Ha F Y) = {}"
      proof (rule ccontr)
    assume "(restrictH ?H' F Y) \<inter> (restrictH ?Ha F Y) \<noteq> {}"
    then obtain m where o1: "m \<in> (restrictH ?H' F Y)" "m \<in> (restrictH ?Ha F Y)"
      by auto
    obtain h1 where "h1 \<in> ?H'" "m \<subseteq>\<^sub>m h1" using restrictH_def o1 by blast
    moreover obtain h2 where o2: "h2 \<in> ?Ha" "m \<subseteq>\<^sub>m h2" using restrictH_def o1 by blast
    moreover have "\<forall>y\<in>F. h1 y = h2 y"
      by (metis (no_types, lifting) \<open>m \<subseteq>\<^sub>m h1\<close> \<open>m \<subseteq>\<^sub>m h2\<close> domIff hx_none map_le_def o1(1))
    moreover have "h1 x \<noteq> h2 x"
      using calculation(1) calculation(3) calculation(5) by auto
    ultimately have "h2 \<in> ?H'" by auto
    from this o2(1) show False by auto
  qed
moreover have "(restrictH ?H' F Y) \<union> (restrictH ?Ha F Y) = restrictH Hc F Y"
    apply safe
    apply (simp add: restrictH_def)
    apply blast
    apply (simp add: restrictH_def)
    apply blast
    apply (simp add: restrictH_def)
    apply blast
    done

  moreover have "finite (restrictH ?H' F Y)" using finiteres
    using c1.hyps(1) s21 by blast
  moreover have "finite (restrictH ?Ha F Y)" using finiteres
    using c1.hyps(1) s21 by blast
  ultimately have s33: "card (restrictH Hc F Y) = 
        card (restrictH ?H' F Y) + card (restrictH ?Ha F Y)"
    using card_Un_disjoint by (metis (no_types, lifting))
  from s30 s31 s32 s33 have s60: "card (restrictH Hc (insert x F) Y) = card (restrictH Hc F Y) + card (restrictH ?H' F Y)"
    by auto


(*
  have "?Ha = {h\<in>Hc. \<not>((\<lambda>d. h(x:=Some d)) ` Y) \<subseteq> Hc}" by auto
  have ha1:"?Ha = {h\<in>Hc. \<exists>d\<in>Y.  h(x:=Some d) \<notin> Hc}" by auto
  have ha2:"\<forall>h\<in>?Ha. \<forall>d\<in>Y. Some d \<noteq> h x \<longrightarrow> h(x:=Some d) \<notin> ?Ha"
    proof
      fix h
      assume a1: "h\<in>?Ha"
      then obtain d where o1: "d\<in>Y" "h(x:=Some d) \<notin> Hc" by auto
      then have s1: "h(x:=Some d)\<notin>?Ha" by auto
      then have "Some d \<noteq> h x" using a1 by auto
      obtain e where o2: "h x = Some e"
        by (metis (no_types, lifting) DiffE UNIV_I a1 domD domh ha1)
      then have "e\<in>Y"
        using a1 ranI ranh by fastforce
      moreover have "e\<noteq>d" using \<open>Some d \<noteq> h x\<close> o2 by auto 
      ultimately have "Y = {d,e}" using cardY o1(1) card_2_explicit by fastforce 
      then show "\<forall>d'\<in>Y. Some d' \<noteq> h x \<longrightarrow> h(x:=Some d') \<notin> ?Ha"
        using o2 s1 by auto 
    qed
  then have "?Ha = {h\<in>Hc. \<forall>d\<in>Y. Some d\<noteq>h x \<longrightarrow> h(x:=Some d) \<notin> Hc}"
    by (smt Collect_cong cardY card_2_exists fun_upd_upd ha1 map_upd_eqD1 mem_Collect_eq)
    

  have "bij_betw (\<lambda>m. m(x:=None)) (restrictH ?Ha (insert x F) Y) (restrictH ?Ha F Y)"
      apply(rule bij_betw_imageI)
     apply(simp add: inj_on_def)
     apply rule
    apply rule
  proof
    fix h1 h2
    assume a1: "h1\<in>(restrictH ?Ha (insert x F) Y)" "h2\<in>(restrictH ?Ha (insert x F) Y)" 
           "h1(x := None) = h2(x := None)"
    then obtain h where o1: "h\<in>?Ha" "h1 \<subseteq>\<^sub>m h" using restrictH_def
        proof -
          assume a1: "\<And>h. \<lbrakk>h \<in> Hc - {h \<in> Hc. (\<lambda>d. h(x \<mapsto> d)) ` Y \<subseteq> Hc}; h1 \<subseteq>\<^sub>m h\<rbrakk> \<Longrightarrow> thesis"
          have "h1 \<in> allmaps (insert x F) Y \<and> (\<exists>f. f \<in> Hc - {f \<in> Hc. (\<lambda>b. f(x \<mapsto> b)) ` Y \<subseteq> Hc} \<and> h1 \<subseteq>\<^sub>m f)"
            using \<open>h1 \<in> restrictH (Hc - {h \<in> Hc. (\<lambda>d. h(x \<mapsto> d)) ` Y \<subseteq> Hc}) (insert x F) Y\<close> restrictH_def by fastforce
          then show ?thesis
            using a1 by meson
        qed
        then have "\<forall>d\<in>Y. Some d \<noteq> h x \<longrightarrow> h(x:=Some d) \<notin> ?Ha" using ha2 by auto
        have "h1 x \<noteq> None" using hx_none a1(1) by fastforce
        then have "h x = h1 x" using o1(2) map_le_def by (metis domIff)
  have "\<forall>h\<in>?H'. ((\<lambda>d. h(x:=Some d)) ` Y) \<subseteq> ?H'" by auto *)


  have s40: "\<forall>B\<subseteq>F. shatters ?H' B Y \<longrightarrow> shatters ?H' (insert x B) Y"
  proof(safe)
    fix B
    assume "B\<subseteq>F"
    assume "shatters ?H' B Y"
    then have s1: "(\<forall>m\<in>(allmaps B Y).\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h)"  by (simp add: alt_shatters)
    have "(\<forall>m\<in>(allmaps (insert x B) Y).\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h)"
    proof
      fix m
      assume "m\<in>(allmaps (insert x B) Y)" 
      then obtain n d where o1: "m = (\<lambda>(m,d). m(x:=Some d)) (n, d)" "n\<in> allmaps B Y" "d\<in>Y"
        using c1(2) bij_allmaps[of x B Y] \<open>B \<subseteq> F\<close> bij_betw_imp_surj_on by blast
      then obtain h where o2: "h\<in>?H'" "n \<subseteq>\<^sub>m h" using s1 by blast
      then obtain h2 where o3: "h2 x \<noteq> h x \<and> (\<forall>a\<in>F. h2 a = h a)" "h2\<in>Hc" by blast
      then have s2: "h2 \<in> ?H'"
        using o2(1) by force
      have "h \<in> Hc" using o2(1) by auto
     then have "h\<in>H_map" using \<open>Hc \<subseteq> H_map\<close> by blast
     have "h2\<in>H_map" using \<open>Hc \<subseteq> H_map\<close> o3(2) by blast
     have "Some ` Y = {h x, h2 x}"
     proof -
       have "ran h \<subseteq> Y"
         by (simp add: \<open>h \<in> H_map\<close> ranh)
       then have "h x \<in> Some ` Y"
         by (metis UNIV_I \<open>h \<in> H_map\<close> contra_subsetD domD domh imageI ranI)
       moreover have "h2 x \<in> Some ` Y"
         by (metis (mono_tags, hide_lams) Hdef \<open>h2 \<in> H_map\<close> image_iff mapify_def)
       ultimately show ?thesis using card_2_explicit o3(1)
         by (metis card_some_y)
     qed
     show "\<exists>h\<in>?H'. m \<subseteq>\<^sub>m h"
     proof (cases "Some d = h x")
       case True
       then show ?thesis
         by (metis (mono_tags, lifting) case_prod_conv fun_upd_triv map_le_upd o1(1) o2(1) o2(2)) 
     next
       case False
       then have "Some d = h2 x"
         using \<open>Some ` Y = {h x, h2 x}\<close> o1(3) by blast 
       then show ?thesis
         by (metis (mono_tags, lifting) \<open>B \<subseteq> F\<close> allmaps_def case_prod_conv fun_upd_triv map_le_def
            map_le_upd mem_Collect_eq o1(1) o1(2) o2(2) o3(1) s2 subset_iff) 
     qed
   qed
    then show "shatters ?H' (insert x B) Y" using alt_shatters by blast
  qed

  have "card (restrictH Hc F Y) \<le> card ({B. B\<subseteq>F \<and> shatters Hc B Y})"
    using c1.hyps(3) a100 by auto

  moreover have "{B. B\<subseteq>F \<and> shatters Hc B Y} = {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B}"
    using c1.hyps(2) by blast

  ultimately have s61: "card (restrictH Hc F Y) \<le> card ({B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B})"
    by auto

  have "?H' \<subseteq> H_map"
    using a100 by blast
  then have "card (restrictH ?H' F Y) \<le> card ({B. B\<subseteq>F \<and> shatters ?H' B Y})"
    using c1.hyps(3) by auto

  moreover have "{B. B\<subseteq>F \<and> shatters ?H' B Y} \<subseteq> {B. B\<subseteq>F \<and> shatters ?H' (insert x B) Y}"
    using s40 by blast
  moreover have "finite {B. B\<subseteq>F \<and> shatters ?H' (insert x B) Y}"
    by (simp add: c1.hyps(1))
  ultimately have "card (restrictH ?H' F Y) \<le> card ({B. B\<subseteq>F \<and> shatters ?H' (insert x B) Y})"
    by (meson card_mono le_trans)
    

  moreover have "bij_betw (\<lambda>B. insert x B) {B. B\<subseteq>F \<and> shatters ?H' (insert x B) Y} {B. B\<subseteq>(insert x F) \<and> shatters ?H' B Y \<and> x \<in> B}"
   apply(rule bij_betwI')
    using c1.hyps(2) apply fastforce
    apply blast
  proof -
    fix b
    assume a1: "b\<in>{B. B\<subseteq>(insert x F) \<and> shatters ?H' B Y \<and> x \<in> B}"
    then have s1: "b\<subseteq>(insert x F)" "shatters ?H' b Y" "x \<in> b" by auto
    then obtain b' where "insert x b' = b" "x\<notin>b'" by auto
    then have "b' \<subseteq> F"
      using \<open>b \<subseteq> insert x F\<close> by blast
    then have "b' \<in> {B. B\<subseteq>F \<and> shatters ?H' (insert x B) Y}"
      using \<open>insert x b' = b\<close> s1(2) by blast
    then show "\<exists>xa\<in>{B. B \<subseteq> F \<and> shatters ?H' (insert x B) Y}.  b = insert x xa"
      using \<open>insert x b' = b\<close> by blast
  qed

  ultimately have s55: "card (restrictH ?H' F Y) \<le> card ({B. B\<subseteq>(insert x F) \<and> shatters ?H' B Y \<and> x \<in> B})"
    by (simp add: bij_betw_same_card) 

  have "\<forall>B. shatters ?H' B Y \<longrightarrow> shatters Hc B Y"
    using over_shatter by (metis (mono_tags, lifting) mem_Collect_eq subsetI)
  then have "{B. B\<subseteq>(insert x F) \<and> shatters ?H' B Y \<and> x \<in> B} \<subseteq> {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B}"
    by blast
   moreover have s70: "finite {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B}"
     by (simp add: c1.hyps(1))
   ultimately have s62: "card (restrictH ?H' F Y) \<le> card ({B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B})"
     using s55 card_mono by (metis (no_types, lifting) le_trans) 

   from s60 s61 s62 have "card (restrictH Hc (insert x F) Y) \<le> card ({B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B})
                                                              + card ({B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B})"
     by auto

  moreover have "{B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B} \<union> {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B}
      = {B. B \<subseteq> insert x F \<and> shatters Hc B Y}" by auto

  moreover have "{B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B} \<inter> {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<in> B}
      = {}" by auto
  moreover have "finite {B. B\<subseteq>(insert x F) \<and> shatters Hc B Y \<and> x \<notin> B}"
     by (simp add: c1.hyps(1))
   ultimately show "card (restrictH Hc (insert x F) Y) \<le> card {B. B \<subseteq> insert x F \<and> shatters Hc B Y}" 
     using card_Un_disjoint s70 by (metis (no_types, lifting)) 
 qed
qed



lemma assumes "VCDim = Some d"
      and "m>0"
      and "C\<subseteq>X"
      and "card C = m"
    shows superaux: "card (restrictH H_map C Y) \<le> sum (\<lambda>x. m choose x) {0..d}"
proof -
  have f3: "finite C" using assms(2,4) card_ge_0_finite by auto
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
    then show ?case using f3 by (simp add: n_subsets assms(4) Suc.IH)
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
  have "\<forall>n \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}. n \<le> sum (\<lambda>x. m choose x) {0..d}" using superaux assms(1,2)
    by fastforce
  then have "finite {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"
    using finite_nat_set_iff_bounded_le by auto
  moreover have "{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
  ultimately have "growth m \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"
    using Max_in growth_def by auto
  then show ?thesis
    using assms(1) assms(2) vcd.superaux vcd_axioms by fastforce
qed


lemma growthgtone: "VCDim = Some d \<Longrightarrow> m \<ge> 1 \<Longrightarrow> growth m \<ge> 1"
proof -
  assume a1: "m \<ge> 1" "VCDim = Some d"
  then have "\<forall>n \<in> {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}. n \<le> sum (\<lambda>x. m choose x) {0..d}" using superaux
    by fastforce
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
    by (metis (no_types, lifting) Collect_cong Max_ge choose_one leD neq0_conv zero_less_binomial_iff) 
qed


(*Theorem 6.11*)
lemma assumes "set_pmf D \<subseteq> X"
      and "f ` X = Y"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
    shows theorem611: "measure_pmf.prob (Samples m D f) {S. \<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h)
                   \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
  sorry


definition representative :: "(nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "representative S m \<epsilon> D f \<longleftrightarrow> (\<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>)"


definition "uniform_convergence = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y  \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f} \<ge> 1 - \<delta>)))"

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

lemma aux123: "m\<ge>d \<Longrightarrow> sum (\<lambda>x. m choose x) {0..d} \<le> (d+1)*m^d"
   using sum_bounded_above[of "{0..d}" "(\<lambda>x. m choose x)" "m^d"]
   by (smt One_nat_def add.right_neutral add_Suc_right atLeastAtMost_iff binomial_le_pow binomial_n_0 card_atLeastAtMost diff_zero
       le_antisym le_neq_implies_less le_trans less_one nat_le_linear nat_zero_less_power_iff neq0_conv of_nat_id power_increasing_iff)

  lemma assumes "set_pmf D \<subseteq> X"
      and "f ` X = Y"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
      and "\<epsilon> > 0"
      and "m \<ge> M \<epsilon> \<delta>"
      and "M = (\<lambda>\<epsilon> \<delta>. nat( ceiling (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)))"
      and "VCDim = Some d"
    shows aux456: "h\<in>H \<Longrightarrow> abs(PredErr D f h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(real(2*m)))
      \<Longrightarrow> abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>"
  proof -
    fix S h
    assume a10: "h\<in>H" "abs(PredErr D f h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))"
    have f1: "m \<ge> (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)"
      using assms(5,6) ceil_gr by auto
    then have a2: "2*m \<ge> d"
      by (smt divide_nonneg_nonneg less_imp_le_nat mult_2 nat_less_real_le of_nat_0_le_iff of_nat_add zero_le_power2) 
    from f1 have a1: "2*m > 1"
      by (smt divide_nonneg_nonneg le_add2 le_neq_implies_less less_1_mult mult.right_neutral numeral_eq_one_iff
          of_nat_0_le_iff one_add_one real_of_nat_ge_one_iff semiring_norm(85) zero_le_power2) 

    from aux123 lem610 a2 a1 assms(7) have f2: "growth (2*m) \<le> (d+1)*(2*m)^d"
      by (smt le_trans less_imp_le_nat of_nat_0_less_iff real_of_nat_ge_one_iff) 

    have a12: "growth (2*m) \<ge> 1" using growthgtone assms(7) a1 by auto
    have ad: "\<delta>>0" using assms(3) by auto

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
     moreover have "((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2) > 0" using assms(4) ad c1
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
       by (smt ad assms(4) mult_sign_intros(5) real_le_lsqrt
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
      then show ?thesis using assms(4)
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
     then have "1/sqrt(2*m) \<le> 1/(4/(\<epsilon>*\<delta>/2))" using assms(4) ad frac_le
       by (smt mult_pos_pos zero_less_divide_iff)
     then have "1/sqrt(2*m) \<le> (\<epsilon>*\<delta>/2)/4" by simp
     then have "4/sqrt(2*m) \<le> (\<epsilon>*\<delta>/2)" by linarith
     then have "4/sqrt(2*m) \<le> (\<epsilon>/2)*\<delta>" by simp
     then have "4/sqrt(2*m)/\<delta> \<le> \<epsilon>/2" using ad pos_divide_le_eq by blast
     then show ?thesis
       by (simp add: divide_divide_eq_left mult.commute)
    qed
    ultimately have "(4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m)) \<le> \<epsilon>" by auto
    from this a10 show "abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>" by auto
  qed

lemma subsetlesspmf: "A\<subseteq>B \<Longrightarrow> measure_pmf.prob Q A \<le> measure_pmf.prob Q B"
  using measure_pmf.finite_measure_mono by fastforce

lemma assumes "set_pmf D \<subseteq> X"
      and "f ` X = Y"
      and "\<delta>\<in>{x.0<x\<and>x<1}"
      and "\<epsilon> > 0"
      and "m \<ge> M \<epsilon> \<delta>"
      and "M = (\<lambda>\<epsilon> \<delta>. nat (ceiling (((ln(d+1)+d*2)/(\<epsilon>*\<delta>/2)^2)^2/2 + (4/(\<epsilon>*\<delta>/2))^2/2 + 1 + d)))"
      and "VCDim = Some d"
    shows aux200: "measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f} \<ge> 1 - \<delta>"
proof -
  have "\<forall>h S. h\<in>H \<longrightarrow> abs(PredErr D f h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(real(2*m)))
      \<longrightarrow> abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>" using assms aux456 by auto
  then have "{S. \<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))}
     \<subseteq>{S. (\<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>)}" by auto
  moreover have "measure_pmf.prob (Samples m D f) {S. \<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h)
     \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
    using assms theorem611 by auto
  ultimately show ?thesis using subsetlesspmf representative_def
    by (smt Collect_cong) 
qed


lemma assumes "VCDim = Some d"
  shows "uniform_convergence"
proof -
  obtain M where "M = (\<lambda>\<epsilon> \<delta>. nat \<lceil>((ln (real (d + 1)) + real (d * 2)) / (\<epsilon> * \<delta> / 2)\<^sup>2)\<^sup>2 / 2 + (4 / (\<epsilon> * \<delta> / 2))\<^sup>2 / 2
             + 1 + real d\<rceil>)" by auto
  from this have "(\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow>
               f ` X = Y \<longrightarrow>
               (\<forall>(m::nat) \<epsilon>. 0 < \<epsilon> \<longrightarrow>
                      (\<forall>(\<delta>::real)\<in>{x. 0 < x \<and> x < 1}.
                          M \<epsilon> \<delta> \<le> m \<longrightarrow>
                          1 - \<delta> \<le> measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f})))"
    using aux200 assms by auto
  then show ?thesis using uniform_convergence_def by auto
qed




lemma assumes "representative S m \<epsilon> D f"
          and "S\<in>Samples m D f"
          and "set_pmf D \<subseteq> X"
          and "f ` X = Y"
          and RealizabilityAssumption: "\<exists>h'\<in>H. PredErr D f h' = 0"
        shows reptopred: "PredErr D f (ERMe S m) \<le> \<epsilon>"
proof -
      from RealizabilityAssumption  
    obtain h' where h'H: "h'\<in>H" and u: "PredErr D f h' = 0" by blast

    from u have "measure_pmf.prob D {S \<in> set_pmf D. f S \<noteq> h' S} = 0" unfolding PredErr_alt .
    with measure_pmf_zero_iff[of D "{S \<in> set_pmf D. f S \<noteq> h' S}"]       
    have correct: "\<And>x. x\<in>set_pmf D \<Longrightarrow> f x = h' x" by blast

 from assms(2) set_Pi_pmf[where A="{0..<m}"]
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

    then have "h' \<in>ERM S m" using ERM_0_in h'H by auto
    then have "ERMe S m \<in> ERM S m" using ERMe_def by (metis some_eq_ex)
    then have "ERMe S m \<in> H" using ERM_subset by blast     
    moreover have "(\<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h) \<le> \<epsilon>)"
      using representative_def assms(1) by blast
    ultimately have "abs(PredErr D f (ERMe S m) - TrainErr S {0..<m} (ERMe S m)) \<le> \<epsilon>"
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



lemma assumes "(\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y  \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f} \<ge> 1 - \<delta>))"
  shows aux44:"set_pmf D \<subseteq> X \<Longrightarrow> f ` X = Y \<Longrightarrow> (\<exists>h'\<in>H. PredErr D f h' = 0) \<Longrightarrow>  \<epsilon> > 0 \<Longrightarrow> \<delta>\<in>{x.0<x\<and>x<1} \<Longrightarrow> m \<ge> M \<epsilon> \<delta> \<Longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>"
  proof -
  fix D f m \<epsilon> \<delta>
  assume a1: "set_pmf D \<subseteq> X" "f ` X = Y" "\<exists>h'\<in>H. PredErr D f h' = 0" "\<epsilon> > 0" "\<delta>\<in>{x.0<x\<and>x<1}" "m \<ge> M \<epsilon> \<delta>"
  from this assms have "measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f} \<ge> 1 - \<delta>" by auto
  then have "measure_pmf.prob (Samples m D f) 
  {S. set_pmf D \<subseteq> X \<and> f ` X = Y \<and> (\<exists>h'\<in>H. PredErr D f h' = 0) \<and> (S\<in>Samples m D f) \<and> representative S m \<epsilon> D f} \<ge> 1 - \<delta>"
    using a1 by (smt DiffE mem_Collect_eq pmf_prob_cong set_pmf_iff)
  moreover have "{S. set_pmf D \<subseteq> X \<and> f ` X = Y \<and> (\<exists>h'\<in>H. PredErr D f h' = 0) \<and> (S\<in>Samples m D f) \<and> representative S m \<epsilon> D f}
        \<subseteq> {S. PredErr D f (ERMe S m) \<le> \<epsilon>}" using reptopred by blast
  ultimately show "measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>"
    using subsetlesspmf order_trans by fastforce
qed


(* lemma 4.2*)
lemma assumes "uniform_convergence"(*"representative H S m (\<epsilon>/2)"*)
    and RealizabilityAssumption: "\<exists>h'\<in>H. PredErr D f h' = 0"
  shows "PAC_learnable (ERMe)" 
proof -
  obtain M where f1: "(\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y  \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. representative S m \<epsilon> D f} \<ge> 1 - \<delta>))"
    using assms uniform_convergence_def by auto
  from aux44 f1 have "(\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y \<longrightarrow> (\<exists>h'\<in>H. PredErr D f h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. PredErr D f (ERMe S m) \<le> \<epsilon>} \<ge> 1 - \<delta>))"
  by blast
  then show ?thesis using PAC_learnable_def by auto
qed

end
end