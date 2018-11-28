theory VCDim
  imports Complex_Main
begin

lemma "finite A \<Longrightarrow> \<exists>l. set l = A" using finite_list by auto


term restrict_map

definition restrictM :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b option) set" where
   "restrictM C D = {m. dom m = C \<and> ran m \<subseteq> D \<and> C\<noteq>{}}"

lemma "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (restrictM C D) "
  unfolding restrictM_def   
  sorry

lemma "finite D \<Longrightarrow> finite C \<Longrightarrow> card C > 0 \<Longrightarrow> card (restrictM C D) =  card D ^ card C"
proof (induct rule: finite.induct)
  case emptyI
  then show ?case by(auto intro!: ranI simp: restrictM_def power_0_left card_gt_0_iff)   
next
  case (insertI A a)
  then show ?case sorry
qed 


definition restrictH  where
  "restrictH H C D = restrictM C D \<inter> H"
  
definition "restrictMn C D = (if C = {} then {} else {m. dom m = C \<and> ran m \<subseteq> D})"  
definition "restrictHn H C D = {m\<in>(restrictMn C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatteringn H C D \<longleftrightarrow> restrictMn C D = restrictHn H C D"
  
lemma "shatteringn H C D \<longleftrightarrow> (\<forall>m\<in>(restrictMn C D).\<exists>h\<in>H. m \<subseteq>\<^sub>m h)"
  by (smt Collect_cong dom_def dom_empty mem_Collect_eq restrictHn_def restrictMn_def shatteringn_def)

lemma assumes "card D = 2"
  shows "finite C \<Longrightarrow> card (restrictHn H C D) \<le> card ({B. B\<subseteq>C \<and> shatteringn H B D})"
proof (induct rule: finite.induct)
  case emptyI
  then show ?case by (simp add: restrictMn_def restrictHn_def)
next
  case (insertI A a)
  then show ?case sorry
qed

definition "shattering H C D \<longleftrightarrow> restrictM C D \<subseteq> H"

lemma "shattering H C D \<longleftrightarrow> restrictM C D = restrictH H C D"
  by(auto simp: shattering_def restrictH_def)

lemma "restrictM C {} = {}" using restrictM_def
  by (smt Collect_empty_eq bot_least domD dom_def empty_iff equalityI mem_Collect_eq ranI) 
    
lemma "H \<noteq> {}  \<Longrightarrow> shattering H {} D"
  by (simp add: restrictM_def shattering_def) 

lemma assumes "card D = 2"
      and "\<forall>h\<in>H.  \<forall>x. fun_upd h x None \<in> H"
  shows "finite C \<Longrightarrow> card (restrictH H C D) \<le> card ({B. B\<subseteq>C \<and> shattering H B D})"
proof (induct rule: finite.induct)
  case emptyI
  then show ?case
    by (simp add: restrictM_def restrictH_def)
next
  case (insertI A a)
  then show ?case sorry
qed    

  
  
  
  
  
fun restrict :: "('a \<Rightarrow> real) set \<Rightarrow> 'a list \<Rightarrow> real list set" where
"restrict H C = image (\<lambda>x. map x C) H"



fun inspair :: "('b\<times>'b list) \<Rightarrow> 'b list" where
"inspair (a,l) = a#l"


lemma card_inspair:"card (image inspair A) = card A"
  by (metis card_image inj_onI inspair.cases inspair.simps list.inject)

lemma fuse_inspair: "a\<in>A \<Longrightarrow> b\<in>B \<Longrightarrow> (a#b)\<in> image inspair (A\<times>B)"
  by (simp add: image_iff)

lemma "distinct C \<Longrightarrow> card (restrict {f. \<forall>x. f x \<in> {-1,1}} C) = 2^(length C)"
proof (induction C)
  case Nil
  have "\<forall>H. H \<noteq> {} \<longrightarrow> restrict H [] = {[]}" by auto
  moreover have "{f. \<forall>x. f x \<in> {-1,1}} \<noteq> {}" by auto
  ultimately have "restrict {f. \<forall>x. f x \<in> {- 1, 1}} [] = {[]}" by smt
  then show ?case
    by (smt One_nat_def card.insert card_empty finite.intros(1) insert_absorb
        insert_not_empty list.size(3) power_0) 
next
  case (Cons a C)
  have s0: "restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C) = image (\<lambda>g. (g a)#(map g C)) {f. \<forall>x. f x \<in> {- 1, 1}}"
    by auto
  have "\<forall>e\<in>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)).
         e\<in>image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))"
  proof
    fix e
    assume a2: "e\<in>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C))"
    then obtain b t where s1: "e = b#t" by auto
    then have s2: "t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} C"
      using a2 by auto
    moreover have s3: "b \<in> {-1,1}" using s1 a2 by auto
    ultimately show "e\<in>image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))"
      by (simp add: fuse_inspair s1)
  qed 
  then have s10: "(restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C))
           \<subseteq> image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))"
    by auto
  have a1: "\<forall>x\<in>set C. a \<noteq> x" using Cons.prems by auto
  have "\<forall>t\<in>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C).
        1#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C) \<and>
        (-1)#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)"
  proof
    fix t
    assume "t\<in>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C)"
    then obtain f1 where s1: "f1\<in>{f. \<forall>x. f x \<in> {- 1, 1}}" "t = map f1 C" by auto
    have s2: "fun_upd f1 a (-1)\<in>{f. \<forall>x. f x \<in> {- 1, 1}}"
         "fun_upd f1 a 1\<in>{f. \<forall>x. f x \<in> {- 1, 1}}" using s1(1) by auto
    have s3: "map (fun_upd f1 a 1) C = t" "map (fun_upd f1 a (-1)) C = t"
      using a1 s1(2) by auto
    then have "1#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)"
              "(-1)#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)"
       apply (smt fun_upd_same image_iff s0 s2(2))
       apply (smt s3 fun_upd_same image_iff s0 s2(1))
      done
    then show "1#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C) \<and>
        (-1)#t\<in>restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)" by auto
  qed
  then have s11: "image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))
             \<subseteq> (restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C))" by auto
 
  from s10 s11 have "(restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C))
           = image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))"
    by auto
 moreover have "card (image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C)))
            =card ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))"
    using card_inspair by auto
  moreover have "card ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C))
                = 2 * card (restrict {f. \<forall>x. f x \<in> {- 1, 1}} C)"
    by (simp add: card_cartesian_product)
  moreover have "distinct C" using Cons.prems by auto
  ultimately have "card (restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)) = 2*(2 ^ length C)"
    using Cons.IH by auto
  then show "card (restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C)) = (2 ^ length (a#C))"
    using a1 by auto
qed

definition "shatters H C \<equiv> restrict H C = {l. length l = length C \<and> (\<forall>x\<in>(set l). x\<in>{-1,1::real})}"

lemma "\<forall>H\<subseteq>{f. \<forall>x. f x \<in> {-1,1::real}}. card (restrict H C) \<le> card ({B. B\<subseteq>(set C) \<and>  shatters H (filter (\<lambda>x. x\<in>B) C)})"
proof(induction C)
  case Nil
  show ?case
  proof
  fix H
  show "H\<subseteq>{f. \<forall>x. f x \<in> {-1,1::real}} \<longrightarrow> card (restrict H []) \<le> card ({B. B\<subseteq>(set []) \<and>  shatters H (filter (\<lambda>x. x\<in>B) [])})"
  proof (cases "H = {}")
    case True
    then show ?thesis by auto
  next
    case c1: False
    moreover have "\<forall>H. H \<noteq> {} \<longrightarrow> restrict H [] = {[]}" by auto
    ultimately have s1: "card (restrict H []) = 1"
      by (smt is_singletonI is_singleton_altdef)
    have "\<forall>B. shatters H [x\<leftarrow>[] . x \<in> B]" using shatters_def c1
      by fastforce
    then have "card {B. B \<subseteq> set [] \<and> shatters H [x\<leftarrow>[] . x \<in> B]} = 1" by auto
    then show ?thesis using s1 by auto
  qed
qed
next
  case (Cons a C)


  then show ?case sorry
qed


lemma "X\<subseteq>A \<Longrightarrow> finite X \<Longrightarrow> card {f. \<forall>x. (f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)} = 2 ^ (card X)"
  apply(rule finite_subset_induct[of X A])
  apply auto[2]
proof -
  obtain f::"'a \<Rightarrow> real" where s2:"\<forall>x. f x = 1" by fastforce
  then have "\<forall>q. q\<in>{f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = 1)} \<longrightarrow> q = f" by auto
  then have "{f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = (1::real))} = {f}" by auto
  then have "bij_betw id {f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = (1::real))} {f}" by auto
  then have "card {f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = (1::real))} = card {f}"
    using bij_betw_same_card[of id "{f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = (1::real))}" "{f}"]
    
    using arg_cong[of "{f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = (1::real))}" "{f}" "card"]
    
  moreover have "card {f} = 1" by auto
  ultimately have "card {f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = 1)} = 1"
    using arg_cong[of "{f. \<forall>x. f x \<in> {(-1::real),1} \<and> (x \<notin> {} \<longrightarrow> f x = 1)}" "{f}" "card"]
    


lemma "finite X \<Longrightarrow> card {f. \<forall>x. (f x \<in> {-1,1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)} = 2 ^ (card X)"
proof-
  assume "card X = 1"
  then obtain x where s1: "x\<in>X" by fastforce
  obtain f::"'a \<Rightarrow> real" where s2:"\<forall>x. f x = 1" by fastforce
  then have s3: "f \<in> {f. \<forall>x. (f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)}" by auto
  from this s1 have s4: "fun_upd f x (-1) \<in> {f. \<forall>x. (f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)}" by auto
  have "fun_upd f x (-1) x \<noteq> f x " using s2 by auto
  then have "fun_upd f x (-1) \<noteq> f" by fastforce
  then have s5:"card {f, fun_upd f x (-1)} = 2" by auto
  from s3 s4 have s6: "{f, fun_upd f x (-1)} \<subseteq> {f. \<forall>x. (f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)}" by auto
  have "\<forall>q. (q \<in> {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1))} \<longrightarrow> q \<in> {f, fun_upd f x (-1)})"
  proof
    fix q
    have "q \<in> {f. \<forall>x. (x \<in> X \<longrightarrow> f x \<in> {(- 1::real), 1}) \<and> (x \<notin> X \<longrightarrow> f x = 1)} \<Longrightarrow>
        q \<in> {f, f(x := - 1)}"
      proof (cases "q x = 1")
        case True
        moreover assume "q \<in> {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1))}"
        ultimately have "\<forall>x. q x=f x"
          by (smt CollectD One_nat_def \<open>card X = 1\<close> card_Suc_eq s1 s2 singleton_iff)
        then show "q\<in>{f, fun_upd f x (-1)}" by auto
      next
        case c1: False
        moreover assume "q \<in> {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1))}"
        ultimately have "\<forall>x2. q x2=fun_upd f x (-1) x2"
          by (smt CollectD One_nat_def \<open>card X = 1\<close> card_Suc_eq fun_upd_apply insert_iff s2 singletonD) 
        then show "q\<in>{f, fun_upd f x (-1)}" by auto
      qed
    then show "q \<in> {f. \<forall>x. (x \<in> X \<longrightarrow> f x \<in> {(- 1::real), 1}) \<and> (x \<notin> X \<longrightarrow> f x = 1)} \<longrightarrow>
        q \<in> {f, f(x := - 1)}" by auto
  qed
  then have "{f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1))} \<subseteq>{f, fun_upd f x (-1)}"
    by auto
  from this s5 s6 have "card {f. \<forall>x. (f x \<in> {(-1::real),1}) \<and> (x\<notin>X \<longrightarrow> f x = 1)} = 2"
    by (smt Collect_cong Collect_mono_iff insert_compr) 
qed    


lemma "X\<subseteq>A \<Longrightarrow> finite X \<Longrightarrow> finite Y \<Longrightarrow> card {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> Y) \<and> (x\<notin>X \<longrightarrow> f x = undefined))} = (card Y) ^ (card X)"
  apply (rule finite_subset_induct[of X A])
     apply auto
proof -
  have "\<forall>f g. f\<in>{f. \<forall>x. f x = undefined} \<longrightarrow> g\<in>{f. \<forall>x. f x = undefined} \<longrightarrow> f = g" by auto
  moreover have "{f. \<forall>x. f x = undefined} \<noteq> {}" by auto
  ultimately show "card {f. \<forall>x. f x = undefined} = Suc 0"
    using card_Suc_eq by fastforce 
   

lemma "let X = {0::nat}; Y = {0::nat} in card {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> Y) \<and> (x\<notin>X \<longrightarrow> f x = 0))}=1"
  apply auto
  oops
lemma "\<forall>x. f x = g x \<Longrightarrow> f = g" by auto

 (*have "finite (restrict {f. \<forall>x. f x \<in> {- 1, 1}} C)" 
    using Cons.IH by (metis card_infinite power_eq_0_iff zero_neq_numeral) 
  then have "finite (image inspair ({-1,1::real}\<times>(restrict {f. \<forall>x. f x \<in> {- 1, 1}} C)))"
    by auto
  then have "finite (restrict {f. \<forall>x. f x \<in> {- 1, 1}} (a#C))"
    using s10 finite_subset by auto*)


value "let X = {0::nat}; Y = {0::nat} in card {f. \<forall>x.((x\<in>X \<longrightarrow> f x \<in> Y) \<and> (x\<notin>X \<longrightarrow> f x = undefined))}"

lemma "\<nexists>x. x\<in>{}" by auto