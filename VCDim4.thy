theory VCDim4
  imports Complex_Main AGentleStart HOL.Vector_Spaces
begin
  

definition "mapify f = (\<lambda>x. Some (f x))" (*This should exist somewhere*)
  
definition "allmaps C D = (if C = {} then {} else {m. dom m = C \<and> ran m \<subseteq> D})"  
definition "restrictH H C D = {m\<in>(allmaps C D). \<exists>h\<in>H. m \<subseteq>\<^sub>m h}"
definition "shatters H C D \<longleftrightarrow> allmaps C D = restrictH H C D"


lemma finitemaps: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (allmaps C D)"
  by (simp add: allmaps_def finite_set_of_finite_maps)

lemma finiteres: "finite C \<Longrightarrow> finite D \<Longrightarrow> finite (restrictH H C D)"
  by (simp add: finitemaps restrictH_def)

lemma alt_shatters: "shatters H C D \<longleftrightarrow> (\<forall>m\<in>(allmaps C D).\<exists>h\<in>H. m \<subseteq>\<^sub>m h)" 
  by (smt Collect_cong dom_def dom_empty mem_Collect_eq restrictH_def allmaps_def shatters_def)
  
lemma empty_shatted: "shatters H {} D"
  by (simp add: allmaps_def restrictH_def shatters_def)


lemma "dim B < card B \<Longrightarrow> dependent B"
  using dim_eq_card_independent nat_less_le by auto

lemma "dependent B = (\<exists>a\<in>B. a \<in> span (B - {a}))" using dependent_def by auto

lemma "a \<in> span B \<Longrightarrow> finite B \<Longrightarrow> \<exists>f. a = sum (\<lambda>x. scaleR (f x)  x) B"
  using span_finite by fastforce



datatype mivec = Supo "(real \<Rightarrow> nat) set"

(*typedef 'a movec = "UNIV::(nat \<Rightarrow> 'a) set"
morphisms vec_nth vec_lambda
  by simp *)

typedef movec = "{f::(nat \<Rightarrow> real). \<exists>k. \<forall>q>k. f q = 0}"
  morphisms vec_nth vec_lambda
  by auto



instantiation movec :: zero
begin
definition "0 \<equiv> vec_lambda (\<lambda> i. 0)"
  instance ..
end

instantiation movec :: plus
begin
  definition "(+) \<equiv> (\<lambda> x y. vec_lambda (\<lambda> i. vec_nth x i + vec_nth y i))"
  instance ..
end

instantiation movec ::  minus
begin
  definition "(-) \<equiv> (\<lambda> x y. vec_lambda (\<lambda> i. vec_nth x i - vec_nth y i))"
  instance ..
end

instantiation movec ::  uminus
begin
  definition "uminus \<equiv> (\<lambda> x. vec_lambda (\<lambda> i. - (vec_nth x i)))"
  instance ..
end

lemma zero_index [simp]: "vec_nth 0 i = 0"
  unfolding zero_movec_def
  by (simp add: movec.vec_lambda_inverse)

lemma plusin: "(\<lambda>i. movec.vec_nth x i + movec.vec_nth y i)\<in>{f. \<exists>k. \<forall>q>k. f q = 0}"
proof
  obtain k1 where o1: "\<forall>q>k1. movec.vec_nth x q = 0"
  using movec.vec_nth by auto
  obtain k2 where  o2: "\<forall>q>k2. movec.vec_nth y q = 0"
    using movec.vec_nth by auto
  obtain k where "k=max k1 k2" "\<forall>q>k. movec.vec_nth x q = 0"
      "\<forall>q>k. movec.vec_nth y q = 0" using o1 o2 by auto
  then have "\<forall>q>k. movec.vec_nth x q + movec.vec_nth y q = 0" by auto
  then show "\<exists>d.\<forall>q>d. movec.vec_nth x q + movec.vec_nth y q = 0" by auto
qed

lemma movector_add_component [simp]: "vec_nth (x + y) i = vec_nth x i + vec_nth y i"
  unfolding plus_movec_def using plusin
  by (simp add: movec.vec_lambda_inverse)

lemma minusin: "(\<lambda>i. movec.vec_nth x i - movec.vec_nth y i)\<in>{f. \<exists>k. \<forall>q>k. f q = 0}"
proof
  obtain k1 where o1: "\<forall>q>k1. movec.vec_nth x q = 0"
  using movec.vec_nth by auto
  obtain k2 where  o2: "\<forall>q>k2. movec.vec_nth y q = 0"
    using movec.vec_nth by auto
  obtain k where "k=max k1 k2" "\<forall>q>k. movec.vec_nth x q = 0"
      "\<forall>q>k. movec.vec_nth y q = 0" using o1 o2 by auto
  then have "\<forall>q>k. movec.vec_nth x q - movec.vec_nth y q = 0" by auto
  then show "\<exists>d.\<forall>q>d. movec.vec_nth x q - movec.vec_nth y q = 0" by auto
qed

lemma movector_minus_component [simp]: "vec_nth (x - y) i = vec_nth x i - vec_nth y i"
    unfolding minus_movec_def using minusin
  by (simp add: movec.vec_lambda_inverse)

lemma movector_uminus_component [simp]: "vec_nth (- x) i = - (vec_nth x i)"
  unfolding uminus_movec_def using vec_nth
  by (simp add: movec.vec_lambda_inverse)





lemma movec_eq_iff: "(x = y) \<longleftrightarrow> (\<forall>i. vec_nth x i = vec_nth y i)"
  by (simp add: vec_nth_inject [symmetric] fun_eq_iff)

(*
lemma movec_lambda_beta [simp]: "vec_nth (vec_lambda g) i = g i"
  using vec_nth  by (simp add: vec_lambda_inverse) 

lemma movec_lambda_unique: "(\<forall>i. vec_nth f i = g i) \<longleftrightarrow> vec_lambda g = f"
  by (auto simp add: movec_eq_iff)

lemma movec_lambda_eta [simp]: "vec_lambda (\<lambda> i. (vec_nth g i)) = g"
  by (simp add: movec_eq_iff) *)


instance movec ::  semigroup_add
  by standard (simp add: movec_eq_iff add.assoc)

instance movec ::  ab_semigroup_add
  by standard (simp add: movec_eq_iff add.commute)

instance movec ::  monoid_add
  apply standard
  using zero_movec_def movec_eq_iff by auto

instance movec ::  comm_monoid_add
  by standard (simp add: movec_eq_iff)

instance movec ::  cancel_semigroup_add
  by standard (simp_all add: movec_eq_iff)

instance movec ::  cancel_ab_semigroup_add
  by standard (simp_all add: movec_eq_iff diff_diff_eq)

instance movec :: cancel_comm_monoid_add ..

instance movec ::  group_add
  apply standard
  using zero_movec_def movec_eq_iff by auto

instance movec ::  ab_group_add
  by standard (simp_all add: movec_eq_iff)


subsection\<open>Basic componentwise operations on movectors\<close>

instantiation movec :: times
begin

definition "( * ) \<equiv> (\<lambda> x y.  vec_lambda (\<lambda> i. (vec_nth x i) * (vec_nth y i)))"
instance ..

end

instantiation movec ::  one
begin

definition "1 \<equiv> vec_lambda (\<lambda> i. 1)"
instance ..

end

instantiation movec ::  ord
begin

definition "x \<le> y \<longleftrightarrow> (\<forall>i. vec_nth x i \<le> vec_nth y i)"
definition "x < (y::movec) \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
instance ..

end

text\<open>The ordering on one-dimensional movectors is linear.\<close>
(*
class cart_one =
  assumes UNIV_one: "card (UNIV :: 'a set) = Suc 0"
begin

subclass linorder
proof
  from UNIV_one show "finite (UNIV :: 'a set)"
    using card_infinite by force
qed

end

instance movec:: (order) order
  by standard (auto simp: less_eq_movec_def less_movec_def movec_eq_iff
      intro: order.trans order.antisym order.strict_implies_order)

instance movec :: (linorder, cart_one) linorder
proof
  obtain a :: 'b where all: "\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a"
  proof -
    have "card (UNIV :: 'b set) = Suc 0" by (rule UNIV_one)
    then obtain b :: 'b where "UNIV = {b}" by (auto iff: card_Suc_eq)
    then have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P b" by auto
    then show thesis by (auto intro: that)
  qed
  fix x y :: "'a^'b::cart_one"
  note [simp] = less_eq_movec_def less_movec_def all movec_eq_iff field_simps
  show "x \<le> y \<or> y \<le> x" by auto
qed
*)
text\<open>Constant Vectors\<close>

definition "movec x = vec_lambda (\<lambda> i. x)"

text\<open>Also the scalar-movector multiplication.\<close>

definition movector_scalar_mult:: "real \<Rightarrow> movec \<Rightarrow> movec" (infixl "*s" 70)
  where "c *s x = vec_lambda (\<lambda> i. c * (vec_nth x i))"

text \<open>scalar product\<close>

definition scalar_product :: "movec \<Rightarrow> movec \<Rightarrow> real" where
  "scalar_product v w = (\<Sum> i \<in> UNIV. vec_nth v i * vec_nth w i)"


subsection \<open>Real movector space\<close>

instantiation movec ::  real_vector
begin

definition "scaleR \<equiv> (\<lambda> r x. vec_lambda (\<lambda> i. scaleR r (vec_nth x i)))"

lemma scalein: "(\<lambda> i. scaleR r (vec_nth x i))\<in>{f. \<exists>k. \<forall>q>k. f q = 0}"
  by (smt mem_Collect_eq movec.vec_lambda_cases movec.vec_lambda_inverse scale_zero_right)

lemma movector_scaleR_component [simp]: "vec_nth (scaleR r x) i = scaleR r (vec_nth x i)"
  unfolding scaleR_movec_def scalein by (smt mem_Collect_eq movec.vec_lambda_inverse movec.vec_nth scale_zero_right) 

instance
  by standard (simp_all add: movec_eq_iff algebra_simps)
end


subsection \<open>Inner product space\<close>



definition "minner x y = sum (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) 
{q. vec_nth x q \<noteq> 0 \<and> vec_nth y q \<noteq> 0}"

lemma minner_scale: "minner (scaleR r x) y = r * minner x y"
  proof (cases "r = 0")
    case True
    then show ?thesis unfolding minner_def
      by simp 
  next
    case False
    then have "{q. movec.vec_nth (r *\<^sub>R x) q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}
      = {q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}" by simp 
    then show ?thesis unfolding minner_def
      using movector_scaleR_component sum_distrib_left inner_scaleR_left sum.cong by smt
  qed

lemma findef: "finite {q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}"
   using movec.vec_nth infinite_nat_iff_unbounded by fastforce

lemma minner_comm: "minner x y = minner y x"
    unfolding minner_def
    using findef inner_commute sum.cong Collect_cong by smt

lemma anotin: "a\<notin>{q. vec_nth x q \<noteq> 0 \<and> vec_nth y q \<noteq> 0} \<Longrightarrow> (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) a = 0"
  by simp


lemma minner_distrib: "minner (x + y) z = minner x z + minner y z"
proof -
  let ?A = "{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}
\<union>{q. movec.vec_nth y q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}
\<union>{q. movec.vec_nth (x+y) q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}"
  have fina: "finite ?A" using findef by blast
  have f1: "(\<Sum>i\<in>?A. movec.vec_nth x i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth x i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left 
    by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge1)
have f2: "(\<Sum>i\<in>?A. movec.vec_nth y i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth y q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth y i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left 
  by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge1)  
have f3: "(\<Sum>i\<in>?A. movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth (x+y) q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left  
  by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge2)
  have f4: "(\<Sum>i\<in>?A. movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>?A. movec.vec_nth x i \<bullet> movec.vec_nth z i)
      + (\<Sum>i\<in>?A. movec.vec_nth y i \<bullet> movec.vec_nth z i)"
    using inner_add_left sum.distrib[of "(\<lambda>i. movec.vec_nth x i \<bullet> movec.vec_nth z i)" "(\<lambda>i. movec.vec_nth y i \<bullet> movec.vec_nth z i)" ?A]
    by (metis (no_types, lifting) movector_add_component sum.cong)
  
    show ?thesis
    unfolding minner_def
    using f1 f2 f3 f4 by simp
qed

lemma minner_sum: "finite A \<Longrightarrow> A \<subseteq> UNIV \<Longrightarrow> minner y (sum f A) = sum (\<lambda>x. minner y (f x)) A"
proof (induct A rule: finite_subset_induct)
  case empty
  then show ?case
    by (metis add.right_neutral add_left_cancel minner_comm minner_distrib sum_clauses(1))
next
  case (insert a F)
  then show ?case
    using minner_comm minner_distrib by auto
qed

(*

instantiation movec :: real_inner
begin
(*
definition transformover :: "movec \<Rightarrow> movec" where
 "transformover x = (let k = Min {k. vec_nth x k \<noteq> 0} in vec_lambda (\<lambda>i. (if i = 0 then vec_nth x k else 0)))"

definition transformover2 :: "movec \<Rightarrow> real" where
 "transformover2 x = (let k = Min {k. vec_nth x k \<noteq> 0} in vec_nth x k)"


definition "inner x y = (if (\<exists> k. \<forall> q>k. vec_nth x q = 0 \<and> vec_nth y q = 0) 
then sum (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) {0..(SOME k.\<forall> q>k. vec_nth x q = 0 \<and> vec_nth y q = 0)}
 else inner (transformover2 x) (transformover2 y))"

definition "inner x y = sum (\<lambda>i. (vec_nth x i) * (vec_nth y i)) 
{0..(SOME k.\<forall> q>k. vec_nth x q = 0 \<and> vec_nth y q = 0)}"*)

definition "inner x y = sum (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) 
{q. vec_nth x q \<noteq> 0 \<and> vec_nth y q \<noteq> 0}"

(*definition "inner x y = sum (\<lambda>i. (vec_nth x i) * (vec_nth y i)) UNIV"*)
lemma findef: "finite {q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}"
   using movec.vec_nth infinite_nat_iff_unbounded by fastforce

lemma anotin: "a\<notin>{q. vec_nth x q \<noteq> 0 \<and> vec_nth y q \<noteq> 0} \<Longrightarrow> (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) a = 0"
  by simp

definition "norm x = L2_set (\<lambda>i. norm (vec_nth x i)) {q. vec_nth x q \<noteq> 0}"


instance proof
  fix r :: real and x y z :: "movec"
  
  show "inner x y = inner y x" 
    unfolding inner_movec_def
    using findef inner_commute sum.cong Collect_cong by smt
    

  (*proof(cases "(\<exists> k. \<forall> q>k. vec_nth x q = 0 \<and> vec_nth y q = 0)")
    case True
    then show ?thesis
      by (auto simp add: inner_commute inner_movec_def HOL.conj_comms(1))

  next
    case False
    then show ?thesis sorry
  qed
  proof -
    obtain nn :: "real \<Rightarrow> nat" where
      f1: "\<forall>r. r < real (nn r)"
      using reals_Archimedean2 by moura
    have "\<forall>m. \<exists>n. \<forall>na>n. movec.vec_nth m na = 0"
      using movec.vec_nth by auto
    then show "(\<Sum>n = 0..SOME n. \<forall>na>n. movec.vec_nth x na = 0 \<and> movec.vec_nth y na = 0. movec.vec_nth x n * movec.vec_nth y n) = (\<Sum>n = 0..SOME n. \<forall>na>n. movec.vec_nth y na = 0 \<and> movec.vec_nth x na = 0. movec.vec_nth y n * movec.vec_nth x n)"
      using f1 by (metis (full_types, lifting) less_numeral_extra(3) movec_def movec_lambda_beta of_nat_less_iff)
  qed *)
  let ?A = "{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}
\<union>{q. movec.vec_nth y q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}
\<union>{q. movec.vec_nth (x+y) q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}"
  have fina: "finite ?A" using findef by blast
  have f1: "(\<Sum>i\<in>?A. movec.vec_nth x i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth x i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left 
    by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge1)
have f2: "(\<Sum>i\<in>?A. movec.vec_nth y i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth y q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth y i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left 
  by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge1)  
have f3: "(\<Sum>i\<in>?A. movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>{q. movec.vec_nth (x+y) q \<noteq> 0 \<and> movec.vec_nth z q \<noteq> 0}.
       movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)" using fina anotin sum.mono_neutral_left  
  by (metis (no_types, lifting) DiffE le_sup_iff mem_Collect_eq sup_ge2)
  have f4: "(\<Sum>i\<in>?A. movec.vec_nth (x+y) i \<bullet> movec.vec_nth z i)
      = (\<Sum>i\<in>?A. movec.vec_nth x i \<bullet> movec.vec_nth z i)
      + (\<Sum>i\<in>?A. movec.vec_nth y i \<bullet> movec.vec_nth z i)"
    using inner_add_left sum.distrib[of "(\<lambda>i. movec.vec_nth x i \<bullet> movec.vec_nth z i)" "(\<lambda>i. movec.vec_nth y i \<bullet> movec.vec_nth z i)" ?A]
    by (metis (no_types, lifting) movector_add_component sum.cong)
  
    show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_movec_def
    using f1 f2 f3 f4 by simp
  show "inner (scaleR r x) y = r * inner x y"
  proof (cases "r = 0")
    case True
    then show ?thesis unfolding inner_movec_def
      by simp 
  next
    case False
    then have "{q. movec.vec_nth (r *\<^sub>R x) q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}
      = {q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth y q \<noteq> 0}" by simp 
    then show ?thesis unfolding inner_movec_def
      using movector_scaleR_component sum_distrib_left inner_scaleR_left sum.cong by smt
  qed
  show "0 \<le> inner x x"
    unfolding inner_movec_def
    by (simp add: sum_nonneg)
  have f5: "(\<forall>i. i \<in> {q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth x q \<noteq> 0}
     \<longrightarrow> 0 < movec.vec_nth x i \<bullet> movec.vec_nth x i)"
    using inner_gt_zero_iff by blast
  show "inner x x = 0 \<longleftrightarrow> x = 0"
  proof(cases "x=0")
    case True
    then show ?thesis using inner_movec_def
      by simp
  next
    case c1: False
    then have "{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth x q \<noteq> 0} \<noteq> {}"
      by (simp add: movec_eq_iff)
    then have "inner x x > 0" unfolding inner_movec_def using f5 findef sum_pos
      by (metis (no_types, lifting) Collect_cong) 
    then show ?thesis using c1 by auto
  qed
 (*unfolding inner_movec_def
  using movec_eq_iff findef 
    sum_nonneg_eq_0_iff[of "{q. movec.vec_nth x q \<noteq> 0 \<and> movec.vec_nth x q \<noteq> 0}" "(\<lambda>i. movec.vec_nth x i \<bullet> movec.vec_nth x i)"]  
  zero_index   by (simp add: movec_eq_iff sum_nonneg_eq_0_iff)
  proof -
    obtain k where "\<forall>q>k. vec_nth x q = 0"
      using movec.vec_nth by auto
    then have "sum (\<lambda>i. (vec_nth x i) * (vec_nth y i)) UNIV
             = sum (\<lambda>i. (vec_nth x i) * (vec_nth y i)) {0..k}"
      using VCDim4.zero_index lessI mem_Collect_eq movec.vec_lambda_inverse movec.vec_nth movec_lambda_beta movec_lambda_unique 

   *)
  show "norm x = sqrt (inner x x)"
    unfolding inner_movec_def norm_movec_def L2_set_def
    by (metis (no_types, lifting) Collect_cong power2_norm_eq_inner sum.cong)
  
qed

end
*)
(*

instantiation movec :: (real_vector, linorder) real_vector
begin
definition "scaleR \<equiv> (\<lambda> r x. vec_lambda (\<lambda> i. scaleR r (vec_nth x i)))"
instance
proof
  fix f1 f2 f3::"('a,'b)movec"
  fix i::'b
  show "vec_nth f1 i + vec_nth f2 i + vec_nth f3 i = vec_nth f1 i + (vec_nth f2 i + vec_nth f3 i)"

end


datatype  ('a, 'b ) myvec  = Supa "('a \<Rightarrow> 'b) set"

instantiation movec :: uminus
begin
definition "uminus \<equiv> (\<lambda> f x. - f x)"

instance ..
end

instantiation mivec :: real_vector
begin
  (*definition "uminus \<equiv> (\<lambda> f x. - f x)"*)
definition "scaleR \<equiv> (\<lambda> (r::real) (f::nat\<Rightarrow>real) i::nat. scaleR r (f i))"

instance
  apply standard
end

instantiation myvec :: (real_vector,real_vector)real_vector
begin                             

end

term vector_space

locale daba = fixes d::nat
begin

typedef limnat = "{a :: nat. a < 10}"
  by (meson mem_Collect_eq numeral_less_iff semiring_norm(76))

setup_lifting type_definition_limnat

class testi =
  fixes sizi :: "type \<Rightarrow> nat"

instantiation limnat :: finite
begin

end

instance limnat :: finite
proof
  have "(UNIV::limnat set) = image Abs_limnat {a :: nat. a < 10}"
    using type_definition.univ type_definition_limnat by blast
  moreover have "finite {a :: nat. a < 10}" by blast
  ultimately show "finite (UNIV::limnat set)" by (metis finite_imageI)
qed

end
*)

lemma exmovec: "\<exists>v::movec. (\<forall>k<d. vec_nth v k = f k) \<and> v \<in> {x. \<forall>q\<ge>d. vec_nth x q = 0}"
proof -
      have "(\<lambda>x. (if x<d then f x else 0)) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
      proof
        have "\<forall>q>d. (if q < d then f q else 0) = 0" by auto
        then show "\<exists>j. \<forall>q>j. (if q < d then f q else 0) = 0" by blast
      qed
      then obtain v where o: "vec_nth v = (\<lambda>x. (if x<d then f x else 0))"
        by (metis (no_types, lifting) movec.vec_nth_cases)
      then have "(\<forall>k<d. movec.vec_nth v k = f k)" by auto
      moreover have "\<forall>q\<ge>d. vec_nth v q = 0"
        using o by simp 
      ultimately show ?thesis by auto
qed


definition "linear_predictor w = (\<lambda>x. minner w x > 0)"

definition "all_linear V = image linear_predictor V"

term vector_space

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
        shows "\<not> shatters (image mapify (all_linear V)) B {True, False}"
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


lemma vec_sum: "finite A \<Longrightarrow> vec_nth (sum f A) i = sum (\<lambda>v. vec_nth (f v) i) A"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case using movector_add_component
    by simp
qed



lemma "span {x. \<forall>q\<ge>d. movec.vec_nth x q = 0} \<subseteq> {x. \<forall>q\<ge>d. movec.vec_nth x q = 0}"
proof
  let ?A = "{x. \<forall>q\<ge>d. movec.vec_nth x q = 0}"
  fix x
  assume a1: "x \<in> span {x. \<forall>q\<ge>d. movec.vec_nth x q = 0}"
  have "\<forall>y\<in>?A. \<forall>q\<ge>d. vec_nth y q = 0" by auto
  then have "\<forall>r. \<forall>y\<in>?A. \<forall>q\<ge>d. vec_nth (scaleR (r y) y) q = 0" by auto
  then have "\<forall>r. \<forall>t\<subseteq>?A. \<forall>q\<ge>d. finite t \<longrightarrow> (\<Sum>a\<in>t. vec_nth (scaleR (r a) a) q) = 0"
    by (meson subsetCE sum.neutral) 
  then have "\<forall>r. \<forall>t\<subseteq>?A. \<forall>q\<ge>d. finite t \<longrightarrow> vec_nth (\<Sum>a\<in>t. scaleR (r a) a) q = 0" 
    by (simp add: vec_sum)
  then have "\<forall>q\<ge>d. vec_nth x q = 0" using a1 span_alt
        proof -
      { fix nn :: nat
        have ff1: "\<And>m M. (m::movec) \<notin> span M \<or> (\<exists>f. m = (\<Sum>m | f m \<noteq> 0. f m *\<^sub>R m) \<and> {m. f m \<noteq> 0} \<subseteq> M \<and> finite {m. f m \<noteq> 0})"
      using span_alt by auto
        { assume "movec.vec_nth x nn \<noteq> 0"
          then have "\<exists>m. m \<in> span {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> movec.vec_nth m nn \<noteq> 0"
            using a1 by blast
          then have "\<exists>m. (\<exists>f. m = (\<Sum>m | f m \<noteq> 0. f m *\<^sub>R m) \<and> {m. f m \<noteq> 0} \<subseteq> {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> finite {m. f m \<noteq> 0}) \<and> m \<in> span {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> movec.vec_nth m nn \<noteq> 0"
            using ff1 by meson
          then have "\<not> d \<le> nn \<or> movec.vec_nth x nn = 0"
            using \<open>\<forall>r t. t \<subseteq> {x. \<forall>q\<ge>d. movec.vec_nth x q = 0} \<longrightarrow> (\<forall>q\<ge>d. finite t \<longrightarrow> movec.vec_nth (\<Sum>a\<in>t. r a *\<^sub>R a) q = 0)\<close> by blast }
        then have "\<not> d \<le> nn \<or> movec.vec_nth x nn = 0"
          by blast }
      then show ?thesis
        by blast
      qed 
   then show "x \<in> {x. \<forall>q\<ge>d. movec.vec_nth x q = 0}" by auto
qed


lemma fixes V::"(movec) set"
  assumes "V = {x. \<forall>q\<ge>d. vec_nth x q = 0}"
  shows "\<exists>B. card B = d \<and> B \<subseteq> V \<and> shatters (image mapify (all_linear V)) B {True, False}"
  and "dim V = d"
proof -
  let ?B = "(image (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0)) {..<d})"
  have f1: "\<forall>(k::nat). (\<lambda>i. if i = k then 1 else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
     by auto
  then have "\<forall>k j. k = j \<longleftrightarrow> vec_lambda (\<lambda>i. if i = k then 1 else 0) = vec_lambda (\<lambda>i. if i = j then 1 else 0)"
    using fun_eq_iff movec.vec_lambda_inject by smt
  then have "inj (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0))" by (meson injI) 
  then have "card ?B = d"
    by (metis (no_types, lifting) card_image card_lessThan injD inj_on_def)
  moreover have "?B \<subseteq> V" using assms f1
    by (smt image_subset_iff leD lessThan_iff mem_Collect_eq movec.vec_lambda_inverse) 
  moreover have "(\<forall>m\<in>(allmaps ?B {True, False}).\<exists>h\<in>(image mapify (all_linear V)). m \<subseteq>\<^sub>m h)"
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
    obtain w where o0: "\<forall>k<d. vec_nth w k = (?v \<circ> m \<circ> (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0))) k" "w\<in>V"
      using exmovec assms by blast
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
            have f2: "m \<in> (if (\<lambda>n. movec.vec_lambda (\<lambda>na. if na = n then 1 else 0)) ` {..<d} = {} then {} else {f. dom f = (\<lambda>n. movec.vec_lambda (\<lambda>na. if na = n then 1 else 0)) ` {..<d} \<and> ran f \<subseteq> {True, False}})"
              using a1 allmaps_def by blast
              have f3: "\<forall>F f. F \<noteq> {} \<or> (f::movec \<Rightarrow> bool option) \<notin> F"
                by blast
              have "\<forall>M B f. (f \<in> {f. dom f = (M::movec set) \<and> ran f \<subseteq> (B::bool set)}) = (dom f = M \<and> ran f \<subseteq> B)"
                by simp
              then have "mapify (linear_predictor w) \<in> Collect ((\<subseteq>\<^sub>m) m)"
                using f3 f2 f1 \<open>\<forall>x\<in>(\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) ` {..<d}. mapify (linear_predictor w) x = m x\<close> by presburger
              then show ?thesis
                by blast
            qed 
            moreover have "mapify (linear_predictor w) \<in> (image mapify (all_linear V))"
              using o0(2) all_linear_def by blast
            ultimately show "\<exists>h\<in>(image mapify (all_linear V)). m \<subseteq>\<^sub>m h" by auto
          qed
          ultimately show "\<exists>B. card B = d \<and> B \<subseteq> V \<and> shatters (image mapify (all_linear V)) B {True, False}"
            using alt_shatters by blast


          have "V \<subseteq> span ?B" unfolding assms
            apply rule
          proof(induct d)
            case 0
            have "{x. \<forall>q\<ge>0. movec.vec_nth x q = 0} = {0}" using movec_eq_iff zero_index by auto
            then show ?case using span_empty "0.prems" by auto
            next
              case c1: (Suc d)
              then have a1: "x\<in>{x. \<forall>q\<ge>Suc d. movec.vec_nth x q = 0}" by auto
              then obtain y where o1: "y\<in>{x. \<forall>q\<ge>d. movec.vec_nth x q = 0}" "\<forall>q<d. vec_nth y q = vec_nth x q"
                using exmovec[of d "vec_nth x"] by auto

              then have f20: "\<forall>q\<noteq>d. vec_nth (x - y) q = 0" using a1 movector_minus_component
                by (smt less_SucE mem_Collect_eq not_le)
               have f21: "vec_nth (x - y) d = vec_nth x d" using o1 movector_minus_component by auto
             
               let ?r = "vec_nth x d"
               let ?vd = "(vec_lambda (\<lambda>i. if i = d then 1 else 0))"
              
               have f22: "vec_nth (scaleR ?r ?vd) d = scaleR ?r 1"
                using f1 movector_scaleR_component movec.vec_lambda_inverse[of "(\<lambda>n. if n = d then 1 else 0)"]
                by force 
              have f23: "\<forall>q\<noteq>d. vec_nth (scaleR ?r ?vd) q = 0"
                using f1 movec.vec_lambda_inverse[of "(\<lambda>n. if n = d then 1 else 0)"]
                by force
               have "\<forall>i. movec.vec_nth (x - y) i = movec.vec_nth (scaleR ?r ?vd) i"
               proof
                 fix i
                 show "movec.vec_nth (x - y) i = movec.vec_nth (scaleR ?r ?vd) i"
                   apply (cases "i=d")
                   using f21 f22 f20 f23 by auto
               qed     
              then have "x - y = scaleR ?r ?vd"
                using movec_eq_iff by auto
              then have f30: "x = y + scaleR ?r ?vd"
                by (metis add.commute diff_add_cancel)
              let ?SucB = "(\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) ` {..<(Suc d)}"
              let ?oldB = "(\<lambda>k. movec.vec_lambda (\<lambda>i. if i = k then 1 else 0)) ` {..<d}"
              have "?vd \<in> ?SucB"
                by auto
              then have f31: "?vd \<in> span ?SucB"
                by (simp add: span_base)
              have "y\<in> span ?oldB" using o1 c1 by auto
              moreover have "span ?oldB \<subseteq> span ?SucB"
                by (meson le_Suc_eq le_eq_less_or_eq lessThan_subset_iff span_mono subset_image_iff)
              ultimately have "y \<in> span ?SucB" by auto
              then show ?case using f30 f31 span_mul span_add by metis       
            qed

            have "span ?B \<subseteq> V"
            proof
            fix x
            assume a1: "x \<in> span ?B"
            have "\<forall>y\<in>?B. \<forall>q\<ge>d. vec_nth y q = 0"
              using \<open>?B \<subseteq> V\<close> assms by blast
            then have "\<forall>r. \<forall>y\<in>?B. \<forall>q\<ge>d. vec_nth (scaleR (r y) y) q = 0" by auto
            then have "\<forall>r. \<forall>t\<subseteq>?B. \<forall>q\<ge>d. finite t \<longrightarrow> (\<Sum>a\<in>t. vec_nth (scaleR (r a) a) q) = 0"
              by (meson subsetCE sum.neutral) 
            then have "\<forall>r. \<forall>t\<subseteq>?B. \<forall>q\<ge>d. finite t \<longrightarrow> vec_nth (\<Sum>a\<in>t. scaleR (r a) a) q = 0" 
              by (simp add: vec_sum)
            then have "\<forall>q\<ge>d. vec_nth x q = 0" using a1 span_alt 
                  proof -
                { fix nn :: nat
                  have ff1: "\<And>m M. (m::movec) \<notin> span M \<or> (\<exists>f. m = (\<Sum>m | f m \<noteq> 0. f m *\<^sub>R m) \<and> {m. f m \<noteq> 0} \<subseteq> M \<and> finite {m. f m \<noteq> 0})"
                using span_alt by auto
                  { assume "movec.vec_nth x nn \<noteq> 0"
                    then have "\<exists>m. m \<in> span {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> movec.vec_nth m nn \<noteq> 0"
                      using a1 by blast
                    then have "\<exists>m. (\<exists>f. m = (\<Sum>m | f m \<noteq> 0. f m *\<^sub>R m) \<and> {m. f m \<noteq> 0} \<subseteq> {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> finite {m. f m \<noteq> 0}) \<and> m \<in> span {m. \<forall>n\<ge>d. movec.vec_nth m n = 0} \<and> movec.vec_nth m nn \<noteq> 0"
                      using ff1 by meson
                    then have "\<not> d \<le> nn \<or> movec.vec_nth x nn = 0"
                      using \<open>\<forall>r t. t \<subseteq> {x. \<forall>q\<ge>d. movec.vec_nth x q = 0} \<longrightarrow> (\<forall>q\<ge>d. finite t \<longrightarrow> movec.vec_nth (\<Sum>a\<in>t. r a *\<^sub>R a) q = 0)\<close> by blast }
                  then have "\<not> d \<le> nn \<or> movec.vec_nth x nn = 0"
                    by blast }
                then show ?thesis
                  by blast
                qed 
             then show "x \<in> {x. \<forall>q\<ge>d. movec.vec_nth x q = 0}" by auto
          qed

          have "independent ?B" unfolding 
 qed

 term module

lemma "dim {x. \<forall>q\<ge>d. movec.vec_nth x q = 0} = d" oops

locale vcd =
  fixes X :: "'a set"
    and Y :: "'b set"
    and H :: "('a \<Rightarrow> 'b) set"
assumes infx: "infinite X"
    and cardY: "card Y = 2"
    and Hdef: "\<forall>h x. h\<in>H \<longrightarrow> h x \<in> Y"
    and nonemptyH: "H \<noteq> {}"
begin

lemma "X \<noteq> {}" using infx by auto

abbreviation "H_map \<equiv> image mapify H"

lemma ranh: "\<forall>h\<in>H_map. ran h \<subseteq> Y" using Hdef mapify_def
  by (smt imageE mem_Collect_eq option.simps(1) ran_def subset_iff)

lemma domh: "\<forall>h\<in>H_map. dom h = UNIV"
  by (simp add: mapify_def) 

definition "VCDim = (if finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} then Some (Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}) else None)"

definition "growth m = Max {k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m}"

lemma "{k. \<exists>C\<subseteq>X. k = card (restrictH H_map C Y) \<and> card C = m} \<noteq> {}"
  by (smt Collect_empty_eq_bot bot_empty_eq empty_iff infinite_arbitrarily_large infx)
  
lemma assumes "VCDim = Some m" 
  shows "(\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y)"
   and noshatter: "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"
proof -
  have s1: "m = Max {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.discI option.inject)
  moreover have s2: "finite {m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y}" using VCDim_def assms
    by (metis (mono_tags, lifting) Collect_cong option.simps(3))
   moreover have "{m. \<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y} \<noteq> {}"
    using empty_shatted by fastforce
  ultimately show "\<exists>C\<subseteq>X. card C = m \<and> shatters H_map C Y" using Max_in by auto
  show "\<not>(\<exists>C\<subseteq>X. card C > m \<and> shatters H_map C Y)"
    by (metis (mono_tags, lifting) Max_ge leD mem_Collect_eq s1 s2)
qed
  

(*Equation 6.3*)
lemma eq63: "finite C \<Longrightarrow> card (restrictH H_map C Y) \<le> card ({B. B\<subseteq>C \<and> shatters H_map B Y})"
proof (induct rule: finite.induct)
  case emptyI
  then show ?case by (simp add: allmaps_def restrictH_def)
next
  case (insertI A a)
  then show ?case sorry
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
    by (metis (mono_tags, lifting) Collect_cong dual_order.strict_trans1 neq_iff not_le_imp_less)
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
  obtain h where f3: "h\<in>H_map" using nonemptyH by auto
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


text \<open>Definition of the Prediction Error (2.1). 
    This is the Isabelle way to write: 
      @{text "L\<^sub>D\<^sub>,\<^sub>f(h) =  D({S. f S \<noteq> h S})"} \<close>
definition PredErr :: "'a pmf \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "PredErr D f h = measure_pmf.prob D {S. f S \<noteq> h S}" 

lemma PredErr_alt: "PredErr D f h = measure_pmf.prob D {S\<in>set_pmf D.  f S \<noteq> h S}"
  unfolding PredErr_def apply(rule pmf_prob_cong) by (auto simp add: set_pmf_iff) 

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
    shows aux33: "measure_pmf.prob (Samples m D f) {S. \<forall>h\<in>H. abs(PredErr D f h - TrainErr S {0..<m} h) \<le> (4+sqrt(ln(real(growth (2*m)))))/(\<delta> * sqrt(2*m))} \<ge> 1 - \<delta>"
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
    using assms aux33 by auto
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



definition ERM :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "ERM S n = {h. is_arg_min (TrainErr S {0..<n}) (\<lambda>s. s\<in>H) h}"

definition ERMe :: "(nat \<Rightarrow> ('a \<times> 'b)) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "ERMe S n = (SOME h. h\<in> ERM S n)"

lemma ERM_subset: "ERM S n \<subseteq> H" 
  by (simp add: is_arg_min_linorder subset_iff ERM_def)

lemma TrainErr_nn: "TrainErr S I h \<ge> 0"
proof -
  have "0 \<le> (\<Sum>i\<in>I. 0::real)" by simp
  also have "\<dots> \<le> (\<Sum>i\<in>I. case S i of (x, y) \<Rightarrow> if h x \<noteq> y then 1 else 0)"
    apply(rule sum_mono) by (simp add: split_beta') 
  finally show ?thesis 
    unfolding TrainErr_def by auto
qed

lemma ERM_0_in: "h' \<in> H \<Longrightarrow> TrainErr S {0..<n} h' = 0 \<Longrightarrow> h' \<in>ERM S n"
  unfolding ERM_def by (simp add: TrainErr_nn is_arg_min_linorder)


definition PAC_learnable :: "((nat \<Rightarrow> 'a \<times> 'b) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool" where
  "PAC_learnable L = (\<exists>M::(real \<Rightarrow> real \<Rightarrow> nat). 
            (\<forall>D f. set_pmf D \<subseteq> X \<longrightarrow> f ` X = Y \<longrightarrow> (\<exists>h'\<in>H. PredErr D f h' = 0) \<longrightarrow> (\<forall>m. \<forall> \<epsilon> > 0. \<forall>\<delta>\<in>{x.0<x\<and>x<1}. m \<ge> M \<epsilon> \<delta> \<longrightarrow> 
          measure_pmf.prob (Samples m D f) {S. PredErr D f (L S m) \<le> \<epsilon>} \<ge> 1 - \<delta>)))"

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