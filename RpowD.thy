theory RpowD
  imports "HOL-Analysis.Analysis"
begin

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

lemma minner_alt: "finite A \<Longrightarrow> {q. vec_nth x q \<noteq> 0 \<and> vec_nth y q \<noteq> 0} \<subseteq> A
       \<Longrightarrow> minner x y = sum (\<lambda>i. inner (vec_nth x i) (vec_nth y i)) A"
  by (metis (no_types, lifting) Collect_cong DiffE anotin minner_def sum.mono_neutral_cong_left)
    

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

lemma le_valid: "(\<lambda>i. if i \<le> (k::nat) then f i else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
  using leD by auto
  
lemma lt_valid: "(\<lambda>i. if i < (k::nat) then f i else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
  using not_less_iff_gr_or_eq by auto
     
lemma eq_valid: "(\<lambda>i. if i = (k::nat) then f i else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
  by auto


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


lemma vec_sum: "finite A \<Longrightarrow> vec_nth (sum f A) i = sum (\<lambda>v. vec_nth (f v) i) A"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case using movector_add_component
    by simp
qed





(*not needed*)
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

definition myroom :: "nat \<Rightarrow> movec set" where
    "myroom d = {x. \<forall>q\<ge>d. vec_nth x q = 0}"

definition unit_vec :: "nat \<Rightarrow> movec" where
    "unit_vec d = vec_lambda (\<lambda>i. if i = d then 1 else 0)"

definition mybasis :: "nat \<Rightarrow> movec set" where
    "mybasis d = image (\<lambda>k. unit_vec k) {..<d}"


lemma roomSpan: "myroom d = span (mybasis d)"
proof -
  have f1: "\<forall>(k::nat). (\<lambda>i. if i = k then 1 else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
    by auto
  have "(mybasis d) \<subseteq> myroom d" using f1 myroom_def mybasis_def unit_vec_def
    by (smt image_subset_iff leD lessThan_iff mem_Collect_eq movec.vec_lambda_inverse) 

  have "myroom d \<subseteq> span (mybasis d)"
    apply rule
  proof(induct d)
    case 0
    have "{x. \<forall>q\<ge>0. movec.vec_nth x q = 0} = {0}" using movec_eq_iff zero_index by auto
    then show ?case using span_empty "0.prems" myroom_def mybasis_def  by auto
    next
      case c1: (Suc d)
      then have a1: "x\<in>{x. \<forall>q\<ge>Suc d. movec.vec_nth x q = 0}" using myroom_def by auto
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
      have "?vd \<in> mybasis (Suc d)" using mybasis_def unit_vec_def
        by auto
      then have f31: "?vd \<in> span (mybasis (Suc d))"
        by (simp add: span_base)
      have "y\<in> span (mybasis d)" using o1 c1 myroom_def by auto
      moreover have "span (mybasis d) \<subseteq> span (mybasis (Suc d))" using mybasis_def
        by (simp add: image_mono span_mono) 
      ultimately have "y \<in> span (mybasis (Suc d))" by auto
      then show ?case using f30 f31 span_mul span_add by metis       
    qed

    moreover have "span (mybasis d) \<subseteq> myroom d"
    proof
    fix x
    assume a1: "x \<in> span (mybasis d)"
    have "\<forall>y\<in>(mybasis d). \<forall>q\<ge>d. vec_nth y q = 0"
      using \<open>(mybasis d) \<subseteq> myroom d\<close>
      by (simp add: myroom_def subset_eq)
    then have "\<forall>r. \<forall>y\<in>(mybasis d). \<forall>q\<ge>d. vec_nth (scaleR (r y) y) q = 0" by auto
    then have "\<forall>r. \<forall>t\<subseteq>(mybasis d). \<forall>q\<ge>d. finite t \<longrightarrow> (\<Sum>a\<in>t. vec_nth (scaleR (r a) a) q) = 0"
      by (meson subsetCE sum.neutral) 
    then have "\<forall>r. \<forall>t\<subseteq>(mybasis d). \<forall>q\<ge>d. finite t \<longrightarrow> vec_nth (\<Sum>a\<in>t. scaleR (r a) a) q = 0" 
      by (simp add: vec_sum)
    then have "\<forall>q\<ge>d. vec_nth x q = 0" using a1 span_alt
      by (smt mem_Collect_eq) 
     then show "x \<in> myroom d" using myroom_def  by auto
   qed

   ultimately show ?thesis by auto

 qed


lemma indbasis: "independent (mybasis d)"
proof(induct d)
 case 0
 then show ?case using independent_empty mybasis_def by auto
next
  case c1: (Suc d)
  have "unit_vec d \<notin> myroom d" using myroom_def unit_vec_def vec_lambda_inverse[of "(\<lambda>i. if i = d then 1 else 0)"] by fastforce
  then have "unit_vec d \<notin> span (mybasis d)" using roomSpan by auto
  moreover have "mybasis (Suc d) = insert (unit_vec d) (mybasis d)" using mybasis_def
    by (simp add: lessThan_Suc) 
  ultimately show ?case using independent_insertI c1 by auto
qed

lemma cardbasis: "card (mybasis d) = d"
proof -
  have f1: "\<forall>(k::nat). (\<lambda>i. if i = k then 1 else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}"
    by auto
  then have "\<forall>k j. k = j \<longleftrightarrow> vec_lambda (\<lambda>i. if i = k then 1 else 0) = vec_lambda (\<lambda>i. if i = j then 1 else 0)"
    using fun_eq_iff movec.vec_lambda_inject by smt
  then have "inj (\<lambda>k. vec_lambda (\<lambda>i. if i = k then 1 else 0))" by (meson injI) 
  then show ?thesis using mybasis_def unit_vec_def
    by (metis (no_types, lifting) card_image card_lessThan injD inj_on_def)
qed

lemma dim_room: "dim (myroom d) = d" using cardbasis indbasis roomSpan
  by (simp add: dim_eq_card_independent) 

lemma infiniteroom: "d > 0 \<Longrightarrow> infinite (myroom d)"
proof -
  fix d::nat
  assume  "d > 0"
  let ?f = "(\<lambda>x. vec_lambda (\<lambda>i. if i = 0 then x else 0))"
  have "\<forall>x::real. (\<lambda>i::nat. if i = 0 then x else 0) \<in> {f. \<exists>j. \<forall>q>j. f q = 0}" 
    by auto
  then have "\<forall>x y. x = y \<longleftrightarrow> ?f x = ?f y"
    using fun_eq_iff movec.vec_lambda_inject by (metis (mono_tags, lifting)) 
  then have "inj ?f" by (meson injI)
  then have f1: "infinite (range ?f)"
    using finite_imageD infinite_UNIV_char_0 by auto
  have "\<forall>x. ?f x \<in> (myroom d)" unfolding myroom_def
    using \<open>0 < d\<close> movec.vec_lambda_inverse by auto 
  then have "range ?f \<subseteq> myroom d" by auto
  from this f1 show "infinite (myroom d)"
    using finite_subset by auto
qed  

fun upd_movec :: "movec \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> movec" where
"upd_movec v i r = vec_lambda (\<lambda>k. if k=i then r else vec_nth v k)"


end