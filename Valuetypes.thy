section\<open>Value Types\<close>

theory Valuetypes
imports ReadShow
begin

fun iter :: "(int \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> int \<Rightarrow> 'b"
where
  "iter f v x = (if x \<le> 0 then v  
                 else f (x-1) (iter f v (x-1)))"

fun iter' :: "(int \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'b \<Rightarrow> int \<Rightarrow> 'b option"
where
  "iter' f v x = (if x \<le> 0 then Some v
                  else case iter' f v (x-1) of
                          Some v' \<Rightarrow> f (x-1) v'
                        | None \<Rightarrow> None)"

type_synonym Address = String.literal
type_synonym Location = String.literal
type_synonym Valuetype = String.literal

datatype Types = TSInt nat
               | TUInt nat
               | TBool
               | TAddr

fun createSInt :: "nat \<Rightarrow> int \<Rightarrow> Valuetype"
where
  "createSInt b v =
    (if v \<ge> 0
      then ShowL\<^sub>i\<^sub>n\<^sub>t (-(2^(b-1)) + (v+2^(b-1)) mod (2^b))
      else ShowL\<^sub>i\<^sub>n\<^sub>t (2^(b-1) - (-v+2^(b-1)-1) mod (2^b) - 1))"

lemma upper_bound:
  fixes b::nat
    and c::int
  assumes "b > 0"
      and "c < 2^(b-1)"
    shows "c + 2^(b-1) < 2^b"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. (\<forall>(c::int)<2^b. (c + 2^b) < 2^(Suc b))" by simp
  show ?thesis using a1[OF b2] assms by simp
qed

lemma upper_bound2:
  fixes b::nat
      and c::int
    assumes "b > 0"
      and "c < 2^b"
      and "c \<ge> 0"
    shows "c - (2^(b-1)) < 2^(b-1)"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. (\<forall>(c::int)<2^(Suc b). c\<ge>0 \<longrightarrow> (c - 2^b) < 2^b)" by simp
  show ?thesis using a1[OF b2] assms by simp
qed

lemma upper_bound3:
  fixes b::nat
    and v::int
      defines "x \<equiv> - (2 ^ (b - 1)) + (v + 2 ^ (b - 1)) mod 2 ^ b"
    assumes "b>0"
    shows "x < 2^(b-1)"
  using upper_bound2 assms by auto

lemma lower_bound:
    fixes b::nat
  assumes "b>0"
    shows "\<forall>(c::int) \<ge> -(2^(b-1)). (-c + 2^(b-1) - 1 < 2^b)"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. \<forall>(c::int) \<ge> -(2^b). (-c + (2^b) - 1) < 2^(Suc b)" by simp
  show ?thesis using a1[OF b2] assms by simp
qed

lemma lower_bound2:
  fixes b::nat
    and v::int
      defines "x \<equiv> 2^(b - 1) - (-v+2^(b-1)-1) mod 2^b - 1"
    assumes "b>0"
    shows "x \<ge> - (2 ^ (b - 1))"
  using upper_bound2 assms by auto

lemma createSInt_id_g0:
    fixes b::nat
      and v::int
  assumes "v \<ge> 0"
      and "v < 2^(b-1)"
      and "b > 0"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v"
proof -
  from assms have "v + 2^(b-1) \<ge> 0" by simp
  moreover from assms have "v + (2^(b-1)) < 2^b" using upper_bound[of b] by auto
  ultimately have "(v + 2^(b-1)) mod (2^b) = v + 2^(b-1)" by simp
  moreover from assms have "createSInt b v=ShowL\<^sub>i\<^sub>n\<^sub>t (-(2^(b-1)) + (v+2^(b-1)) mod (2^b))" by simp
  ultimately show ?thesis by simp
qed

lemma createSInt_id_l0:
    fixes b::nat
      and v::int
  assumes "v < 0"
      and "v \<ge> -(2^(b-1))"
      and "b > 0"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v"
proof -
  from assms have "-v + 2^(b-1) - 1 \<ge> 0" by simp
  moreover from assms have "-v + 2^(b-1) - 1 < 2^b" using lower_bound[of b] by auto 
  ultimately have "(-v + 2^(b-1) - 1) mod (2^b) = (-v + 2^(b-1) - 1)" by simp
  moreover from assms have "createSInt b v= ShowL\<^sub>i\<^sub>n\<^sub>t (2^(b-1) - (-v+2^(b-1)-1) mod (2^b) - 1)" by simp
  ultimately show ?thesis by simp
qed

lemma createSInt_id:
    fixes b::nat
      and v::int
  assumes "v < 2^(b-1)"
      and "v \<ge> -(2^(b-1))"
      and "b > 0"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v" using createSInt_id_g0 createSInt_id_l0 assms by simp

fun createUInt :: "nat \<Rightarrow> int \<Rightarrow> Valuetype"
  where "createUInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t (v mod (2^b))"

lemma createUInt_id:
  assumes "v \<ge> 0"
      and "v < 2^b"
    shows "createUInt b v =  ShowL\<^sub>i\<^sub>n\<^sub>t v"
by (simp add: assms(1) assms(2))

fun createBool :: "bool \<Rightarrow> Valuetype"
where
  "createBool b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b"

fun createAddress :: "Address \<Rightarrow> Valuetype"
where
  "createAddress ad = ad"

fun convert :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "convert (TSInt b1) (TSInt b2) v =
    (if b1 \<le> b2
      then Some (v, TSInt b2)
      else None)"
| "convert (TUInt b1) (TUInt b2) v =
    (if b1 \<le> b2
      then Some (v, TUInt b2)
      else None)"
| "convert (TUInt b1) (TSInt b2) v =
    (if b1 < b2
      then Some (v, TSInt b2)
      else None)"
| "convert TBool TBool v = Some (v, TBool)"
| "convert TAddr TAddr v = Some (v, TAddr)"
| "convert _ _ _ = None"

lemma convert_id[simp]:
  "convert tp tp kv = Some (kv, tp)"
    by (metis Types.exhaust convert.simps(1) convert.simps(2) convert.simps(4) convert.simps(5) order_refl)

fun olift ::
  "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "olift op (TSInt b1) (TSInt b2) v1 v2 =
    Some (createSInt (max b1 b2) (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt (max b1 b2))"
| "olift op (TUInt b1) (TUInt b2) v1 v2 =
    Some (createUInt (max b1 b2) (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TUInt (max b1 b2))"
| "olift op (TSInt b1) (TUInt b2) v1 v2 =
    (if b2 < b1
      then Some (createSInt b1 (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt b1)
      else None)"
| "olift op (TUInt b1) (TSInt b2) v1 v2 =
    (if b1 < b2
      then Some (createSInt b2 (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt b2)
      else None)"
| "olift _ _ _ _ _ = None"

fun plift ::
  "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "plift op (TSInt b1) (TSInt b2) v1 v2 = Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)"
| "plift op (TUInt b1) (TUInt b2) v1 v2 = Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)"
| "plift op (TSInt b1) (TUInt b2) v1 v2 =
    (if b2 < b1
      then Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)
      else None)"
| "plift op (TUInt b1) (TSInt b2) v1 v2 =
    (if b1 < b2
      then Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)
      else None)" 
| "plift _ _ _ _ _ = None"

definition add :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "add = olift (+)"

definition sub :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "sub = olift (-)"

definition equal :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "equal = plift (=)"

definition less :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "less = plift (<)"

declare less_def [solidity_symbex]

definition leq :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "leq = plift (\<le>)"

fun vtand :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "vtand TBool TBool a b =
    (if a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<and> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True then Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)
    else Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool))"
| "vtand _ _ _ _ = None"

fun vtor :: "Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option"
where
  "vtor TBool TBool a b =
    (if a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False \<and> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False
      then Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool)
      else Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool))"
| "vtor _ _ _ _ = None"

fun ival :: "Types \<Rightarrow> Valuetype"
where
  "ival (TSInt x) = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
| "ival (TUInt x) = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
| "ival TBool = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
| "ival TAddr = STR ''0x0000000000000000000000000000000000000000''"

end
