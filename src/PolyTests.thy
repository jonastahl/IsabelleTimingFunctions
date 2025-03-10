theory PolyTests
  imports Define_Time_Function
begin

text \<open>Register a function for Suc and translate a function using it\<close>
definition "T_Suc n = (0::nat)"
register_time_fun Suc T_Suc

definition "test n = Suc n"
time_fun test

definition "test2 n = Suc n"

text \<open>Translate a similar function but using another function for Suc\<close>
delete_time_fun Suc
definition "T_Suc2 n = (0::nat)"
register_time_fun Suc T_Suc2
time_fun test2

text \<open>Test translating a function inside a locale\<close>
definition "test3 n = test2 n"
locale test
begin
time_fun test3
end
text \<open>And use it outside...\<close>
definition "test4 n = test3 n"
time_fun test4

class arb =
  fixes arb :: "'a \<Rightarrow> 'a"

instantiation nat :: arb
begin
definition "arb_nat (_::nat) \<equiv> 0::nat"
instance..
end
instantiation bool :: arb
begin
definition "arb_bool (_::bool) \<equiv> True"
instance..
end

definition "T_True \<equiv> (8::nat)"
register_time_fun True T_True

time_fun "arb :: nat \<Rightarrow> nat"
time_fun "arb :: bool \<Rightarrow> bool"

definition "user (n::bool) = arb n"
time_fun user
definition "user2 (n::nat) = arb n"
time_fun user2

time_fun "plus::nat\<Rightarrow>nat\<Rightarrow>nat"

definition "add (a::nat) (b::nat) = a + b"
time_fun add

definition "T_Cons x xs = (0::nat)"
register_time_fun Cons T_Cons
time_fun map
find_theorems "_ + (0::nat) = _"
lemmas time_simps = add_0_right add_0_left
thm T_map.simps[simplified T_Cons_def time_simps]

text \<open>Test function register comparison\<close>

text \<open>This should work\<close>
experiment
begin
fun alpha :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "alpha a b = a"

definition "ti_alpha (a::int) (b::int) \<equiv> (0::nat)"
register_time_fun alpha ti_alpha

definition "beta (a::int) \<equiv> alpha a a"
time_fun beta
definition "gamma (a::'a) \<equiv> alpha a a"
text \<open>This should fail\<close>
time_fun gamma

fun delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta a b = a"
time_fun delta
definition "epsilon (a::nat) \<equiv> delta a a"
text \<open>This way should work\<close>
time_fun epsilon
end

end