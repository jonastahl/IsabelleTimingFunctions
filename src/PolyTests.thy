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

term "Suc 1 + 2"
class T_plus =
  fixes T_plus :: "'a \<Rightarrow> 'a \<Rightarrow> nat"
register_time_fun plus T_plus

instantiation nat :: T_plus
begin
definition "T_plus_nat (a::nat) (b::nat) \<equiv> 0::nat"
instance..
end

definition "add (a::nat) (b::nat) = a + b"
time_fun add

end