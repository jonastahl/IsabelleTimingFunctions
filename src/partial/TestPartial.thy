theory TestPartial
  imports Define_Time_Function "HOL-Library.Monad_Syntax" 
begin

partial_function (tailrec) collatz :: "nat \<Rightarrow> bool" where
  "collatz n = (if n \<le> 1 then True
                else if n mod 2 = 0 then collatz (n div 2)
                else collatz (3 * n + 1))"

partial_function (option) T_collatz' :: "nat \<Rightarrow> nat option" where
  "T_collatz' n = (if n \<le> 1 then Some 0
                else if n mod 2 = 0 then do {k \<leftarrow> T_collatz' (n div 2); Some (Suc k)}
                else do {k \<leftarrow> T_collatz' (3 * n + 1); Some (Suc k)})"

time_fun_0 "(mod)"
time_partial_function collatz

definition "dummy a \<equiv> a"
partial_function (tailrec) partdummy :: "nat \<Rightarrow> nat" where
  "partdummy n = dummy n"
definition "user k = partdummy k"
time_fun dummy
time_partial_function partdummy
time_fun user


lemma setIt: "P i \<Longrightarrow> \<forall>n \<in> {Suc i..j}. P n \<Longrightarrow> \<forall>n \<in> {i..j}. P n"
  by (metis atLeastAtMost_iff le_antisym not_less_eq_eq)
lemma "\<forall>n \<in> {2..10}. T_collatz n = T_collatz' n"
  apply (rule setIt, simp add: T_collatz.simps T_collatz'.simps, simp)+
  by (simp add: T_collatz.simps T_collatz'.simps)

partial_function (tailrec) app_tail::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app_tail ys xs = (case ys of [] \<Rightarrow> xs
                        | (y#ys) \<Rightarrow> app_tail (ys) (y#xs))"

time_partial_function app_tail

partial_function (option) T_app_tail' ::"'a list \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "T_app_tail' ys xs = (case ys of [] \<Rightarrow> Some 0
                          | (y#ys) \<Rightarrow> do {k \<leftarrow> T_app_tail' (ys) (y#xs); Some (k + 1)})"

lemma "T_app_tail xs ys = T_app_tail' xs ys"
  

term Option.bind

lemma "T_app_tail [1,2::nat] [] = Some 3"
  apply (subst T_app_tail.simps)
  apply (subst T_app_tail.simps)
  apply (subst T_app_tail.simps)


end