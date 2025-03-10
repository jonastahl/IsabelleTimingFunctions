
signature TIME_MAPPING =
sig

val register_time_function : local_theory -> term -> term -> local_theory
val get_time_function : local_theory -> term -> term option

end

structure Time_Mapping : TIME_MAPPING =
struct

structure TimeMapping = Theory_Data(
  type T = term Net.net
  val empty = Net.empty
  val merge = Net.merge Term.eq_Const_name
)

fun body_types_match lthy t1 t2 =
let
  fun timify t = binder_types (fastype_of (singleton (Variable.polymorphic lthy) t)) ---> HOLogic.natT
in
  try Type.could_unify (timify t1, timify t2)
    |> the_default false
end

fun get_time_function lthy t =
let
in
  case Net.match_term (TimeMapping.get (Local_Theory.exit_global lthy)) t
        |> filter (fn t' => body_types_match lthy t' t)
      of
    [] => NONE
  | [T_t] => SOME T_t
  | _ => error "Found more than on registered time function"
end

fun register_time_function lthy t T_t =
let
  val t_gen = singleton (Variable.polymorphic lthy) t
  val T_t_gen = singleton (Variable.polymorphic lthy) T_t
in
  case get_time_function lthy t
    of SOME _ => error "Time function already registered for this term"
     | NONE =>
        Local_Theory.background_theory
          (TimeMapping.map (Net.insert_term (apply2 fastype_of #> Type.could_unify) (t_gen, T_t_gen)))
          lthy
end

fun register (func, T_func) lthy =
let
  val t = Syntax.read_term lthy func
  val T_t = Syntax.read_term lthy T_func
  val _ = case (t,T_t)
    of (Const _, Const (_,T_T)) =>
        let val t = Term.body_type T_T in
          if t = @{typ nat} orelse t = @{typ "nat option"} then ()
          else error "Timing function needs to end on nat or nat option type"
        end
      | _ => error "Terms need to be single constants"
in
  register_time_function lthy t T_t
end

fun delete func lthy =
let
  val t = Syntax.read_term lthy func
in
  Local_Theory.background_theory
    (TimeMapping.map (Net.delete_term (K true) (t, get_time_function lthy t |> the))) lthy
end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>register_time_fun\<close> "Register a timing function for a function"
    (Parse.prop -- Parse.prop >> register);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>delete_time_fun\<close> "Delete timing function of a function"
    (Parse.prop >> delete);

end