
signature TIME_MAPPING =
sig

val register_time_function_global : theory -> term -> term -> theory
val register_time_function : local_theory -> term -> term -> local_theory
val get_time_function : theory -> term -> term option

end

structure Time_Mapping : TIME_MAPPING =
struct

structure TimeMapping = Generic_Data(
  type T = term Net.net
  val empty = Net.empty
  val merge = Net.merge Term.eq_Const_name
)

fun get_time_function theory t =
  case Net.match_term (TimeMapping.get (Context.Theory theory)) t of
    [] => NONE
  | [T_t] => SOME T_t
  | _ => error "Found more than on registered time function"

fun register_time_function_global theory t T_t =
  case get_time_function theory t
    of SOME _ => error "Time function already registered for this term"
     | NONE => TimeMapping.map (Net.insert_term (K true) (t, T_t)) (Context.Theory theory)
                |> Context.theory_of

fun register_time_function lthy t T_t =
  Local_Theory.background_theory (fn theory => register_time_function_global theory t T_t) lthy

fun register (func, T_func) theory =
let
  val t = Syntax.read_term_global theory func
  val T_t = Syntax.read_term_global theory T_func
  val _ = case (t,T_t)
    of (Const _, Const (_,T_T)) =>
        let val t = Term.body_type T_T in
          if t = @{typ nat} orelse t = @{typ "nat option"} then ()
          else error "Timing function needs to end on nat or nat option type"
        end
      | _ => error "Terms need to be single constants"
in
  register_time_function_global theory t T_t
end

fun delete func theory =
let
  val t = Syntax.read_term_global theory func
in
  TimeMapping.map (Net.delete_term (K true) (t, get_time_function theory t |> the)) (Context.Theory theory)
    |> Context.theory_of
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>register_time_fun\<close> "Register a timing function for a function"
    (Parse.prop -- Parse.prop >> (Toplevel.theory o register));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>delete_time_fun\<close> "Delete timing function of a function"
    (Parse.prop >> (Toplevel.theory o delete));

end